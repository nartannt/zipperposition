
module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm 
module Subst = Subst
module Sc = Scoped

module TermSet = T.Set
module TypeSet = Ty.Set

module ArgMap = Map.Make(ID)
module ClauseArgMap = Map.Make(Int)

(* Note: for ease of notation, variables, functions ... use "polymorphic" in the sense of "non-monomorphic" *)

(* TODO make a neat little module with a decent interface *)
(* TODO massive refactor once we get this working*)
(* TODO make parameters proportional*)
(* TODO remove clauses with literals with uninstantiable type variables *)
(* TODO rewrite typed_sym to get rid of all the junk*)
(* TODO rewrite final monomorphic filtering more elegantly*)
(* TODO write nice documentation and comments *)
(* TODO CI tests *)
(* TODO unit tests *)
(* TODO integration tests *)
(* TODO squash all commits and make the necessary rebase so that this can be added to the main zipperposition branch*)
(* TODO check if a newly generated type already exists and don't add it to new in that case *)
(* TODO clean the mangling implementation *)
(* TODO rewrite implementation to handle clause instantiation *)

(* Iter.union needs to be provided an equality function when dealing with lists of types *)
let ty_arg_eq ty_arg1 ty_arg2 = List.for_all Fun.id (List.map2 Ty.equal ty_arg1 ty_arg2)

(* the given type does not contain any tType *)
let is_not_meta ty =
    not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

(* the given type is not meta and requires no type arguments*)
let is_instantiated ty =
    (List.for_all is_not_meta (Ty.expected_args ty)) && Ty.expected_ty_vars ty = 0

(* returns the substitution that allows matching a monomorphic type against a type *)
let match_type ty ~mono_type =
    (* TODO understand this i have no idea what the scopes do*)
    Unif.Ty.matching_same_scope ~pattern:ty mono_type ~scope:0

(* returns an (ID, type list) iter that represent the function symbols and their type arguments that 
 * can be extracted from the term *)
let typed_sym term = 
    (*get all applications*)
    let all_apps = Iter.filter T.is_app (T.Seq.subterms term) in
    (*get all the function symbols and types at the application level*)
    let get_typed_sym app_term =
        let hd_term = T.head_term_mono app_term in
        let _, f = T.open_fun hd_term in
        let ty = T.ty hd_term in
        (* TODO this is somewhat hackish, is there a more natural way of doing this? *)
        let unsafe_term_to_type (term: T.t) = Ty.of_term_unsafe (term:>InnerTerm.t) in
        match T.head f with
            | Some(id) when is_instantiated ty -> Some(id, List.map unsafe_term_to_type (snd (T.as_app f)))
            | _ -> None
    in
    Iter.filter_map get_typed_sym all_apps

(* applies a substitution to a type*)
let apply_ty_subst subst ty =
    Subst.Ty.apply Subst.Renaming.none subst (ty, 0)

(* applies a substitution to a literal *)
let apply_subst_lit lit subst =
    Literal.apply_subst_no_simp Subst.Renaming.none subst (lit, 0)

(* merges two maps by union of their iters*)
let merge_map_arg_iter (old_ty_args_1, new_ty_args_1) (old_ty_args_2, new_ty_args_2) =
    Iter.union ~eq:ty_arg_eq old_ty_args_1 old_ty_args_2, Iter.union ~eq:ty_arg_eq new_ty_args_1 new_ty_args_2


(* the union of two substitution iters*)
let iter_subst_union = Iter.union ~eq:Subst.equal ~hash:Subst.hash

(* takes a list of monomorphic types
 * takes a list of polymorphic types
 * returns a set (iter for now) of type substitutions that match the 
 * polymorphic types to the monomorphic types one by one 
 * expects the list to be of the same length *)
let type_arg_list_subst type_list_poly type_list_mono =
    let combine subst_iter mono_ty poly_ty =
        try 
            Iter.cons (match_type poly_ty ~mono_type:mono_ty) subst_iter
        with Unif.Fail ->
            subst_iter
    in
    List.fold_left2 combine Iter.empty type_list_mono type_list_poly


(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns a set (iter for now) of the type substitutions that can be derived from the given maps *)
let derive_type_arg_subst mono_map poly_map = 
    (*derives the substitutions from two sets (iters) of type arguments*)
    let type_arg_iter_subst mono_type_args_iter poly_type_args_iter =
        let poly_arg_map mono_type_args_iter poly_type_list =
            Iter.flat_map (type_arg_list_subst poly_type_list) mono_type_args_iter
        in
        Iter.flat_map (poly_arg_map mono_type_args_iter) poly_type_args_iter
    in
    
    let combine fun_sym (old_poly_args, new_poly_args) acc =
        let new_poly_subst, old_poly_subst = acc in
        let old_mono_args, new_mono_args = ArgMap.find fun_sym mono_map in
        (* substitutions derived from the new poly type args *)
        let derived_new_poly_subst =
            type_arg_iter_subst (Iter.union ~eq:ty_arg_eq old_mono_args new_mono_args) new_poly_args
        in
        (* substitutions dervied from the old poly type args and the new mono type args*)
        let derived_old_poly_subst =
            type_arg_iter_subst new_mono_args old_poly_args
        in
        let new_poly_subst_res = iter_subst_union new_poly_subst derived_new_poly_subst in
        let old_poly_subst_res = iter_subst_union old_poly_subst derived_old_poly_subst in
        new_poly_subst_res, old_poly_subst_res
    in

    ArgMap.fold combine poly_map (Iter.empty, Iter.empty)

(* truncates an iter after len elements *)
let iter_truncate len iter =
    Iter.filter_mapi (fun count elem -> if count < len then Some(elem) else None) iter

(* given a map from function symbols to polymorphic type arguments
 * given a set (iter for now) of type substitutions
 * generates two maps of the derived monomorphic and polymorphic type arguments *)
(* possible optimisation, do this step at the same time as deriving the substitutions *)
(* the absolute bound gives a hard cap on the number of new type arguments that are added for each function symbol
 * for each clause, the relative bound caps the number of new type arguments based on the number of existing ones note that
 * the relative bound will allow at least one new type argument even if no type arguments currently exist*)
(* TODO maybe add a parameter for a floor on the relative bounds*)
(* TODO the relative bound for the new mono type args are based on the poly map, change this*)
(* TODO paramatrise bounds*)
let apply_subst_map poly_map new_poly_subst old_poly_subst =
    (* applies the substitution to the type arguments, returns some iff the result is different from
     * the original type arguments *)
    let apply_ty_subst_arg_opt subst ty_args =
        let new_ty_args = List.map (apply_ty_subst subst) ty_args in
        let is_diff = List.exists2 (fun ty_1 ty_2 -> not (Ty.equal ty_1 ty_2)) ty_args new_ty_args in
        if is_diff then Some new_ty_args
        else None
    in

    let apply_subst_iter (old_poly_args_iter, new_poly_args_iter) =
        (* keep only the type args that are different from the original *)
        let applied_poly_args_1 = Iter.flat_map (fun subst -> Iter.filter_map (apply_ty_subst_arg_opt subst) new_poly_args_iter) new_poly_subst in
        let applied_poly_args_2 = Iter.flat_map (fun subst -> Iter.filter_map (apply_ty_subst_arg_opt subst) old_poly_args_iter) old_poly_subst in
        Iter.union ~eq:ty_arg_eq applied_poly_args_1 applied_poly_args_2
    in

    (* map of both monomorphic and polymorphic type arguments *)
    let mixed_map = ArgMap.map apply_subst_iter poly_map in

    (* splits the mixed map into its monomorphic and polymorphic components *)
    let split_iter type_args_iter =
        (* might be able to find a more efficient way of doing this*)
        let mono_type_args = Iter.filter (List.for_all Ty.is_ground) type_args_iter in
        let poly_type_args = Iter.filter (List.for_all (fun ty -> not (Ty.is_ground ty))) type_args_iter in
        mono_type_args, poly_type_args
    in

    let combine_split fun_sym type_args_iter (acc_mono_map, acc_poly_map) =
        let mono_iter, poly_iter = split_iter type_args_iter in
        let new_mono_map = ArgMap.add fun_sym mono_iter acc_mono_map in
        let new_poly_map = ArgMap.add fun_sym poly_iter acc_poly_map in
        new_mono_map, new_poly_map
    in
    let new_mono_map, new_poly_map = ArgMap.fold combine_split mixed_map (ArgMap.empty, ArgMap.empty) in
    new_mono_map, new_poly_map
    
(* given a subst iter corresponding to a clause, given a bound that limits the number of substitutions
 * per type variable, returns an iter of the selected substitutions *)
(* the variables are ordered with respect to (HVar.compare InnerTerm.compare) basically an arbitrary order*)
let select_subst subst_iter ty_var_subst_max =
    let ty_vars = Iter.flat_map (fun subst -> Subst.domain subst) subst_iter in
    let sorted_ty_vars = Iter.sort_uniq ~cmp:(fun var var' -> HVar.compare InnerTerm.compare (Scoped.get var) (Scoped.get var') ) ty_vars in
    let select_subst_for_var ty_var =
        let subst_iter_for_var = Iter.filter (fun subst -> Subst.mem subst ty_var) subst_iter in
        (* TODO Subst.compare isn't the best substitution comparison functionp
         * we would like to favour older substitutions as well as subtitutions which instantiate
         * multiple type variables*)
        let subst_iter_for_var_sorted = Iter.sort_uniq ~cmp:Subst.compare subst_iter_for_var in
        let selected_subst = iter_truncate ty_var_subst_max subst_iter_for_var_sorted in
        selected_subst 
    in
    let select_var_fold acc ty_var = iter_subst_union acc (select_subst_for_var ty_var) in
    Iter.fold select_var_fold Iter.empty sorted_ty_vars

(* generates an iter of monomorphising substitutions obtained from the subst_iter 
 * at most new_clauses_max new substitutions will be returned (maybe +1) *)
(* assumes that the subst_iter is somehow sorted *)
let generate_monomorphising_subst subst_iter lit_arr new_clauses_max = 
    let clause_ty_vars lit_arr =
        Iter.flat_map (fun lit -> (Literal.Seq.vars lit :> InnerTerm.t HVar.t Iter.t)) (Iter.of_array lit_arr)
    in
    let can_monomorphise =
        let subst_ty_vars = Iter.flat_map (fun subst -> Iter.map Scoped.get (Subst.domain subst)) subst_iter in
        Iter.subset ~eq:(HVar.equal InnerTerm.equal) subst_ty_vars (clause_ty_vars lit_arr)
    in
    let instantating_subst ty_var subst_iter =
        Iter.filter (fun subst -> Subst.mem subst ty_var) subst_iter
    in
    if not can_monomorphise then Iter.empty
    else
    let rec monomorphising_subst_iter subst_iter vars_to_instantiate subst_acc curr_subst_count = 
        match Iter.head vars_to_instantiate with
            | None -> Iter.singleton subst_acc, curr_subst_count - 1
            | Some ty_var ->
                    let next_substitutions = instantating_subst ty_var subst_iter in
                    let next_vars curr_vars subst = Iter.diff ~eq:(fun var var' -> HVar.equal InnerTerm.equal (Scoped.get var) (Scoped.get var')) curr_vars (Subst.domain subst) in
                    let subst_fold (acc, acc_count) subst =
                        let mono_subst_res, res_count =
                            monomorphising_subst_iter subst_iter (next_vars vars_to_instantiate subst) (Subst.merge subst_acc subst) acc_count in
                        if res_count <= 0 then acc, 0
                        else 
                            iter_subst_union acc mono_subst_res, res_count
                    in
                    Iter.fold subst_fold (Iter.empty, curr_subst_count) next_substitutions
    in
    let mono_subst_iter, _ = monomorphising_subst_iter subst_iter (Iter.map (fun var -> Scoped.make var 0) (clause_ty_vars lit_arr)) Subst.empty new_clauses_max in
    mono_subst_iter


(* takes a map from functions symbols to sets (iter for now) of monomorphic type arguments
 * takes an array of literals
 * takes a map from clause_ids to a map of function symbols to sets (iter for now) of monomorphic type arguments
 * takes a clause id
 * returns a map of new monomorphic type arguments
 * returns a map of new polymorphic type arguments
 * returns an array of literals that have been partially monomorphised
 * that have been partially monomorphised *)
let mono_step_clause mono_type_args_map poly_type_args_map literals =

    (* the bounds that we want to establish *)

    (* how many new mono type args we allow to be derived from each clause, relative and hard cap*)
    let new_mono_per_clause_rel = 1.2 in
    let new_mono_per_clause_abs = 50 in
    (* the relative floor is for the cases where the relative proportion is too low to yield any new
     * clauses (ie: we have 10 type arguments but a limit of 0.05, then mono_rel_floor type arguments are
     * allowed instead of 0) still capped by the abs cap*)
    let mono_rel_floor = 1 in
    (* same as for the monomorphic bounds *)
    let new_poly_per_clause_rel = 1.2 in
    let new_poly_per_clause_abs = 50 in
    let poly_rel_floor = 1 in


    (* TODO same function to refactor*)
    let max_nb_mono iter_len =
        let rel_int = int_of_float (float_of_int iter_len *. new_mono_per_clause_rel) in
        min new_mono_per_clause_abs (max mono_rel_floor rel_int)
    in
    let max_nb_poly iter_len =
        let rel_int = int_of_float (float_of_int iter_len *. new_poly_per_clause_rel) in
        min new_poly_per_clause_abs (max poly_rel_floor rel_int)
    in

    (*generate all substitutions from mono and poly type arguments*)
    let new_poly_subst_all, old_poly_subst_all = derive_type_arg_subst mono_type_args_map poly_type_args_map in

    let total_subst_nb = (Iter.length new_poly_subst_all) + (Iter.length old_poly_subst_all) in
    
    (* TODO parametrise bound find some reasonable way to order the subst iter such that truncating makes sense*)
    let subst_rel_floor = 1 in
    let subst_abs_max = 50 in
    let subst_rel_max = 1.1 in
    let truncate_nb = min subst_abs_max (max subst_rel_floor (int_of_float (float_of_int total_subst_nb *. subst_rel_max))) in
    let new_poly_subst, old_poly_subst = iter_truncate truncate_nb new_poly_subst_all, iter_truncate truncate_nb old_poly_subst_all in
    let subst_iter = iter_subst_union new_poly_subst old_poly_subst in

    (*apply the substitutions to the poly type arguments*)
    (*split them into the new_mono and new_poly type arguments*)
    let new_mono_map_all, new_poly_map_all = apply_subst_map poly_type_args_map new_poly_subst old_poly_subst in

    (* truncationg the new type arguments according to the bounds *)
    (* TODO, same function, to refactor and seperate *)
    let new_mono_map = 
        ArgMap.mapi (fun fun_sym iter -> iter_truncate (max_nb_mono (Iter.length (fst (ArgMap.find fun_sym mono_type_args_map)))) iter) new_mono_map_all
    in
    let new_poly_map = 
        ArgMap.mapi (fun fun_sym iter -> iter_truncate (max_nb_poly (Iter.length (fst (ArgMap.find fun_sym poly_type_args_map)))) iter) new_poly_map_all
    in

    (* TODO parametrise and proportionalise bounds*)
    let selected_subst = select_subst subst_iter 50 in
    let monomorphising_subst = generate_monomorphising_subst selected_subst literals 200 in
    let new_lits_iter = Iter.map (fun subst -> Array.map (fun lit -> apply_subst_lit lit subst) literals) monomorphising_subst in

    (*
    (*apply the substitutions to the literals*)
    let new_lits_iter =
        Array.fold_left (fun acc lit -> Iter.union ~eq:Literal.equal acc (Iter.map (apply_subst_lit lit) subst_iter)) Iter.empty literals
    in

    (* this renames variables to make sure that we don't have naming conflicts between the bound variables of the terms*)
    let new_lits_vars_iter = Iter.fold (fun acc lit -> Iter.union ~eq:(HVar.equal Ty.equal) acc (Literal.Seq.vars lit)) Iter.empty new_lits_iter in
    let new_lits_vars_list = Iter.to_list (Iter.filter (fun var -> not (Ty.is_tType (HVar.ty var))) new_lits_vars_iter) in
    let fresh_lits_vars = List.map (fun var -> Term.var (HVar.fresh ~ty:(HVar.ty var) ())) new_lits_vars_list in

    let rename_vars_lit lit =
        List.fold_left2 (fun acc_lit old_var fresh_var -> Literal.replace acc_lit ~old:(Term.var old_var) ~by:fresh_var) lit new_lits_vars_list fresh_lits_vars
    in
    let new_lits_renamed = Iter.map rename_vars_lit new_lits_iter in

    let new_lits_arr = Iter.to_array new_lits_renamed in

    let lit_is_monomorphic = function
        | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
        | _ -> true
    in
    let new_arr_mono = Array.for_all lit_is_monomorphic new_lits_arr in*)


    (*returns the new_mono_map, new_poly_map and new_literals*)
    new_mono_map, new_poly_map, new_lits_iter



let print_all_type_args fun_sym iter =
    Printf.printf "for this function symbol: %s -- we have the following type arguments (old) :\n" (ID.name fun_sym);
    Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (fst iter);
    Printf.printf "(new) :\n";
    Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (snd iter)

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map from function symbols to sets (iter for now) of polymorphic type arguments
 * takes a list of clauses under the form of a (clause_id * literal array) (clause_ids are ints)
 * returns an updated monomorphic map, polymorphic map and list of updated clauses *)
let mono_step clause_list mono_map poly_clause_map =

    let new_clauses = ref 0 in
    
    (* given an accumulator that contains a list of clauses and two type argument maps (one mono and one poly)
     * returns an accumulator updated with regards to the given literals*)
    let process_clause acc (clause_id, literals) =
        let (acc_clauses, acc_mono_map, acc_poly_clause_map) = acc in
        (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
        let poly_map = ClauseArgMap.find clause_id poly_clause_map in

        (* newly generated literals and type arguments*)
        let (new_mono_map, new_poly_map, new_mono_clauses) = mono_step_clause mono_map poly_map literals in

        let merge_iter _ iter_1 iter_2 = Some (Iter.union ~eq:ty_arg_eq iter_1 iter_2) in
        let res_mono_map = ArgMap.union merge_iter new_mono_map acc_mono_map in
        (* this entails that if two clauses have the same id, then the type arguments derived from the earlier
         * ones will be overwritten*)
        let res_poly_clause_map = ClauseArgMap.add clause_id new_poly_map acc_poly_clause_map in

        new_clauses := !new_clauses + (Iter.length new_mono_clauses);

        let clause_list = Iter.to_list (Iter.map (fun lit_arr -> clause_id, lit_arr) new_mono_clauses) in
        (clause_list @ acc_clauses, res_mono_map, res_poly_clause_map)
    in
    let new_mono_clauses, new_mono_map, new_poly_clause_map = 
        List.fold_left process_clause ([], ArgMap.empty, ClauseArgMap.empty) clause_list
    in
    let age_map original_map extra_map =
        let new_args_iter fun_sym = match ArgMap.find_opt fun_sym extra_map with
            | Some iter -> iter
            | None -> Iter.empty
        in
        let iter_age_fold fun_sym (original_old_iter, original_new_iter) acc_map =
            let new_old_iter = Iter.union ~eq:ty_arg_eq original_old_iter original_new_iter in
            ArgMap.add fun_sym (new_old_iter, new_args_iter fun_sym) acc_map
        in
        ArgMap.fold iter_age_fold original_map ArgMap.empty
    in
    let res_mono_map = age_map mono_map new_mono_map in
    let clause_map_age clause_id original_poly_map =
        match ClauseArgMap.find_opt clause_id new_poly_clause_map with
            | None -> age_map original_poly_map ArgMap.empty
            | Some extra_poly_map -> age_map original_poly_map extra_poly_map
    in
    let res_poly_clause_map = ClauseArgMap.mapi clause_map_age poly_clause_map in
    Printf.printf "\nwe have an extra %i new lits generated\n" !new_clauses;
    new_mono_clauses, res_mono_map, res_poly_clause_map

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * same for polymorphic type arguments
 * takes a term
 * returns the maps updated with the additional function symbol -> type arguments bindings derived from the term
 * note that all function symbols are added to the maps, even when no corresponding type arguments are found
 * this is to avoid trouble when ArgMap.find is used later *)
(* we assume this function is used only for the initialisation of the maps and that they contain no new type
 * arguments *)
let add_typed_sym mono_map poly_map term =
    let typed_symbols = typed_sym term in
    let type_args_are_mono = List.for_all Ty.is_ground in
    let map_update_fun ty_args add_args = function
        | None when add_args -> 
                Some (Iter.empty, Iter.singleton ty_args)
        | Some (_, curr_iter) when add_args ->
                (*Printf.printf "boop\n";*)
                Some (Iter.empty, Iter.cons ty_args curr_iter)
        | None -> Some (Iter.empty, Iter.empty)
        | Some (_, curr_iter)-> Some (Iter.empty, curr_iter)
    in
    (*using tuples because this function will be used in a fold*)
    let update_maps (curr_mono_map, curr_poly_map) (ty_sym, ty_args) =
        let ty_args_mono = type_args_are_mono ty_args in
        let new_mono_map = ArgMap.update ty_sym (map_update_fun ty_args ty_args_mono) curr_mono_map in
        let new_poly_map = ArgMap.update ty_sym (map_update_fun ty_args (not ty_args_mono)) curr_poly_map in
        new_mono_map, new_poly_map
    in
    let res_mono_map, res_poly_map = Iter.fold update_maps (mono_map, poly_map) typed_symbols in

    (* makes sure all function symbols have been added to the mono_map, to be later removed when find_opt
     * replaces find *)
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_mono_map != None) typed_symbols));
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_poly_map != None) typed_symbols));
    (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym res_mono_map != None) res_poly_map));
    res_mono_map, res_poly_map

(* given an array of literals, returns an iter of all the terms in literals *)
let terms_iter literals = 
    Literals.Seq.terms literals

(* will initialise the maps with the function symbol -> type arguments bindings derived from the clauses *)
let map_initialisation_step (mono_map, clause_poly_map) (clause_id, literals) =
    let clause_terms_iter = terms_iter literals in

    let update_maps (curr_mono_map, curr_poly_map) term =
        add_typed_sym curr_mono_map curr_poly_map term
    in
    let new_mono_map, new_poly_map = Iter.fold update_maps (mono_map, ArgMap.empty) clause_terms_iter in
    let new_clause_poly_map = match ClauseArgMap.find_opt clause_id clause_poly_map with
        | None -> ClauseArgMap.add clause_id new_poly_map clause_poly_map
        (*should not happen if each clause has a unique id*)
        | Some other_poly_map ->
                ClauseArgMap.add clause_id
                    (ArgMap.union
                        (fun _ pair_1 pair_2 -> Some (merge_map_arg_iter pair_1 pair_2))
                        new_poly_map other_poly_map)
                    clause_poly_map
    in
    let all_ty_syms = Iter.flat_map typed_sym clause_terms_iter in

    (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym new_mono_map != None) new_poly_map));
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym new_mono_map != None) all_ty_syms));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key new_mono_map != None) poly_map ) new_clause_poly_map));

    new_mono_map, new_clause_poly_map

(* takes a list of (clause_id, literal array) pairs
 * takes an integer to limit the numbers of iterations
 * returns an updated list of clauses *)
let monomorphise_problem clause_list loop_count =
    Printf.printf "\nBeginning monomorphisation\n";
    (* create initial maps *)
    let init_mono_map, init_clause_poly_map =
        List.fold_left map_initialisation_step (ArgMap.empty, ClauseArgMap.empty) clause_list in

    (* remove duplicates *)
    let init_mono_map = ArgMap.map (fun (old_iter, new_iter) -> Iter.sort_uniq old_iter, Iter.sort_uniq new_iter) init_mono_map in

    (* another check due to a later Map.find*)
    (assert (List.for_all (fun (clause_id, _) -> ClauseArgMap.find_opt clause_id init_clause_poly_map != None) clause_list));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key init_mono_map != None) poly_map ) init_clause_poly_map));

    (* monomorphisation loop *)
    let rec monomorphisation_loop curr_count mono_map poly_clause_map clause_list =
        let mono_map = ArgMap.map (fun (new_iter, old_iter) -> Iter.sort_uniq new_iter, Iter.sort_uniq old_iter) mono_map in
        Printf.printf "we have %i total monomorphic type args\n" (ArgMap.fold (fun _ (old_iter, new_iter) acc -> (Iter.length old_iter) + (Iter.length new_iter) + acc) mono_map 0);
        if curr_count <= 0 then mono_map, poly_clause_map, clause_list
        else
            (* given that the maps are updated independently of the clause list, we could not pass the udpated
             clauses as parameter, however, it is convienient to do so*)
            let new_clauses, new_mono_map, new_poly_clause_map = mono_step clause_list mono_map poly_clause_map in
            monomorphisation_loop (curr_count-1) new_mono_map new_poly_clause_map new_clauses 
    in

    (* resulting clause_list with updated literals *)
    let _, _, clause_list_res =
        monomorphisation_loop loop_count init_mono_map init_clause_poly_map clause_list in

    let lit_is_monomorphic = function
        | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
        | _ -> true
    in

    let mono_clause_list_res =
        let mono_clauses = List.filter (fun (clause_id, lit_arr) -> Array.for_all lit_is_monomorphic lit_arr) clause_list_res in
        let mono_clauses_no_empty = List.filter (fun (_, lit_arr) -> Array.to_list lit_arr != []) mono_clauses in
        Printf.printf "We have lost %i clauses\n" (List.length clause_list_res - List.length mono_clauses);
        mono_clauses_no_empty
    in


    mono_clause_list_res

(* We're not done yet, because even though we have monomorphised the clauses, they still make use of polymorphic type constructors which can't be handled by e 
 * therefore, we must replace all instantiated polymorphic type constructors by a monomorphic type, this should not be hard, ex: replace all list int by list_int
 * all fun int bool by fun_int_bool ect ...*)

let rec convert_type ty = 
    let open Ty in
    let args = expected_args ty in
    let ret = returns ty in
    if args != [] then
        (List.map convert_type args) ==> (convert_type ret)
    else match view ty with
        | Builtin _ -> ty 
        (* TODO this is a temporary fix, need to find better solution, ties in to the mangle problem*)
        | _ -> Ty.const (ID.make (Ty.mangle ty))


(* converts the given iter of literals to simple terms with mangled types*)
(* my attempted way to do this is to use the existing conversion functions except
 * that whenever a type would be converted, we transform it into a mangled constant*)
let convert_lits lit_iter =
    Iter.empty
