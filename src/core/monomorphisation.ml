
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

(* TODO make a neat little module with a decent interface *)
(* TODO massive refactor once we get this working*)
(* TODO find more efficient data structures for this process, iter are easy to manipulate but sets would
 * probably be more appropriate *)
(* TODO make parameters proportional*)
(* TODO remove literals with uninstantiable type variables *)
(* TODO rewrite typed_sym to get rid of all the junk*)
(* TODO rewrite final monomorphic filtering more elegantly*)
(* TODO use sets of lits to make sure we don't have duplicates*)
(* TODO remove useless prints *)
(* TODO write nice documentation and comments *)
(* TODO CI tests *)
(* TODO preliminary tests *)
(* TODO squash all commits and make the necessary rebase so that this can be added to the main zipperposition branch*)

(* Iter.union needs to be provided an equality function when dealing with lists of types *)
let ty_arg_eq ty_arg1 ty_arg2 = List.for_all Fun.id (List.map2 Ty.equal ty_arg1 ty_arg2)

(* the given type does not contain any tType *)
let is_not_meta ty =
    not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

let is_instantiated ty =
    List.for_all is_not_meta (Ty.expected_args ty) && Ty.expected_ty_vars ty = 0

(* returns the substitution that allows matching a monomorphic type against a type *)
let match_type ty mono_type =
    (*Printf.printf "\nwe are matching %s against %s\n" (Ty.to_string mono_type) (Ty.to_string ty);*)
    let subst = Unif.Ty.matching_same_scope ~scope:0 ~pattern:mono_type ty in
    subst

let typed_sym term = 
    InnerTerm.show_type_arguments := true;
    (*get all applications*)
    let all_apps = Iter.filter T.is_app (T.Seq.subterms term) in
    (*get all the function symbols and types at the application level*)
    let get_typed_sym app_term =
        let hd_term = T.head_term_mono app_term in
        (*let ty_args, f = T.as_fun app_term in*)
        let _, f = T.open_fun hd_term in
        let ty = T.ty hd_term in
        (* TODO add a function that splits an app into its type arguments and its function symbol
         * in Term.ml because this current fix is extremely hackish*)
        let unsafe_term_to_type (term: T.t) = Ty.of_term_unsafe (term:>InnerTerm.t) in
        match T.head f with
            | Some(id) when is_instantiated ty -> Some(List.map unsafe_term_to_type (snd (T.as_app f)), id, ty)
            | _ -> None
    in
    let res = Iter.filter_map get_typed_sym all_apps in

    (*(Iter.iter (fun (ty_args, s, _) -> (Printf.printf "\n symbol %s, ty_args: %s" (ID.name s) (String.concat "; " (List.map Ty.to_string ty_args)) )) res);*)
    Iter.map (fun (ty_args, s, _) -> s, ty_args) res

let apply_ty_subst subst ty =
    Subst.Ty.apply Subst.Renaming.none subst (ty, 0)

let apply_subst_lit lit subst =
    Literal.apply_subst Subst.Renaming.none subst (lit, 0)

let merge_map_arg_iter (old_ty_args_1, new_ty_args_1) (old_ty_args_2, new_ty_args_2) =
    Iter.union ~eq:ty_arg_eq old_ty_args_1 old_ty_args_2, Iter.union ~eq:ty_arg_eq new_ty_args_1 new_ty_args_2


let iter_subst_union = Iter.union ~eq:Subst.equal ~hash:Subst.hash

(* takes a list of monomorphic types
 * takes a list of polymorphic types
 * returns a set (iter for now) of type substitutions that match the 
 * polymorphic types to the monomorphic types one by one 
 * expects the list to be of the same length *)
let type_arg_list_subst type_list_mono type_list_poly =
    let combine subst_iter mono_ty poly_ty =
        try 
            Iter.cons (match_type poly_ty mono_ty) subst_iter
        with Unif.Fail ->
            Printf.printf "mono type: %s and poly type: %s\n" (Ty.to_string mono_ty) (Ty.to_string poly_ty);
            subst_iter
    in
    let res = List.fold_left2 combine Iter.empty type_list_mono type_list_poly in
    (*Printf.printf "list.length blabla %i\n" (Iter.length res);*)
    res


(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns a set (iter for now) of the type substitutions that can be derived from the given maps *)
let derive_type_arg_subst mono_map poly_map = 
    (*derives the substitutions from two sets (iters) of type arguments*)
    let type_arg_iter_subst mono_type_args_iter poly_type_args_iter =
        (*Printf.printf "who is guilty: %i or %i\n" (Iter.length mono_type_args_iter) (Iter.length poly_type_args_iter);*)
        let poly_arg_map mono_type_args_iter poly_type_list =
            Iter.flat_map (type_arg_list_subst poly_type_list) mono_type_args_iter
        in
        let res = Iter.flat_map (poly_arg_map mono_type_args_iter) poly_type_args_iter in
        (*Printf.printf "here? %i\n" (Iter.length res);*)
        res
    in
    
    let combine fun_sym (old_poly_args, new_poly_args) acc =
        let new_poly_subst, old_poly_subst = acc in
        let old_mono_args, new_mono_args = ArgMap.find fun_sym mono_map in
        (* substitutions derived from the new poly type args *)
        let derived_new_poly_subst =
            type_arg_iter_subst (Iter.union ~eq:ty_arg_eq old_mono_args new_mono_args) new_poly_args
        in
        (*Printf.printf "new_poly_args %i\n" (Iter.length new_poly_args);
        Printf.printf "old_poly_args %i\n" (Iter.length old_poly_args);*)
        (* substitutions dervied from the old poly type args and the new mono type args*)
        let derived_old_poly_subst =
            type_arg_iter_subst new_mono_args old_poly_args
        in
        let new_poly_subst_res = iter_subst_union new_poly_subst derived_new_poly_subst in
        let old_poly_subst_res = iter_subst_union old_poly_subst derived_old_poly_subst in
        new_poly_subst_res, old_poly_subst_res
    in

    ArgMap.fold combine poly_map (Iter.empty, Iter.empty)

let iter_truncate len iter =
    Iter.filter_mapi (fun count elem -> if count < len then Some(elem) else None) iter

(* given a map from function symbols to polymorphic type arguments
 * given a set (iter for now) of type substitutions
 * generates two maps of the derived monomorphic and polymorphic type arguments *)
(* possible optimisation, do this step at the same time as deriving the substitutions *)
let apply_subst_map poly_map new_poly_subst old_poly_subst =
    (* applies the substitution to the type arguments, returns some iff the result is different from
     * the original type arguments *)
    let apply_ty_subst_arg_opt subst ty_args =
        let new_ty_args = List.map (apply_ty_subst subst) ty_args in
        let is_diff = List.exists2 (fun ty_1 ty_2 -> not (Ty.equal ty_1 ty_2)) ty_args new_ty_args in
        if true || is_diff then Some new_ty_args
        else None
    in

    let apply_subst_iter (old_poly_args_iter, new_poly_args_iter) =
        (* keep only the type args that are different from the original *)
        let applied_poly_args_1 = Iter.flat_map (fun subst -> Iter.filter_map (apply_ty_subst_arg_opt subst) new_poly_args_iter) new_poly_subst in
        let applied_poly_args_2 = Iter.flat_map (fun subst -> Iter.filter_map (apply_ty_subst_arg_opt subst) old_poly_args_iter) old_poly_subst in
        Iter.union ~eq:ty_arg_eq applied_poly_args_1 applied_poly_args_2
    in


    let mixed_map = ArgMap.map apply_subst_iter poly_map in

    let split_iter type_args_iter =
        (* might be able to find a more efficient way of doing this*)
        let mono_type_args = Iter.filter (List.for_all is_instantiated) type_args_iter in
        let poly_type_args = Iter.filter (List.for_all (fun ty -> not (is_instantiated ty))) type_args_iter in
        mono_type_args, poly_type_args
    in

    let combine_split fun_sym type_args_iter (acc_mono_map, acc_poly_map) =
        let mono_iter, poly_iter = split_iter type_args_iter in
        (* TODO parametrise and rationalise bounds*)
        let mono_iter_bound =  max (min 10 (int_of_float (float_of_int (Iter.length (fst (ArgMap.find fun_sym poly_map))) *. 0.5))) 10 in
        let poly_iter_bound =  max (min 10 (int_of_float (float_of_int (Iter.length (fst (ArgMap.find fun_sym poly_map))) *. 0.5))) 10 in
        let new_mono_map = ArgMap.add fun_sym (iter_truncate mono_iter_bound mono_iter) acc_mono_map in
        let new_poly_map = ArgMap.add fun_sym (iter_truncate poly_iter_bound poly_iter) acc_poly_map in
        new_mono_map, new_poly_map
    in
    let new_mono_map, new_poly_map = ArgMap.fold combine_split mixed_map (ArgMap.empty, ArgMap.empty) in
    new_mono_map, new_poly_map
    


(* takes a map from functions symbols to sets (iter for now) of monomorphic type arguments
 * takes an array of literals
 * takes a map from clause_ids to a map of function symbols to sets (iter for now) of monomorphic type arguments
 * takes a clause id
 * returns a map of new monomorphic type arguments
 * returns a map of new polymorphic type arguments
 * returns an array of literals that have been partially monomorphised
 * that have been partially monomorphised *)
let mono_step_clause mono_type_args_map poly_type_args_map literals =
    (*generate all substitutions from mono and poly type arguments*)
    (* the sort_uniq allows for a consistent arbitrary means of sorting the substitutions for subsequent truncation *)
    let new_poly_subst, old_poly_subst = derive_type_arg_subst mono_type_args_map poly_type_args_map in
    let subst_iter_all = Iter.sort_uniq (iter_subst_union new_poly_subst old_poly_subst) in
    (*Printf.printf "all substitiutions %i\n" (Iter.length subst_iter_all);*)

    (* TODO parametrise bound find some reasonable way to order the subst iter such that truncating makes sense*)
    let truncate_nb = min (max 1 (int_of_float (float_of_int (Iter.length subst_iter_all) *. 0.1))) 5 in
    let subst_iter = iter_truncate truncate_nb subst_iter_all in
    (*Printf.printf "new subst %i\n" (Iter.length subst_iter);*)
    (*Printf.printf "We are allowing %i new subst\n" (int_of_float (float_of_int (Iter.length subst_iter_all) *. 0.1));*)
    (*apply the substitutions to the poly type arguments*)
    (*split them into the new_mono and new_poly type arguments*)
    let new_mono_map, new_poly_map = apply_subst_map poly_type_args_map new_poly_subst old_poly_subst in

    (*apply the substitutions to the literals*)
    let new_lits_iter = 
        Array.fold_left (fun acc lit -> Iter.union ~eq:Literal.equal acc (Iter.map (apply_subst_lit lit) subst_iter)) Iter.empty literals
    in


    let new_lits_arr = Iter.to_array new_lits_iter in

    (*returns the new_mono_map, new_poly_map and new_literals*)
    new_mono_map, new_poly_map, new_lits_arr 


(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map from function symbols to sets (iter for now) of polymorphic type arguments
 * takes a list of clauses under the form of a (clause_id * literal array) (clause_ids are ints)
 * returns an updated monomorphic map, polymorphic map and list of updated clauses *)
let mono_step clause_list mono_map poly_clause_map =
    let print_all_type_args fun_sym iter =
        Printf.printf "for this function symbol: %s -- we have the following type arguments (old) :\n" (ID.name fun_sym);
        Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (fst iter);
        Printf.printf "(new) :\n";
        Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (snd iter);
    in
    (*ArgMap.iter print_all_type_args mono_map;*)


    let new_lits = ref 0 in
    (*let ty_arg_map_fold original_map fun_sym new_iter acc_map =
        let original_old_iter, original_new_iter = ArgMap.find fun_sym original_map in
        (*Printf.printf "perhaps here? %i\n" (Iter.length new_old_iter);*)
        ArgMap.add fun_sym (new_old_iter, new_iter) acc_map
    in*)
    (* given an accumulator that contains a list of clauses and two type argument maps (one mono and one poly)
     * returns an accumulator updated with regards to the given literals*)
    let process_clause acc (clause_id, literals) =
        let (acc_clauses, acc_mono_map, acc_poly_clause_map) = acc in
        (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
        let poly_map = ClauseArgMap.find clause_id poly_clause_map in

        (* newly generated literals and type arguments*)
        let (new_mono_map, new_poly_map, new_literals) = mono_step_clause mono_map poly_map literals in

        let merge_iter _ iter_1 iter_2 = Some (Iter.union ~eq:ty_arg_eq iter_1 iter_2) in
        let res_mono_map = ArgMap.union merge_iter new_mono_map acc_mono_map in
        (* this entails that if two clauses have the same id, then the type arguments derived from the earlier
         * ones will be overwritten*)
        let res_poly_clause_map = ClauseArgMap.add clause_id new_poly_map acc_poly_clause_map in

        let lit_is_monomorphic = function
            | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
            | _ -> true
        in
        (*only add monomorphic literals, we already generate the new types ourselves and we will
         * filter out non-monomorphic literals at the end anyways*)
        let mono_lits = Array.of_list (List.filter lit_is_monomorphic (Array.to_list new_literals)) in

        (* TODO make bound better *)
        let max_arr_index = 5 + (1000 / (List.length clause_list)) in
        let mono_lits_truncated = Array.sub mono_lits 0 (min (Array.length mono_lits) max_arr_index) in
        
        new_lits := !new_lits + (Array.length mono_lits_truncated);

        ((clause_id, mono_lits_truncated)::acc_clauses, res_mono_map, res_poly_clause_map)
    in
    let new_clauses, new_mono_map, new_poly_clause_map = 
        List.fold_left process_clause ([], ArgMap.empty, ClauseArgMap.empty) clause_list
    in
    let age_map original_map extra_map =
        let new_args_iter fun_sym = match ArgMap.find_opt fun_sym extra_map with
            | Some iter -> iter
            | None -> Iter.empty
        in
        let iter_age_fold fun_sym (original_old_iter, original_new_iter) acc_map =
            let new_old_iter = Iter.union ~eq:ty_arg_eq original_old_iter original_new_iter in
            (*Printf.printf "all old are now: %i\n" (Iter.length new_old_iter);*)
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
    Printf.printf "\nwe have an extra %i new lits generated\n" !new_lits;
    new_clauses, res_mono_map, res_poly_clause_map

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
    let map_update_fun ty_args mono_case = function
        | None when mono_case -> Some (Iter.empty, Iter.singleton ty_args)
        | Some (_, curr_iter) when mono_case -> Some (Iter.empty, Iter.cons ty_args curr_iter)
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
                        (fun _ pair_1 pair_2-> Some (merge_map_arg_iter pair_1 pair_2))
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

    (* another check due to a later find*)
    (assert (List.for_all (fun (clause_id, _) -> ClauseArgMap.find_opt clause_id init_clause_poly_map != None) clause_list));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key init_mono_map != None) poly_map ) init_clause_poly_map));

    (* monomorphisation loop *)
    let rec monomorphisation_loop curr_count mono_map poly_clause_map clause_list =
        let mono_map = ArgMap.map (fun (new_iter, old_iter) -> Iter.sort_uniq new_iter, Iter.sort_uniq old_iter) mono_map in
        Printf.printf "we have %i total type args\n" (ArgMap.fold (fun _ (old_iter, new_iter) acc -> (Iter.length old_iter) + (Iter.length new_iter) + acc) mono_map 0);
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
        (* very ugly to change with refactoring *)
        let mono_clauses = List.map (fun (clause_id, lit_arr) -> clause_id, Array.of_list (List.filter lit_is_monomorphic (Array.to_list lit_arr))) clause_list_res in
        let mono_clauses_no_empty = List.filter (fun (_, lit_arr) -> Array.to_list lit_arr != []) mono_clauses in
        mono_clauses_no_empty
    in

    let lits_replace = Array.map (fun _ -> Literal.mk_absurd) in
    let crap_clauses = List.map (fun (clause_id, lits) -> clause_id, lits_replace lits) mono_clause_list_res in
    Printf.printf "We end up with a grand total of ... %i clauses!\n" (List.length crap_clauses);
    mono_clause_list_res

(* We're not done yet, because even though we have monomorphised the clauses, they still make use of polymorphic type constructors which can't be handled by e 
 * therefore, we must replace all instantiated polymorphic type constructors by a monomorphic type, this should not be hard, ex: replace all list int by list_int
 * all fun int bool by fun_int_bool ect ...*)

let rec convert_type ty = 
    let args = Ty.expected_args ty in
    let ret = Ty.returns ty in
    if args != [] then
        let open Ty in
        (List.map convert_type args) ==> (convert_type ret)
    else Ty.const (ID.make (Ty.mangle ty))
    

    
