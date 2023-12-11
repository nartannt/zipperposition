
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
module SubstMap = Map.Make(Int)
module PbSubstMap = Map.Make(Int)

(* Note: for ease of notation, variables, functions ... use "polymorphic" in the sense of "non-monomorphic" *)

(* TODO make a neat little module with an elegant interface *)
(* TODO massive refactor once we get this working*)
(* TODO write nice documentation and comments *)
(* TODO add option to choose substitutions semi-randomly*)
(* TODO clean up interface with the rest of the prover*)
(* TODO unit tests *)
(* TODO integration tests *)
(* TODO squash all commits and make the necessary rebase so that this can be added to the main zipperposition branch*)

type basic_bounds = {
    relative_bound : float;
    absolute_cap : int;
    relative_floor : int;
}

type all_bounds = {
    mono_clause : basic_bounds;
    poly_clause : basic_bounds;
    subst_per_ty_var : int;
    monomorphising_subst : int;
    new_clauses_relative_bound : float;
}

let begin_time = ref 0.0
let total_count = ref 0
let total_time = ref 0.0

(* TODO find if there is something more efficient *)
let remove_duplicates iter ~eq = 
    Iter.map List.hd (Iter.group_by ~eq iter)

(* TODO add this to Type.ml (with better name) *)
let rec my_ty_eq ty ty' =
    let res = match Ty.view ty, Ty.view ty' with
        | Fun (l, ty), Fun (l', ty') ->
            (List.for_all2 my_ty_eq l l' && my_ty_eq ty ty')
        | Forall ty, Forall ty' -> my_ty_eq ty ty'
        | Var var, Var var' when Ty.is_tType (HVar.ty var) && Ty.is_tType (HVar.ty var')
            -> HVar.equal ( fun _ _ -> true) var var'
        | Builtin b, Builtin b' -> b = b'
        | DB i, DB i' -> i = i'
        (* TODO check with someone that knows the code if using the name is fine
         * my suspicion is that it isn't, in that case attempt to find alternative solution*)
        | App (f, l), App (f', l') -> ID.name f = ID.name f' && List.for_all2 my_ty_eq l l'
        | _ ->  false
    in
    res

(* Iter.union needs to be provided an equality function when dealing with lists of types *)
(* not that Ty.equal is a physical equality*)
let ty_arg_eq ty_arg1 ty_arg2 =
    let start_time = Sys.time() in
    let res = List.for_all2 my_ty_eq ty_arg1 ty_arg2 in
    total_time := !total_time +. (Sys.time() -. start_time);
    total_count := !total_count + 1;
    res
    

let lit_is_monomorphic = function
    | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
    | _ -> true

(* the given type does not contain any tType *)
let is_not_meta ty =
    not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

(* the given type is not meta and requires no type arguments*)
(*relation with ground?*)
let is_instantiated ty =
    (List.for_all is_not_meta (Ty.expected_args ty)) && Ty.expected_ty_vars ty = 0

(* returns the substitution that allows matching a monomorphic type against a type *)
let match_type ty ~mono_type =
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
    Literal.apply_subst Subst.Renaming.none subst (lit, 0)

(* merges two maps by union of their iters*)
let merge_map_arg_iter (old_ty_args_1, new_ty_args_1) (old_ty_args_2, new_ty_args_2) =
    Iter.union ~eq:ty_arg_eq old_ty_args_1 old_ty_args_2, Iter.union ~eq:ty_arg_eq new_ty_args_1 new_ty_args_2


(* the union of two substitution iters*)
let iter_subst_union = Iter.union ~eq:Subst.equal ~hash:Subst.hash

(* takes a list of monomorphic types
 * takes a list of polymorphic types
 * returns an iter of type substitutions that match the 
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


(* given a basic bound and the size of whatever object we are bounding
 * returns the numbers of elements to keep*)
let max_nb len bound =
    let rel_cap = int_of_float (float_of_int len *. bound.relative_bound) in
    min bound.absolute_cap (max bound.relative_floor rel_cap)

(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns an iter of the type substitutions that can be derived from the given maps *)
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
            (*assumes that old_mono_args and new_mono_args are distinct, which should be the case*)
            (* TODO the uniq should be useless, keeping it for testing in the meantime*)
            type_arg_iter_subst (remove_duplicates ~eq:ty_arg_eq (Iter.append old_mono_args new_mono_args)) new_poly_args
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
    (* TODO this could potentially be faster *)
    (*Iter.drop ((Iter.length iter) - len) iter*)

(* given a map from function symbols to polymorphic type arguments
 * given an iter of type substitutions
 * generates two maps of the derived monomorphic and polymorphic type arguments *)
let apply_subst_map old_mono_map poly_map new_poly_subst old_poly_subst =
    (* applies the substitution to the type arguments, returns some iff the result is different from
     * the original type arguments *)
    let apply_ty_subst_arg subst ty_args =
        List.map (apply_ty_subst subst) ty_args
    in

    let apply_subst_iter (old_poly_args_iter, new_poly_args_iter) =
        let applied_poly_args_1 = Iter.flat_map (fun subst -> Iter.map (apply_ty_subst_arg subst) new_poly_args_iter) new_poly_subst in
        let applied_poly_args_2 = Iter.flat_map (fun subst -> Iter.map (apply_ty_subst_arg subst) old_poly_args_iter) old_poly_subst in
        Iter.union ~eq:ty_arg_eq applied_poly_args_1 applied_poly_args_2
    in

    (* map of both monomorphic and polymorphic type arguments *)
    let mixed_map = ArgMap.map apply_subst_iter poly_map in

    (* splits the mixed map into its monomorphic and polymorphic components *)
    let split_iter type_args_iter =
        let type_args_iter = Iter.persistent_lazy type_args_iter in
        (* might be able to find a more efficient way of doing this, instead of going through the iter twice*)
        let mono_type_args = Iter.filter (List.for_all Ty.is_ground) type_args_iter in
        let poly_type_args = Iter.filter (List.for_all (fun ty -> not (Ty.is_ground ty))) type_args_iter in
        mono_type_args, poly_type_args
    in

    let combine_split fun_sym type_args_iter (acc_mono_map, acc_poly_map) =
        let mono_iter, poly_iter = split_iter type_args_iter in

        (* the diff prevents rederiving the same substitutions, indeed if we have alpha among the poly_ty_args we will continously
         * rederive all the monomorphic type arguments*)
        let new_mono_map = ArgMap.add fun_sym (remove_duplicates ~eq:ty_arg_eq (Iter.persistent_lazy mono_iter)) acc_mono_map in
        (*TODO make similar check here, likely not as important as the mono case*)
        let new_poly_map = ArgMap.add fun_sym (remove_duplicates ~eq:ty_arg_eq (Iter.persistent_lazy poly_iter)) acc_poly_map in
        new_mono_map, new_poly_map
    in
    let new_mono_map_all, new_poly_map_all = ArgMap.fold combine_split mixed_map (ArgMap.empty, ArgMap.empty) in
    let new_mono_map = ArgMap.mapi (fun fun_sym mono_iter -> Iter.diff ~eq:ty_arg_eq mono_iter (ArgMap.find fun_sym old_mono_map)) new_mono_map_all in
    let new_poly_map = ArgMap.mapi (fun fun_sym poly_iter -> Iter.diff ~eq:ty_arg_eq poly_iter (fst (ArgMap.find fun_sym poly_map))) new_poly_map_all in
    new_mono_map, new_poly_map
    
(* given a subst iter corresponding to a clause, given a bound that limits the number of substitutions
 * per type variable, returns an iter of the selected substitutions *)
(* the variables are ordered with respect to (HVar.compare InnerTerm.compare) basically an arbitrary order*)
let select_subst subst_iter ty_vars_to_instantiate ty_var_subst_max =
    let subst_iter = Iter.persistent_lazy subst_iter in
    let can_monomorphise =
        let subst_ty_vars = Iter.flat_map (fun subst -> Iter.map Scoped.get (Subst.domain subst)) subst_iter in
        Iter.subset ~eq:(HVar.equal InnerTerm.equal) subst_ty_vars ty_vars_to_instantiate
    in
    if not can_monomorphise then Iter.empty
    else
        let sorted_ty_vars = Iter.sort_uniq ~cmp:(fun var var' -> HVar.compare InnerTerm.compare var var') ty_vars_to_instantiate in
        let select_subst_for_var ty_var =
            let subst_iter_for_var = Iter.filter (fun subst -> Subst.mem subst ty_var) subst_iter in
            (* using whatever order the substitutions are in to select them *)
            let selected_subst = iter_truncate ty_var_subst_max subst_iter_for_var in
            selected_subst 
        in
        let select_var_fold acc ty_var = iter_subst_union acc (select_subst_for_var ty_var) in
        Iter.fold select_var_fold Iter.empty (Iter.map (fun var -> (var, 0)) sorted_ty_vars)

(* generates an iter of monomorphising substitutions obtained from the subst_iter 
 * at most new_clauses_max new substitutions will be returned (maybe +1) *)
(* assumes that the subst_iter is somehow sorted *)
let generate_monomorphising_subst subst_iter vars_to_instantiate new_clauses_max = 
    (*Printf.printf "start generating monomorphising substitutions %f\n" (Sys.time() -. !begin_time);*)
    (*Printf.printf "we are generating monomorphising substitutions\n";*)
    (*Printf.printf "begin with %i substitutions to deal with\n" (Iter.length subst_iter);*)
    (*Array.iter (fun lit -> Printf.printf "%s\n" (Literal.to_string lit)) lit_arr;*)
    let subst_iter  = Iter.persistent_lazy subst_iter in
    let var_eq = HVar.equal (fun _ _ -> true) in
    let var_eq_sc var var' = var_eq (fst var) (fst var') in
    let instantating_subst ty_var subst_iter =
        Iter.filter (fun subst -> Subst.mem subst ty_var) subst_iter
    in
    let rec monomorphising_subst_iter subst_iter vars_to_instantiate subst_acc curr_subst_count = 
        match Iter.head vars_to_instantiate with
            | None -> Iter.singleton subst_acc, curr_subst_count - 1
            | Some ty_var ->
                (*Printf.printf "this is the subst we have %s\n" (Subst.to_string subst_acc);*)
                let next_substitutions = instantating_subst ty_var subst_iter in
                let next_vars curr_vars subst = remove_duplicates ~eq:var_eq_sc (Iter.diff ~eq:var_eq_sc curr_vars (Subst.domain subst)) in
                let subst_fold (acc, acc_count) subst =
                    if acc_count < 0 then acc, acc_count
                    else
                        let mono_subst_res, res_count =
                            match Subst.merge subst subst_acc with
                                | exception _ -> acc, acc_count
                                (* discussed with Jasmin only allows composition of compatible substitutions (ie: merging) *)
                                | merged_subst -> 
                                    let new_vars_to_instantiate = next_vars vars_to_instantiate subst in
                                    (*Printf.printf "we got that diff len %i\n" (Iter.length new_vars_to_instantiate);*)
                                    (*Printf.printf "That domain is %i\n" (Subst.domain subst |> Iter.length);*)
                                    monomorphising_subst_iter subst_iter new_vars_to_instantiate merged_subst acc_count in
                        if res_count < 0 then acc, res_count
                        else 
                            iter_subst_union acc mono_subst_res, res_count
                in
                Iter.fold subst_fold (Iter.empty, curr_subst_count) next_substitutions
    in
    let scoped_vars = Iter.map (fun var -> var, 0) vars_to_instantiate in
    let mono_subst_iter, _ = monomorphising_subst_iter subst_iter scoped_vars Subst.empty new_clauses_max in
    (*Printf.printf "end up wiht %i substitutions\n" (Iter.length mono_subst_iter);*)
    (*Printf.printf "we are done generating monomorphising substitutions\n";*)
    (*Printf.printf "end generating monomorphising substitutions %f\n" (Sys.time() -. !begin_time);*)
    Iter.persistent_lazy mono_subst_iter

let print_all_type_args fun_sym iter =
    Printf.printf "for this function symbol: %s -- we have the following type arguments  \n(old) :\n" (ID.name fun_sym);
    Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (fst iter);
    Printf.printf "(new) :\n";
    Iter.iter (fun ty_args -> Printf.printf "%s\n" (String.concat "; " (List.map Ty.to_string ty_args))) (snd iter)


let all_arr_len = ref 0



(* given a subst map, an iter of substitutions and the current iteration,
   will update the map accordingly*)
let update_susbt_map all_subst curr_map curr_iteration =
    let add_single_subst (subst_map: ((Subst.t * int ) Iter.t SubstMap.t)) subst =
        let update_map subst = function
            | None -> Some (Iter.singleton (subst, curr_iteration))
            | Some iter -> Some (Iter.cons (subst, curr_iteration) iter)
        in
        Iter.fold (fun curr_map ty_var -> SubstMap.update (HVar.id ty_var) (update_map subst) curr_map) subst_map (Iter.map fst (Subst.domain subst))
    in
    let res = Iter.fold add_single_subst curr_map all_subst in
    res


(* takes a map from functions symbols to sets (iter for now) of monomorphic type arguments
 * takes an array of literals
 * takes a map from clause_ids to a map of function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map of type variables to iters of (substitution, int) pairs
 * this stores all the generated substitutions for each type variable, the integer is used to keep track of the
 * iteration at which it was generated
 * returns a map of new monomorphic type arguments
 * returns a map of new polymorphic type arguments
 * returns the updated substitution map *)
let mono_step_clause mono_type_args_map poly_type_args_map susbt_clause_map curr_iteration literals bounds =

    if false then
        begin
        Printf.printf "Monomorphic\n";
        ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter) mono_type_args_map;
        Printf.printf "Polymorphic\n";
        ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter) poly_type_args_map;
        end;

    (*generate all substitutions from mono and poly type arguments*)
    let new_poly_subst_all, old_poly_subst_all = derive_type_arg_subst mono_type_args_map poly_type_args_map in
    let subst_iter_all = iter_subst_union new_poly_subst_all old_poly_subst_all in

    (*apply the substitutions to the poly type arguments*)
    (*split them into the new_mono and new_poly type arguments*)
    let new_mono_map_all, new_poly_map_all = apply_subst_map (ArgMap.map fst mono_type_args_map) poly_type_args_map new_poly_subst_all old_poly_subst_all in

    (* truncationg the new type arguments according to the bounds *)
    (* TODO factorise with similar truncation done in mono_step for the monomorphic map*)
    let new_poly_map = 
        ArgMap.mapi (fun fun_sym iter -> 
            let all_poly_ty_args = ArgMap.find fun_sym poly_type_args_map in 
            let cap = max_nb (Iter.length (fst all_poly_ty_args) + Iter.length (snd all_poly_ty_args)) bounds.poly_clause in
            Iter.persistent (iter_truncate (max_nb cap bounds.poly_clause) iter)) 
            new_poly_map_all
    in

    new_mono_map_all, new_poly_map, (update_susbt_map subst_iter_all susbt_clause_map curr_iteration)


let count = ref 0

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map from function symbols to sets (iter for now) of polymorphic type arguments
 * takes a list of clauses under the form of a (clause_id * literal array) (clause_ids are ints)
 * returns an updated monomorphic map, polymorphic map and list of updated clauses *)
let mono_step clause_list mono_map poly_clause_map subst_map curr_iter bounds =

    (*Printf.printf "We have %i total literals\n" !all_arr_len;*)
    
    (* given an accumulator that contains a list of clauses and two type argument maps (one mono and one poly)
     * returns an accumulator updated with regards to the given literals*)
    let process_clause acc (clause_id, literals) =

        let (acc_subst, acc_mono_map, acc_poly_clause_map) = acc in

        (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
        let poly_map = ClauseArgMap.find clause_id poly_clause_map in
        let old_clause_subst_map = PbSubstMap.find clause_id subst_map in

        let (new_mono_map_all, new_poly_map, new_clause_subst_map) = mono_step_clause mono_map poly_map old_clause_subst_map curr_iter literals bounds in

        let new_mono_map = new_mono_map_all in
        
        let new_mono_ty_args = ArgMap.fold (fun _ iter acc -> (Iter.length iter) + acc) new_mono_map 0 in
        count := !count + new_mono_ty_args;
        (*if !count mod 100 = 0 then*)
            (*Printf.printf "we have a count of %i\n" !count;*)

        let merge_iter _ iter_1 iter_2 = Some (remove_duplicates ~eq:ty_arg_eq (Iter.append iter_1 iter_2)) in
        let res_mono_map = ArgMap.union merge_iter new_mono_map acc_mono_map in
        (* this entails that if two clauses have the same id, then the type arguments derived from the earlier
         * ones will be overwritten*)
        let res_poly_clause_map = ClauseArgMap.add clause_id new_poly_map acc_poly_clause_map in

        (*let new_clause_list = Iter.to_list (Iter.map (fun lit_arr -> clause_id, lit_arr) new_mono_clauses) in*)
        let res_subst_map = PbSubstMap.add clause_id new_clause_subst_map acc_subst in

        (res_subst_map, res_mono_map, res_poly_clause_map)
    in
    let new_subst_map, new_mono_map_all, new_poly_clause_map = 
        List.fold_left process_clause (subst_map, ArgMap.empty, ClauseArgMap.empty) clause_list
    in
    let new_mono_map = 
        ArgMap.mapi (fun fun_sym iter -> 
            let mono_args = ArgMap.find fun_sym mono_map in
            let cap = max_nb (Iter.length (fst mono_args) + Iter.length (snd mono_args)) bounds.mono_clause in
            Iter.persistent_lazy (iter_truncate cap iter)) new_mono_map_all
    in
    let age_map original_map extra_map =
        let new_args_iter fun_sym = match ArgMap.find_opt fun_sym extra_map with
            | Some iter -> iter
            | None -> Iter.empty
        in
        let iter_age_mapi fun_sym (old_iter, new_iter) =
            (Iter.persistent (Iter.union ~eq:ty_arg_eq old_iter new_iter), Iter.persistent_lazy (new_args_iter fun_sym))
        in
        ArgMap.mapi iter_age_mapi original_map
    in
    let res_mono_map = age_map mono_map new_mono_map in
    let clause_map_age clause_id original_poly_map =
        match ClauseArgMap.find_opt clause_id new_poly_clause_map with
            | None -> age_map original_poly_map ArgMap.empty
            | Some extra_poly_map -> age_map original_poly_map extra_poly_map
    in
    let res_poly_clause_map = ClauseArgMap.mapi clause_map_age poly_clause_map in
    new_subst_map, res_mono_map, res_poly_clause_map

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
    (*(assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_mono_map != None) typed_symbols));
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym res_poly_map != None) typed_symbols));
    (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym res_mono_map != None) res_poly_map));*)
    res_mono_map, res_poly_map

(* for a clause, removes polymorphic type arguments that contain one or more type variables which cannot be instantiated *)
(* the test is making sure that the mono_map is empty for every function symbol in which the type variable appears, so some
 * type variables which can't be instantiated will not be removed *)
let poly_ty_args_filter mono_map poly_map =
    let ty_var_eq = HVar.equal my_ty_eq in
    let vars_of_ty_args ty_args =
        Iter.flat_map (fun ty_list -> List.fold_left (fun acc ty -> Iter.union ~eq:ty_var_eq acc (Ty.Seq.vars ty)) Iter.empty ty_list) ty_args
    in
    let ty_vars_iter = remove_duplicates ~eq:ty_var_eq (Iter.persistent_lazy (ArgMap.fold (fun _ (_, ty_args_iter) acc -> Iter.append (vars_of_ty_args ty_args_iter) acc) poly_map Iter.empty)) in
    let ty_var_uninstantiable curr_poly_map ty_var =
        ArgMap.for_all (fun fun_sym (_, ty_args_iter) -> not (Iter.mem ~eq:ty_var_eq ty_var (vars_of_ty_args ty_args_iter)) || Iter.is_empty (snd (ArgMap.find fun_sym mono_map))) curr_poly_map
    in
    let ty_vars_to_remove = Iter.persistent_lazy (Iter.filter (ty_var_uninstantiable poly_map) ty_vars_iter) in
    let ty_args_filter ty_list =
        List.exists (fun ty -> not (Iter.exists (fun ty_var -> Iter.mem ~eq:ty_var_eq ty_var ty_vars_to_remove) (Ty.Seq.vars ty))) ty_list
    in
    let ty_arg_map_map (_, ty_args_iter) =
        Iter.empty, remove_duplicates ~eq:ty_arg_eq (Iter.persistent_lazy (Iter.filter ty_args_filter ty_args_iter))
    in
    ArgMap.map ty_arg_map_map poly_map
    


(* given an array of literals, returns an iter of all the terms in literals *)
let terms_iter literals = 
    Literals.Seq.terms literals

let init_single_subst_map literals =
    let all_vars = Literals.Seq.vars literals in
    let all_ty_vars = Iter.filter (fun var -> Type.equal (HVar.ty var) Type.tType) all_vars in
    Iter.fold (fun acc ty_var -> SubstMap.add (HVar.id ty_var) Iter.empty acc) SubstMap.empty all_ty_vars



(* will initialise the maps with the function symbol -> type arguments bindings derived from the clauses *)
let map_initialisation_step (mono_map, clause_poly_map, pb_subst_map) (clause_id, literals) =
    (* TODO find out precisely whether this persistent is useful *)
    let clause_terms_iter = Iter.persistent_lazy (terms_iter literals) in

    let update_maps (curr_mono_map, curr_poly_map) term =
        add_typed_sym curr_mono_map curr_poly_map term
    in
    let new_subst_map = PbSubstMap.add clause_id (init_single_subst_map literals) pb_subst_map in
    let new_mono_map, new_poly_map = Iter.fold update_maps (mono_map, ArgMap.empty) clause_terms_iter in
    
    let remove_duplicate_init map =
        (* we can ignore the first item because it will be empty*)
        (* TODO in fact it would be better to generate a single iter and slot it into a tuple now *)
        ArgMap.map (fun (_, iter) -> Iter.empty, remove_duplicates ~eq:ty_arg_eq (Iter.persistent iter)) map
    in
    let new_poly_map_unique = remove_duplicate_init new_poly_map in
    let new_clause_poly_map = match ClauseArgMap.find_opt clause_id clause_poly_map with
        | None -> ClauseArgMap.add clause_id new_poly_map_unique clause_poly_map
        (*should not happen if each clause has a unique id*)
        | Some other_poly_map ->
                ClauseArgMap.add clause_id
                    (ArgMap.union
                        (fun _ pair_1 pair_2 -> Some (merge_map_arg_iter pair_1 pair_2))
                        new_poly_map_unique other_poly_map)
                    clause_poly_map
    in

    (* The assert represent invariants which hold true, checking them is not necessary *)
    (*let all_ty_syms = Iter.flat_map typed_sym clause_terms_iter in

    (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym new_mono_map != None) new_poly_map));
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym new_mono_map != None) all_ty_syms));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key new_mono_map != None) poly_map ) new_clause_poly_map));*)

    new_mono_map, new_clause_poly_map, new_subst_map

let generate_monomorphising_subst_2 subst_map ty_var_iter max_new_subst =
    let remaining_ty_vars ty_var_iter subst =
        Iter.diff ~eq:(HVar.equal InnerTerm.equal) ty_var_iter (Iter.map fst (Subst.domain subst))
    in
    let rec create_subst (subst_acc, acc_iter, acc_count) vars_to_instantiate =
        if acc_count <= 0 then
            acc_iter, acc_count
        else
            match Iter.head vars_to_instantiate with
                | None -> (Iter.singleton subst_acc), acc_count - 1
                | Some ty_var ->
                    (* TODO reinsert that in map as is*)
                    let tmp = SubstMap.find (HVar.id ty_var) subst_map in
                    let candidate_subst = Iter.map fst tmp in
                    (* here is where the substitution selection method is used *)
                    let process_subst acc_count next_subst =
                        match Subst.merge subst_acc next_subst with
                            | exception _ -> Iter.empty, acc_count
                            | merged_subst ->
                                let new_vars_to_instantiate = remaining_ty_vars vars_to_instantiate merged_subst in
                                let res_subst, res_count = create_subst (merged_subst, acc_iter, acc_count) new_vars_to_instantiate in
                                res_subst, res_count
                    in
                    let process_fold (acc_iter, acc_count) next_subst =
                        if acc_count <= 0 then acc_iter, acc_count
                        else
                            let res_subst, res_count = process_subst acc_count next_subst in
                            iter_subst_union acc_iter res_subst, res_count
                    in
                    Iter.fold process_fold (Iter.empty, acc_count) candidate_subst
    in
    let res = Iter.persistent_lazy (create_subst (Subst.empty, Iter.empty, max_new_subst) ty_var_iter |> fst) in
    (*Printf.printf "nb of monomorphising substitutions %i\n" (Iter.length res);*)
    res


let count_arg_map arg_map =
    ArgMap.fold (fun _ (old_iter, new_iter) acc -> (Iter.length old_iter) + (Iter.length new_iter) + acc) arg_map 0

let count_clause_arg_map clause_arg_map =
    ClauseArgMap.fold (fun _ arg_map acc -> (count_arg_map arg_map) + acc) clause_arg_map 0

(* takes a list of (clause_id, literal array) pairs
 * takes an integer to limit the numbers of iterations
 * returns an updated list of clauses *)
let monomorphise_problem clause_list loop_count =
    total_count := 0;
    total_time := 0.0;

    begin_time := Sys.time();
    Printf.printf "\n so it begins... \n\n";

    (* initialisation *)

    Printf.printf "We start with %i total clauses\n" (List.length clause_list);

    let nb_of_lits = List.fold_left (fun acc (_, lit_arr) -> acc + Array.length lit_arr) 0 clause_list in
    Printf.printf "We start with %i total literals\n" nb_of_lits;

    (* create initial maps *)
    let init_mono_map, init_clause_poly_map, init_subst_map =
        List.fold_left map_initialisation_step (ArgMap.empty, ClauseArgMap.empty, PbSubstMap.empty) clause_list in

    (* remove polymorphic type arguments that contain type variables which cannot be instantiated *)
    let init_clause_poly_map = ClauseArgMap.map (fun poly_map -> poly_ty_args_filter init_mono_map poly_map) init_clause_poly_map in

    if false then
        begin
        Printf.printf "\n here we go\n: ";
        ClauseArgMap.iter (fun clause_id poly_map -> Printf.printf "clause nb: %i\n" clause_id; ArgMap.iter (fun fun_sym iter -> print_all_type_args fun_sym iter) poly_map) init_clause_poly_map;
        end;


    (* remove duplicates *)
    (* the old iters are initialy empty (made redundant by changes in the init function *)
    let init_mono_map = ArgMap.map (fun (old_iter, new_iter) -> Iter.empty, remove_duplicates ~eq:ty_arg_eq new_iter) init_mono_map in

    Printf.printf "after init %f\n" (Sys.time() -. !begin_time);

    let clause_is_monomorphic (_, lit_arr) =
        Array.for_all lit_is_monomorphic lit_arr
    in

    let poly_clause_list = List.filter (fun cl -> clause_is_monomorphic cl |> not) clause_list in

    Printf.printf "We begin with %i polymorphic clauses\n" (List.length poly_clause_list);

    let all_bounds = {
        mono_clause = {
            relative_bound = 2.0;
            absolute_cap = 10000000000;
            relative_floor = 5;
        };
        poly_clause = {
            relative_bound = 0.1;
            absolute_cap = 10000000000;
            relative_floor = 0;
        };
        subst_per_ty_var = 1000000;
        (* number of substitutions generated per clause per iteration *)
        monomorphising_subst = 10;
        new_clauses_relative_bound = 2.0;
    } in
    (* monomorphisation loop *)
    let rec monomorphisation_loop curr_count mono_map poly_clause_map subst_map =
        Printf.printf "count %i \n" !count;
        count := 0;
        Printf.printf "\nbegin loop %f\n" (Sys.time() -. !begin_time);
        Printf.printf "total time %f \n" !total_time;
        (*let mono_map = ArgMap.map (fun (old_iter, new_iter) -> remove_duplicates ~eq:ty_arg_eq (Iter.persistent old_iter), remove_duplicates ~eq:ty_arg_eq (Iter.persistent new_iter)) mono_map in*)
        Printf.printf "we have %i total monomorphic type args\n" (count_arg_map mono_map);
        Printf.printf "we have %i total polymorphic type args\n"
         (count_clause_arg_map poly_clause_map);
        Printf.printf "current time %f\n" (Sys.time() -. !begin_time);

        if curr_count <= 0 then mono_map, poly_clause_map, subst_map
        else
            (* given that the maps are updated independently of the clause list, we could not pass the udpated
             clauses as parameter, however, it is convienient to do so*)
            let new_subst, new_mono_map, new_poly_clause_map = mono_step poly_clause_list mono_map poly_clause_map subst_map curr_count all_bounds in
            let res = monomorphisation_loop (curr_count-1) new_mono_map new_poly_clause_map new_subst in
            res
    in

    let _, _, subst_map_res =
        (* TODO check rigorously if persistent or persistent lazy is best (perhaps nothing at all but i doubt it) *)
        let init_mono_map = ArgMap.map (fun (old_iter, new_iter) -> Iter.persistent old_iter, Iter.persistent new_iter) init_mono_map in
        monomorphisation_loop loop_count init_mono_map init_clause_poly_map init_subst_map in

    let var_eq = HVar.equal (fun _ _ -> true) in
    let clause_ty_vars lit_arr =
        (*Printf.printf "lit_arr length %i\n" (Array.length lit_arr);*)
        all_arr_len := !all_arr_len + Array.length lit_arr;
        (* TODO check that this persistent lazy is worth it *)
        let all_vars = remove_duplicates ~eq:var_eq (Iter.persistent_lazy (Iter.flat_map (fun lit -> (Literal.Seq.vars lit :> InnerTerm.t HVar.t Iter.t)) (Iter.of_array lit_arr))) in
        Iter.filter (fun var -> InnerTerm.equal (HVar.ty var) InnerTerm.tType) all_vars
    in

    let instantiate_clause subst_map (clause_id, lit_arr) new_clauses_remaining =
        let vars_to_instantiate = clause_ty_vars lit_arr in
        (* TODO check that monomorphising subst is possible in the first place *)
        let subst_map_filter_age subst_map iteration_count =
            SubstMap.map (fun subst_iter -> Iter.filter (fun (subst, age) -> age = iteration_count) subst_iter) subst_map
        in
        (* the function is written somewhat awkwardly because we want to generate the substitutions of the first iter first *)
        let rec all_mono_subst curr_iter total_subst_nb =
            if curr_iter < 0 then
                Iter.empty
            else
                let prev_subst = all_mono_subst (curr_iter - 1) total_subst_nb in
                if Iter.length prev_subst >= total_subst_nb then
                    prev_subst
                else
                    let curr_subst =
                        generate_monomorphising_subst_2 (subst_map_filter_age subst_map curr_iter) vars_to_instantiate all_bounds.monomorphising_subst
                    in
                    let curr_subst' = iter_truncate (total_subst_nb - Iter.length prev_subst) curr_subst in
                    Iter.append prev_subst curr_subst'
        in
        let mono_subst = all_mono_subst 5 new_clauses_remaining in
        (*Printf.printf "We have %i monomorphising substitutions\n" (Iter.length mono_subst);*)

        let apply_subst subst lit_arr =
            Array.map (fun lit -> apply_subst_lit lit subst) lit_arr
        in
        (* need to make more thourough checks to see if this persistent_lazy is worth it *)
        let new_lits_iter = Iter.map (fun subst -> apply_subst subst lit_arr) (Iter.persistent_lazy mono_subst) in
        Iter.map (fun lit_arr -> clause_id, lit_arr) new_lits_iter
    in

    let new_clauses_fold (acc_cl, acc_remaining) (clause_id, lit_arr) =
        if acc_remaining <= 0 then
            acc_cl, acc_remaining
        else
            begin
            let new_clauses = instantiate_clause (PbSubstMap.find clause_id subst_map_res) (clause_id, lit_arr) acc_remaining in
            let new_remaining = acc_remaining - Iter.length new_clauses in
            Iter.append acc_cl (iter_truncate acc_remaining new_clauses), new_remaining
            end
    in
    Printf.printf "\nfinished messing with types %f\n" (Sys.time() -. !begin_time);
    let total_clause_limit = max 2000 (int_of_float (all_bounds.new_clauses_relative_bound *. float_of_int (List.length clause_list))) in
    (*Printf.printf "total limit apparently %i\n" total_clause_limit;*)
    let new_clauses, _ = List.fold_left new_clauses_fold (Iter.empty, total_clause_limit) poly_clause_list in


    let mono_clauses = List.filter clause_is_monomorphic clause_list in
    let clause_list = (Iter.to_list new_clauses) @ mono_clauses in


    (* resulting clause_list with updated literals *)

    Printf.printf "generating all clauses %f\n" (Sys.time() -. !begin_time);
    Printf.printf "all new clauses %i\n" (List.length clause_list - List.length mono_clauses);

    Printf.printf "\n\nsmall report: average ty_eq time : %f\n" (!total_time /. float_of_int !total_count);
    Printf.printf "total time : %f\n" !total_time;
    Printf.printf "total count : %i\n" !total_count;
    clause_list


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
        | Builtin _ -> ty        (* TODO this is a temporary fix, need to find better solution, ties in to the mangle problem*)
        | _ -> Ty.const (ID.make (Ty.mangle ty))
