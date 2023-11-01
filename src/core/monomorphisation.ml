
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

(* TODO make a neat little module with an ergonomic interface *)
(* TODO massive refactor once we get this working*)
(* TODO find more efficient data structures for this process, iter are easy to manipulate but sets would
 * probably be more appropriate *)
(* TODO make parameters proportional*)
(* TODO remove literals with uninstantiable type variables *)
(* TODO rewrite typed_sym to get rid of all the junk*)
(* TODO rewrite final monomorphic filtering more elegantly*)
(* TODO use sets of lits to make sure we don't have duplicates*)
(* TODO perhaps split the monomorphic and polymorphic type arguments into other maps so that we don't 
 * generate the same substitutions at each loop*)

(* Iter.union needs to be provided an equality function because we are dealing in types for which ocaml has no builting equality *)
let ty_arg_eq ty_arg1 ty_arg2 = List.for_all Fun.id (List.map2 Ty.equal ty_arg1 ty_arg2)

let is_not_meta ty =
    not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

let is_instantiated ty =
    (*Ty.expected_ty_vars ty == 0  && not (Type.Seq.sub ty |> Iter.exists Type.is_tType)*)
    List.for_all is_not_meta (Ty.expected_args ty) && Ty.expected_ty_vars ty = 0

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
            subst_iter
    in
    List.fold_left2 combine Iter.empty type_list_mono type_list_poly


(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns a set (iter for now) of the type substitutions that can be derived from the given maps *)
let derive_type_arg_subst mono_map poly_map = 
    (*derives the substitutions from two sets (iters) of type arguments*)
    let type_arg_iter_subst mono_type_args_iter poly_type_args_iter =
        let poly_arg_iter mono_type_args_iter poly_type_list =
            let res = Iter.flat_map (type_arg_list_subst poly_type_list) mono_type_args_iter in
            res
        in
        Iter.flat_map (poly_arg_iter mono_type_args_iter) poly_type_args_iter
    in
    (* using find because we assume that all function symbols have been recorded in the mono_map*)
    let combine fun_sym poly_args_iter acc =
        (assert (ArgMap.find_opt fun_sym mono_map != None));
        Iter.union ~eq:Subst.equal ~hash:Subst.hash (type_arg_iter_subst (ArgMap.find fun_sym mono_map) poly_args_iter) acc
    in
    ArgMap.fold combine poly_map Iter.empty

let iter_truncate len iter =
    Iter.filter_mapi (fun count elem -> if count < len then Some(elem) else None) iter

(* given a map from function symbols to polymorphic type arguments
 * given a set (iter for now) of type substitutions
 * generates two maps of the derived monomorphic and polymorphic type arguments *)
(* Possible optimisation, do this step at the same time as deriving the substitutions *)
let apply_subst_map poly_map subst_iter =
    let iter_map ty_list =
        Iter.map (fun subst -> List.map (apply_ty_subst subst) ty_list) subst_iter
    in
    let mixed_map = ArgMap.map (Iter.flat_map iter_map) poly_map in
    let split_iter type_args_iter =
        (* might be able to find a more efficient way of doing this*)
        let mono_type_args = Iter.filter (List.for_all is_instantiated) type_args_iter in
        let poly_type_args = Iter.filter (List.for_all (fun ty -> not (is_instantiated ty))) type_args_iter in
        mono_type_args, poly_type_args
    in
    let combine_split fun_sym type_args_iter (acc_mono_map, acc_poly_map) =
        let mono_iter, poly_iter = split_iter type_args_iter in
        (* TODO parametrise and rationalise bounds*)
        let mono_iter_bound = min 10 (int_of_float (float_of_int (Iter.length (ArgMap.find fun_sym poly_map)) *. 0.5)) in
        let poly_iter_bound = min 10 (int_of_float (float_of_int (Iter.length (ArgMap.find fun_sym poly_map)) *. 0.5)) in
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
    let subst_iter_all = Iter.sort_uniq (derive_type_arg_subst mono_type_args_map poly_type_args_map) in

    (* TODO parametrise bound find some reasonable way to order the subst iter such that truncating makes sense*)
    let truncate_nb = min (max 1 (int_of_float (float_of_int (Iter.length subst_iter_all) *. 0.1))) 5 in
    let subst_iter = iter_truncate truncate_nb subst_iter_all in
    (*Printf.printf "We are allowing %i new subst\n" (int_of_float (float_of_int (Iter.length subst_iter_all) *. 0.1));*)
    (*apply the substitutions to the poly type arguments*)
    (*split them into the new_mono and new_poly type arguments*)
    let new_mono_map, new_poly_map = apply_subst_map poly_type_args_map subst_iter in

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
    let new_lits = ref 0 in
    let process_clause acc (clause_id, literals) =
        let (acc_clauses, acc_mono_map, acc_poly_clause_map) = acc in
        (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
        let poly_map = ClauseArgMap.find clause_id poly_clause_map in
        let (new_mono_map, new_poly_map, new_literals) = mono_step_clause mono_map poly_map literals in
        let res_mono_map = ArgMap.union (fun _ elem1 elem2 -> Some (Iter.union ~eq:ty_arg_eq elem1 elem2)) acc_mono_map new_mono_map in
        let res_poly_map = ArgMap.union (fun _ elem1 elem2 -> Some (Iter.union ~eq:ty_arg_eq elem1 elem2)) poly_map new_poly_map in
        let res_poly_clause_map = ClauseArgMap.add clause_id res_poly_map acc_poly_clause_map in

        let lit_is_monomorphic = function
            | Literal.Equation (lt, rt, _) -> T.monomorphic lt && T.monomorphic rt
            | _ -> true
        in
        let mono_lits = Array.of_list (List.filter lit_is_monomorphic (Array.to_list new_literals)) in

        (* TODO make bound better *)
        (* we want at most 1k new lits per monomorphisation loop iteration *)
        (* we still want at least 5 new lit per clause*)
        let max_arr_index = 5 + (1000 / (List.length clause_list)) in
        let mono_lits_truncated = Array.sub mono_lits 0 (min (Array.length mono_lits) max_arr_index) in
        
        new_lits := !new_lits + (Array.length mono_lits_truncated);

        ((clause_id, mono_lits_truncated)::acc_clauses, res_mono_map, res_poly_clause_map)
    in
    let res = List.fold_left process_clause ([], mono_map, poly_clause_map) clause_list in
    Printf.printf "\nwe have an extra %i new lits generated\n" !new_lits;
    res

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * same for polymorphic type arguments
 * takes a term
 * returns the maps updated with the additional function symbol -> type arguments bindings derived from the term
 * note that all function symbols are added to the maps, even when no corresponding type arguments are found
 * this is to avoid trouble when ArgMap.find is used later *)
let add_typed_sym mono_map poly_map term =
    let typed_symbols = typed_sym term in
    let type_args_are_mono = List.for_all Ty.is_ground in
    (*using tuples because this function will be used in a fold*)
    let update_maps (curr_mono_map, curr_poly_map) (ty_sym, ty_args) =
        let ty_args_mono = type_args_are_mono ty_args in
        (*perhaps using ArgMap.update could yeild something more compact*)
        let new_mono_map = match ArgMap.find_opt ty_sym curr_mono_map with
            | None when ty_args_mono -> ArgMap.add ty_sym (Iter.singleton ty_args) curr_mono_map
            | Some type_args_iter when ty_args_mono ->
                    ArgMap.add ty_sym (Iter.cons ty_args type_args_iter) curr_mono_map
            | None -> ArgMap.add ty_sym Iter.empty curr_mono_map
            | Some _ -> curr_mono_map
        in
        (*basically the same code as above, will need to be refactored out*)
        let new_poly_map = match ArgMap.find_opt ty_sym curr_poly_map with
            | None when not ty_args_mono -> ArgMap.add ty_sym (Iter.singleton ty_args) curr_poly_map
            | Some type_args_iter when not ty_args_mono ->
                    ArgMap.add ty_sym (Iter.cons ty_args type_args_iter) curr_poly_map
            | None -> ArgMap.add ty_sym Iter.empty curr_poly_map
            | Some _ -> curr_poly_map 
        in
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
    (assert (ArgMap.for_all (fun fun_sym _ -> ArgMap.find_opt fun_sym new_mono_map != None) new_poly_map));
    let new_clause_poly_map = match ClauseArgMap.find_opt clause_id clause_poly_map with
        | None -> ClauseArgMap.add clause_id new_poly_map clause_poly_map
        | Some other_poly_map ->
                ClauseArgMap.add clause_id
                    (ArgMap.union
                        (fun _ elem1 elem2 -> Some (Iter.union ~eq:ty_arg_eq elem1 elem2))
                        new_poly_map other_poly_map)
                    clause_poly_map
    in
    let all_ty_syms = Iter.flat_map typed_sym clause_terms_iter in
    (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym new_mono_map != None) all_ty_syms));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key new_mono_map != None) poly_map ) new_clause_poly_map));

    new_mono_map, new_clause_poly_map

(* takes a list of (clause_id, literal array) pairs
 * takes an integer to limit the numbers of iterations
 * returns an updated list of clauses *)
let monomorphise_problem clause_list loop_count =
    (* create initial maps *)
    let init_mono_map, init_clause_poly_map =
        List.fold_left map_initialisation_step (ArgMap.empty, ClauseArgMap.empty) clause_list in

    (* remove duplicates *)
    let init_mono_map = ArgMap.map (fun iter -> Iter.sort_uniq iter) init_mono_map in

    Printf.printf "\n initial symbol nb: %i\n" (ArgMap.fold (fun _ iter acc -> (Iter.length iter) + acc) init_mono_map 0);
    
    (* another check due to a later find*)
    (assert (List.for_all (fun (clause_id, _) -> ClauseArgMap.find_opt clause_id init_clause_poly_map != None) clause_list));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key init_mono_map != None) poly_map ) init_clause_poly_map));

    (* monomorphisation loop *)
    let rec monomorphisation_loop curr_count mono_map poly_clause_map clause_list =
        let mono_map = ArgMap.map (fun iter -> Iter.sort_uniq iter) mono_map in
        Printf.printf "so, how's the explosion going? %i\n" (ArgMap.fold (fun _ iter acc -> (Iter.length iter) + acc) mono_map 0);
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

    mono_clause_list_res
