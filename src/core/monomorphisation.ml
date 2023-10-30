
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
(* TODO make parameters propoertional*)
(* TODO quantify at clause level*)
(* TODO remove literals with uninstantiable type variables *)

let is_not_meta ty =
    not (Type.Seq.sub ty |> Iter.exists Type.is_tType)

let is_instantiated ty =
    (*Ty.expected_ty_vars ty == 0  && not (Type.Seq.sub ty |> Iter.exists Type.is_tType)*)
    List.for_all is_not_meta (Ty.expected_args ty) && Ty.expected_ty_vars ty = 0

let match_type ty mono_type =
    let subst = Unif.Ty.matching_same_scope ~scope:0 ~pattern:mono_type ty in
    (*InnerTerm.show_type_arguments := true;
    (Printf.printf "\n old ty:      %s " (Ty.to_string ty));
    (Printf.printf "\n old mono ty: %s " (Ty.to_string mono_type));
    let new_ty = Subst.Ty.apply Subst.Renaming.none subst (ty, 0) in
    (Printf.printf "\n new ty:      %s " (Ty.to_string new_ty));
    InnerTerm.show_type_arguments := false;*)
    (*(Printf.printf "\n mono type: %s" (Ty.to_string mono_type ));
    (*(assert (Iter.is_empty (Ty.Seq.vars mono_type)));*)
    (*(assert (Iter.exists Ty.is_tType (Ty.Seq.sub mono_type) ));*)
    (Printf.printf "\n non-mono type: %s" (Ty.to_string ty ));*)
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
        (*if is_instantiated ty then
            (*(Printf.printf "\n this type: %s" (Ty.to_string (T.ty hd_term));*)
            Printf.printf "\n this term: %s" (T.to_string hd_term);*)
        (*match T.as_const f with
            | Some(id) when is_instantiated ty -> Some(ty_args, id, ty)
            | _ -> None*)
        (* TODO add a function that splits an app into its type arguments and its function symbol
         * in Term.ml*)
        let unsafe_term_to_type (term: T.t) = Ty.of_term_unsafe (term:>InnerTerm.t) in
        match T.head f with
            | Some(id) when is_instantiated ty -> Some(List.map unsafe_term_to_type (snd (T.as_app f)), id, ty)
            | _ -> None
    in
    let res = Iter.filter_map get_typed_sym all_apps in

    (Iter.iter (fun (ty_args, s, _) -> (Printf.printf "\n symbol %s, ty_args: %s" (ID.name s) (String.concat "; " (List.map Ty.to_string ty_args)) )) res);
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
        Iter.cons (match_type poly_ty mono_ty) subst_iter
    in
    List.fold_left2 combine Iter.empty type_list_mono type_list_poly

(* takes a map of function symbols to monomorphic type arguments
 * takes a map of function symbols to polymorphic type arguments
 * returns a set (iter for now) of type substitutions*)
let derive_type_arg_subst mono_map poly_map = 
    let type_arg_iter_subst mono_type_args_iter poly_type_args_iter =
        let poly_arg_iter mono_type_args_iter poly_type_list =
            Iter.flat_map (type_arg_list_subst poly_type_list) mono_type_args_iter
        in
        Iter.flat_map (poly_arg_iter mono_type_args_iter) poly_type_args_iter
    in
    (* using find because we assume that all function symbols have been recorded in the mono_map*)
    let combine fun_sym poly_args_iter acc =
        (assert (ArgMap.find_opt fun_sym mono_map != None));
        Iter.union (type_arg_iter_subst (ArgMap.find fun_sym mono_map) poly_args_iter) acc
    in
    ArgMap.fold combine poly_map Iter.empty

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
    let combine_split fun_sym type_args_iter (mono_map, poly_map) =
        let mono_iter, poly_iter = split_iter type_args_iter in
        let new_mono_map = ArgMap.add fun_sym mono_iter mono_map in
        let new_poly_map = ArgMap.add fun_sym poly_iter poly_map in
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
    let subst_iter = derive_type_arg_subst mono_type_args_map poly_type_args_map in
    (*apply the substitutions to the poly type arguments*)
    (*split them into the new_mono and new_poly type arguments*)
    let new_mono_map, new_poly_map = apply_subst_map poly_type_args_map subst_iter in

    (*apply the substitutions to the literals*)
    let new_lits_iter = Array.fold_left (fun acc lit -> Iter.union acc (Iter.map (apply_subst_lit lit) subst_iter)) Iter.empty literals in
    let new_lits_arr = Iter.to_array new_lits_iter in

    (*returns the new_mono_map, new_poly_map and new_literals*)
    new_mono_map, new_poly_map, new_lits_arr 

(* takes a map from function symbols to sets (iter for now) of monomorphic type arguments
 * takes a map from clause_ids to a map from function symbols to sets (iter for now) of polymorphic type arguments
 * takes a list of clauses under the form of a (clause_id * literal array) (clause_ids are ints)
 * returns an updated monomorphic map, polymorphic map and list of updated clauses *)
let mono_step clause_list mono_map poly_clause_map =
    let process_clause acc (clause_id, literals) =
        let (acc_clauses, acc_mono_map, acc_poly_clause_map) = acc in
        (*assuming it doesn't fail because we previously add all clause ids to the poly_clause_map*)
        let poly_map = ClauseArgMap.find clause_id poly_clause_map in
        let (new_mono_map, new_poly_map, new_literals) = mono_step_clause mono_map poly_map literals in
        let res_mono_map = ArgMap.union (fun _ elem1 elem2 -> Some (Iter.union elem1 elem2)) acc_mono_map new_mono_map in
        let res_poly_map = ArgMap.union (fun _ elem1 elem2 -> Some (Iter.union elem1 elem2)) poly_map new_poly_map in
        let res_poly_clause_map = ClauseArgMap.add clause_id res_poly_map acc_poly_clause_map in
        ((clause_id, new_literals)::acc_clauses, res_mono_map, res_poly_clause_map)
    in
    List.fold_left process_clause ([], mono_map, poly_clause_map) clause_list

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

(* takes a list of (clause_id, literal array) pairs
 * takes an integer to limit the numbers of iterations
 * returns an updated list of clauses *)
let monomorphise_problem clause_list loop_count =
    (* will initialise the maps with the function symbol -> type arguments bindings derived from the clauses *)
    let map_initialisation_step (mono_map, clause_poly_map) (clause_id, literals) =
        let clause_terms_iter = terms_iter literals in

        (*InnerTerm.show_type_arguments := true;
        (Iter.iter (fun term -> (Printf.printf "\n term: %s" (T.to_string term) )) clause_terms_iter);
        InnerTerm.show_type_arguments := false;*)

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
                            (fun _ elem1 elem2 -> Some (Iter.union elem1 elem2))
                            new_poly_map other_poly_map)
                        clause_poly_map
        in
        let all_ty_syms = Iter.flat_map typed_sym clause_terms_iter in
        (assert (Iter.for_all (fun (fun_sym, _) -> ArgMap.find_opt fun_sym new_mono_map != None) all_ty_syms));
        (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key new_mono_map != None) poly_map ) new_clause_poly_map));

        new_mono_map, new_clause_poly_map
    in

    (* create initial maps *)
    let init_mono_map, init_clause_poly_map =
        List.fold_left map_initialisation_step (ArgMap.empty, ClauseArgMap.empty) clause_list in

    (* another check due to a find*)
    (assert (List.for_all (fun (clause_id, _) -> ClauseArgMap.find_opt clause_id init_clause_poly_map != None) clause_list));
    (assert (ClauseArgMap.for_all (fun _ poly_map -> ArgMap.for_all (fun key _ -> ArgMap.find_opt key init_mono_map != None) poly_map ) init_clause_poly_map));

    (* monomorphisation loop *)
    let rec monomorphisation_loop curr_count mono_map poly_clause_map clause_list =
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

    clause_list_res 
    

(*

let add_term_sym typed_sym_map term =
    let typed_sym = typed_sym term in
    let update_map map (sym, ty_args) =
        let new_args = 
            match ArgMap.find_opt sym map with
                | Some (mono_ty_args, non_mono_ty_args) ->
                    if List.for_all Ty.is_ground ty_args then
                        let new_mono = Iter.cons ty_args mono_ty_args in
                        new_mono, non_mono_ty_args
                    else
                        let new_non_mono = Iter.cons ty_args non_mono_ty_args in
                        mono_ty_args, new_non_mono
                | None ->
                    if List.for_all Ty.is_ground ty_args then
                        Iter.singleton ty_args, Iter.empty
                    else
                        Iter.empty, Iter.singleton ty_args
        in
        ArgMap.add sym new_args map 
    in
    Iter.fold update_map typed_sym_map typed_sym
                
let map_typed_sym map term_iter =
    Iter.fold add_term_sym map term_iter


let new_type_args_single non_mono_ty_list mono_ty_list =
    let combine_types subst_iter mono_ty non_mono_ty =
        let new_subst = match_type non_mono_ty mono_ty in
        Iter.cons new_subst subst_iter 
    in
    
    let new_subst = List.fold_left2 combine_types Iter.empty mono_ty_list non_mono_ty_list in
    let new_ty_arg ty_list subst =
        List.map (apply_ty_subst subst) ty_list
    in
    let new_types = Iter.map (new_ty_arg non_mono_ty_list) new_subst in
    let new_mono_ty_args = Iter.filter (List.for_all Ty.is_ground) new_types in
    let new_non_mono_ty_args = Iter.filter (List.for_all (fun ty -> not (Ty.is_ground ty))) new_types in
    new_subst, new_mono_ty_args, new_non_mono_ty_args


let new_type_args mono_ty_args non_mono_ty_list =
    let new_type_args_iter acc mono_ty_list =
        let new_subst, new_mono_ty_args, new_non_mono_ty_args = new_type_args_single non_mono_ty_list mono_ty_list in
        let subst_iter, mono_ty_args, non_mono_ty_args = acc in
        Iter.union new_subst subst_iter, Iter.union mono_ty_args new_mono_ty_args, Iter.union non_mono_ty_args new_non_mono_ty_args
    in
    Iter.fold new_type_args_iter (Iter.empty, Iter.empty, Iter.empty) mono_ty_args

let mono_update_sym (mono_ty_args, non_mono_ty_args) =
    let update_iter acc non_mono_ty_list =
        let new_subst, new_mono_ty_args, new_non_mono_ty_args = new_type_args mono_ty_args non_mono_ty_list in
        let subst_iter, mono_ty_args, non_mono_ty_args = acc in
        Iter.union new_subst subst_iter, Iter.union mono_ty_args new_mono_ty_args, Iter.union non_mono_ty_args new_non_mono_ty_args
    in
    Iter.fold update_iter (Iter.empty, Iter.empty, Iter.empty) non_mono_ty_args


let mono_update_step (map, subst_iter) =
    let update_map sym (mono_ty_args, non_mono_ty_args) (map, subst_iter) =
        let new_subst, new_mono_ty_args, new_non_mono_ty_args = mono_update_sym (mono_ty_args, non_mono_ty_args) in
        ArgMap.add sym (Iter.union mono_ty_args new_mono_ty_args, Iter.union non_mono_ty_args new_non_mono_ty_args) map, Iter.union subst_iter new_subst
    in
    let new_subst, new_map = ArgMap.fold update_map map (ArgMap.empty, Iter.empty) in
    new_subst, new_map

let monomorphise_clause count literals =
    let terms_iter = Array.fold_left (fun acc lit -> Iter.union acc (Literal.Seq.terms lit)) Iter.empty literals in
    let init_map = map_typed_sym ArgMap.empty terms_iter in
    let rec iter_update counter subst_iter map =
        if counter <= 0 then subst_iter, map
        else 
            let new_map, new_subst_iter = mono_update_step (map, subst_iter) in
            iter_update (counter-1) new_subst_iter new_map
    in
    let subst_iter, map = iter_update count Iter.empty init_map in
    let apply_subst_lit lit subst =
        Literal.apply_subst Subst.Renaming.none subst (lit, 0)
    in
    let new_lits_iter_arr = Array.map (fun lit -> Iter.map (apply_subst_lit lit) subst_iter) literals in
    let new_lits_iter = Array.fold_left Iter.union Iter.empty new_lits_iter_arr in
    new_lits_iter


    


let all_typed_sym term_set = 
    let all_sym = TermSet.fold (fun term iter -> Iter.union (typed_sym term) iter) term_set Iter.empty in
    all_sym

let derive_subst mono_term term =
    let mono_ty_symbols = Iter.empty in
    (*(Printf.printf "\n %i monomorphic typed symbols\n" (Iter.filter_count (fun _ -> true) mono_ty_symbols) );*)
    (*let ty_symbols = typed_sym term in*)
    let ty_symbols = Iter.empty in
    (*(Printf.printf "\n %i non-monomorphic typed symbols\n" (Iter.filter_count (fun _ -> true) ty_symbols) );*)
    (* TODO handle exceptions *)
    (*let symbol_subst mono_symbols fun_symbol fun_ty =
        let same_mono_symbols = Iter.filter_map (fun (sym, mono_type) -> if sym == fun_symbol then Some(mono_type) else None) mono_symbols in
        Iter.fold (fun subst mono_type -> Subst.merge (match_type mono_type fun_ty) subst) Subst.empty same_mono_symbols
    in
    let res = Iter.fold (fun subst (fun_sym, fun_type) -> Subst.merge (symbol_subst mono_ty_symbols fun_sym fun_type) subst) Subst.empty ty_symbols in
    res*)
    let single_sym_subst (fun_sym, fun_ty) =
        let same_symbol_mono_types = Iter.filter_map (fun (sym, mono_type) -> if sym == fun_sym then Some(mono_type) else None) mono_ty_symbols in
        let res_subst_iter = Iter.map (match_type fun_ty) same_symbol_mono_types in
        res_subst_iter
    in
    let all_subst = Iter.flat_map single_sym_subst ty_symbols in
    all_subst


let candidate_mono_term term_syms mono_term =
    let mono_term_syms = Iter.map fst (typed_sym mono_term) in
    let common_syms = Iter.inter term_syms mono_term_syms in
    not (Iter.is_empty common_syms)

let new_terms_single mono_term_set term =
    let derive_new_term mono_term term =
        let subst_iter = derive_subst mono_term term in
        let apply_subst term subst = Term.of_term_unsafe (Subst.apply Subst.Renaming.none subst ((term: Term.t :> InnerTerm.t), 0)) in
        let new_terms_iter = Iter.filter_map (fun subst -> try Some(apply_subst term subst) with _ -> None) subst_iter in
        Iter.to_set (module TermSet) new_terms_iter
    in
    let term_syms = Iter.map fst (typed_sym term) in
    let candidate_mono_terms = TermSet.filter (candidate_mono_term term_syms) mono_term_set in
    let res = TermSet.fold (fun mono_term term_set -> TermSet.union (derive_new_term mono_term term) term_set) TermSet.empty candidate_mono_terms in
    (*(Printf.printf "\n %i new terms from %i mono terms \n" (TermSet.cardinal res) (TermSet.cardinal mono_term_set));*)
    (*InnerTerm.show_type_arguments := true;
    (Printf.printf "\n old term: %s " (Term.to_string term));
    (TermSet.iter (fun t -> (Printf.printf "\n new term: %s " (Term.to_string t))) res);
    InnerTerm.show_type_arguments := false;*)
    res
    

let new_substs_single mono_term_set term =
    Iter.flat_map (fun mono_term -> derive_subst mono_term term) (Iter.of_set (module TermSet) mono_term_set)

let new_substs mono_term_set term_set =
    Iter.flat_map (new_substs_single mono_term_set) term_set

let apply_subst term subst =
    Term.of_term_unsafe (Subst.apply Subst.Renaming.none subst ((term: Term.t :> InnerTerm.t), 0))

let new_terms mono_terms terms =
    (*(Printf.printf "\n we have %i mono terms\n" (TermSet.cardinal mono_terms));
    (Printf.printf "\n we have %i non-mono terms\n" (TermSet.cardinal terms));*)
    let res = TermSet.fold (fun term term_set -> TermSet.union term_set (new_terms_single mono_terms term)) terms TermSet.empty in
    (*InnerTerm.show_type_arguments := true;
    (TermSet.iter (fun t -> (Printf.printf "\n new term: %s " (Term.to_string t))) res);
    InnerTerm.show_type_arguments := false;*)
    res

let is_monomorphic term = 
    let res = (List.length (Ty.vars (T.ty term))) == 0 in
    (*(Printf.printf "\n type: %s is mono? %b" (Ty.TPTP.to_string (T.ty term)) res);*)
    res

let split_terms term_set =
    let mono_terms = TermSet.filter is_monomorphic term_set in
    let non_mono_terms = TermSet.filter (fun t -> not (is_monomorphic t)) term_set in
    mono_terms, non_mono_terms

let mono_step mono_terms non_mono_terms =
    let new_terms = new_terms mono_terms non_mono_terms in
    let new_mono_terms, new_non_mono_terms = split_terms new_terms in
    TermSet.union mono_terms new_mono_terms, TermSet.union non_mono_terms new_non_mono_terms


let monomorphised_terms term_set count =
    let mono_terms, non_mono_terms = split_terms term_set in
    (*(Printf.printf "\nbeginning with %i monomorphic terms\n" (TermSet.cardinal mono_terms) );
    (Printf.printf "beginning with %i non-monomorphic terms\n" (TermSet.cardinal non_mono_terms) );*)
    let rec mono_step_limited counter mono_terms non_mono_terms =
        if counter <= 0 then
            mono_terms, non_mono_terms
        else
            let new_mono, new_non_mono = mono_step mono_terms non_mono_terms in
            (*(Printf.printf "\n%i total monomorphic terms\n" (TermSet.cardinal new_mono) );
            (Printf.printf "%i total non-monomorphic terms\n" (TermSet.cardinal new_non_mono) );*)
            mono_step_limited (counter - 1) new_mono new_non_mono
    in 
    let mono_terms_res, _ = mono_step_limited count mono_terms non_mono_terms in
    (Printf.printf "ending up with %i monomorphic terms\n" (TermSet.cardinal mono_terms_res));
    mono_terms_res

let monomorphised_terms_set terms_iter count =
    let term_set = Iter.to_set (module TermSet) terms_iter in
    monomorphised_terms term_set count

let derive_lits left_term_set right_term_set bool =
    let derive_lits_single left_term right_term_set =
        let right_term_list = TermSet.to_list right_term_set in
        List.map (fun right_term -> Literal.mk_lit left_term right_term bool) right_term_list
    in
    TermSet.fold (fun left_term lit_list -> (derive_lits_single left_term right_term_set)@lit_list) left_term_set []
    

let monomorphise_lit lit mono_term_set =
    match lit with
        | Literal.Equation (left_term, right_term, bool) ->
            (*let left_term_set = new_terms_single mono_term_set left_term in
            let left_term_set_mono, _ = split_terms left_term_set in
            let right_term_set = new_terms_single mono_term_set right_term in
            let right_term_set_mono, _ = split_terms right_term_set in
            derive_lits left_term_set_mono right_term_set_mono bool*)
            let left_subst = new_substs_single mono_term_set left_term in
            let right_subst = new_substs_single mono_term_set right_term in
            let new_term_pairs = Iter.map (fun s -> (apply_subst left_term s), (apply_subst right_term s)) (Iter.union left_subst right_subst) in
            let new_mono_term_pairs = Iter.filter (fun (lt, rt) -> is_monomorphic lt && is_monomorphic rt) new_term_pairs in
            let new_lits = Iter.map (fun (lt, rt) -> Literal.mk_lit lt rt bool) new_mono_term_pairs in
            Iter.to_list new_lits
        | _ -> [lit]

let monomorphise_clause_old literals mono_term_set =
    (*let terms_iter = Literals.Seq.terms literals in*)
    (*let term_set = Iter.to_set (module TermSet) terms_iter in
    let mono_term_set = monomorphised_terms term_set 5 in*)
    let monomorphise_lits literals = Array.fold_left (fun lit_list lit -> (monomorphise_lit lit mono_term_set)@lit_list) [] literals in
    let res = monomorphise_lits literals in
    res*)
