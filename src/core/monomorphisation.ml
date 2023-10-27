
module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm 
module Subst = Subst
module Sc = Scoped

module TermSet = T.Set
module TypeSet = Ty.Set

module ArgMap = Map.Make(ID)

(* TODO make a neat little module with an ergonomic interface *)


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


let is_instantiated ty =
    Ty.expected_ty_vars ty == 0  && not (Type.Seq.sub ty |> Iter.exists Type.is_tType)


(* TODO currrent implementation is incorrect because the symbols are taken from the terms as constants
 * therefore, the associated types are that of the constant and are never instantiated *)
let typed_sym term = 
    (*get all applications*)
    let all_apps = Iter.filter T.is_app (T.Seq.subterms term) in
    (*get all the function symbols and types at the application level*)
    let get_typed_sym app_term =
        let hd_term = T.head_term_mono app_term in
        (*let ty_args, f = T.as_fun app_term in*)
        let ty_args, f = T.open_fun hd_term in
        let ty = T.ty hd_term in
        match T.as_const f with
            | Some(id) when is_instantiated ty -> Some(ty_args, id, ty)
            | _ -> None
    in
    let res = Iter.filter_map get_typed_sym all_apps in

    (*let res = Iter.sort_uniq (T.Seq.typed_symbols term) in*)
    InnerTerm.show_type_arguments := true;
    (Iter.iter (fun (ty_args, s, t) -> (Printf.printf "\n symbol %s, type: %s, ty_args: %s" (ID.name s) (Ty.to_string t) (String.concat "; " (List.map Ty.to_string ty_args)) )) res);
    InnerTerm.show_type_arguments := false;
    Iter.map (fun (ty_args, s, _) -> s, ty_args) res

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
    List.fold_left2 combine_types Iter.empty mono_ty_list non_mono_ty_list

let new_type_args mono_ty_args non_mono_ty_list =
    Iter.flat_map (new_type_args_single non_mono_ty_list) mono_ty_args

(* TODO make this more efficient by both generating the substitutions and the new types in the same pass*)
(* TODO find more efficient data structures for this process, iter are easy to manipulate but sets would
 * be more appropriate *)
let mono_update_sym (mono_ty_args, non_mono_ty_args) =
    Iter.flat_map (new_type_args mono_ty_args) non_mono_ty_args

(*let mono_update_step map =
    let new_subst = Map.fold (fun _ (mono_ty_args, non_mono_ty_args) subst_iter -> Iter.union*)


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

let monomorphise_clause literals mono_term_set =
    (*let terms_iter = Literals.Seq.terms literals in*)
    (*let term_set = Iter.to_set (module TermSet) terms_iter in
    let mono_term_set = monomorphised_terms term_set 5 in*)
    let monomorphise_lits literals = Array.fold_left (fun lit_list lit -> (monomorphise_lit lit mono_term_set)@lit_list) [] literals in
    let res = monomorphise_lits literals in
    res
