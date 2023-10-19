
module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm 
module Subst = Subst
module Sc = Scoped

module TermSet = T.Set
module TypeSet = Ty.Set
(*make a map that takes a type variable and returns a set of types*)

(* TODO make a neat little module with an ergonomic interface *)


let match_type mono_type ty =
    let subst = Unif.Ty.matching ~pattern:(mono_type, 0) (ty, 1) in
    subst


let typed_sym term = T.Seq.typed_symbols term

let all_typed_sym term_set = 
    let all_sym = TermSet.fold (fun term iter -> Iter.union (typed_sym term) iter) term_set Iter.empty in
    all_sym

let derive_subst mono_term term =
    let mono_ty_symbols = typed_sym mono_term in
    let ty_symbols = typed_sym term in
    (* TODO handle exceptions *)
    let symbol_subst mono_symbols fun_symbol fun_ty =
        let same_mono_symbols = Iter.filter_map (fun (sym, mono_type) -> if sym == fun_symbol then Some(mono_type) else None) mono_symbols in
        Iter.fold (fun subst mono_type -> Subst.merge (match_type mono_type fun_ty) subst) Subst.empty same_mono_symbols
    in
    Iter.fold (fun subst (fun_sym, fun_type) -> Subst.merge (symbol_subst mono_ty_symbols fun_sym fun_type) subst) Subst.empty ty_symbols

let new_terms_single mono_term_set term =
    (* TODO make sure using Subst.FO isn't a mistake *)
    TermSet.map (fun mono_term -> Subst.FO.apply Subst.Renaming.none (derive_subst mono_term term) (term, 0)) mono_term_set

let new_terms mono_terms terms =
    TermSet.fold (fun term term_set -> TermSet.union term_set (new_terms_single mono_terms term)) TermSet.empty terms

let is_monomorphic term = T.monomorphic term

let split_terms term_set =
    let mono_terms = TermSet.filter Term.monomorphic term_set in
    let non_mono_terms = TermSet.filter (fun t -> not (Term.monomorphic t)) term_set in
    mono_terms, non_mono_terms

let mono_step mono_terms non_mono_terms =
    let new_terms = new_terms mono_terms non_mono_terms in
    let new_mono_terms, new_non_mono_terms = split_terms new_terms in
    TermSet.union mono_terms new_mono_terms, TermSet.union non_mono_terms new_non_mono_terms


let monomorphised_terms term_set =
    let mono_terms, non_mono_terms = split_terms term_set in
    let rec mono_step_limited counter mono_terms non_mono_terms =
        if counter <= 0 then
            mono_terms, non_mono_terms
        else
            let new_mono, new_non_mono = mono_step mono_terms non_mono_terms in
            mono_step_limited (counter - 1) new_mono new_non_mono
    in 
    let mono_terms_res, _ = mono_step_limited 5 mono_terms non_mono_terms in
    mono_terms_res

let derive_lits left_term_set right_term_set bool =
    let derive_lits_single left_term right_term_set =
        let right_term_list = TermSet.to_list right_term_set in
        List.map (fun right_term -> Literal.mk_lit left_term right_term bool) right_term_list
    in
    TermSet.fold (fun left_term lit_list -> (derive_lits_single left_term right_term_set)@lit_list) left_term_set []
    

let monomorphise_lit lit mono_term_set =
    let open Literal in
    match lit with
        | Equation (left_term, right_term, bool) ->
            let left_term_set = new_terms_single mono_term_set left_term in
            let left_term_set_mono, _ = split_terms left_term_set in
            let right_term_set = new_terms_single mono_term_set right_term in
            let right_term_set_mono, _ = split_terms right_term_set in
            derive_lits left_term_set_mono right_term_set_mono bool
        | _ -> [lit]

let monomorphise_clause literals =
    let terms_iter = Literals.Seq.terms literals in
    let term_set = Iter.to_set (module TermSet) terms_iter in
    let mono_term_set = monomorphised_terms term_set in
    let monomorphise_lits literals = Array.fold_left (fun lit_list lit -> (monomorphise_lit lit mono_term_set)@lit_list) [] literals in
    let res = monomorphise_lits literals in
    (Printf.printf "beginning with %i literals\n" (Array.length literals));
    (Printf.printf "ending up with %i literals\n" (List.length res));
    (Printf.printf "-------\n");
    res
