
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
    let subst = Unif.Ty.matching ~pattern:(mono_type, 0) (ty, 0) in
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
    let mono_terms = TermSet.filter is_monomorphic term_set in
    let non_mono_terms = TermSet.filter (fun t -> not (is_monomorphic t)) term_set in
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
            let right_term_set = new_terms_single mono_term_set right_term in
            derive_lits left_term_set right_term_set bool
        | _ -> [lit]

let monomorphise_clauses literals_arr =
    let terms_iter_arr = Array.map Literals.Seq.terms literals_arr in
    let terms_iter = Iter.of_array terms_iter_arr in
    let term_set = Iter.to_set (module TermSet) (Iter.flatten terms_iter) in
    let mono_term_set = monomorphised_terms term_set in
    let monomorphise_lits literals = Array.fold_left (fun lit_list lit -> (monomorphise_lit lit mono_term_set)@lit_list) [] literals in
    Array.map monomorphise_lits literals_arr

    


(*
(*axilliary functions, here so I remember the names*)

(*given a type, returns true iff it is monomorphic and false otherwise*)
(*don't understand what this does yet, copied off of raise PolymorphismDetected*)
let is_monomorphic_type ty = not (Ty.Seq.sub ty |> Iter.exists Ty.is_tType)

let all_typed_sym term_set = 
    let typed_sym term = T.Seq.typed_symbols term in
    let all_sym = TermSet.fold (fun term iter -> Iter.union (typed_sym term) iter) term_set Iter.empty in
    all_sym

(*returns all monomorphically instantiated function symbols and their type in the term as a pair (ID.t * Type) in a map*)
let mono_fun_sym term_set  = 
    let all_sym = all_typed_sym term_set in
    let mono_sym = Iter.filter (fun (_, ty) -> is_monomorphic_type ty) all_sym in
    mono_sym
    
(*exception InvalidUnif

let rec unify_mono mono_type ty =
    if not (is_monomorphic_type mono_type) then raise InvalidUnif;
    let combine sub_opt mono_ty ty =
        match (unify_mono mono_ty ty), sub_opt with
            | Some ty_unif, Some sub ->
                begin
                try
                    let res = Subst.merge ty_unif sub in
                    Some(res)
                with Subst.InconsistentBinding _ -> raise InvalidUnif
                end
            | _, _ -> None
    in
    match Ty.view mono_type, Ty.view ty with
    | Builtin b1, Builtin b2 when b1 == b2 -> Some (Subst.empty)
    | App (id_m, args_m), App (id, args) when id_m == id ->  
        List.fold_left2 combine (Some Subst.empty) args_m args
    | Fun (args_m, ret_m), Fun(args, ret) ->
        List.fold_left2 combine (Some Subst.empty) (ret_m::args_m) (ret::args) 
    (*we want to replace all DB indices by fresh variables*)
    (*we treat those as regular variables except that the substitutions are applied to the type 
     * before it is returned *)
    (* this allows us to avoid accidentally capturing DB variables accross different types of the term
     * whilst also returning a substitution that allows to capture variables quantified at the term level*)

    (*scope 0 for the term level*)
    | mono_ty, Var var ->
            Some(Subst.Ty.bind Subst.empty (Sc.make var 0) (Sc.make mono_ty 0))
    | _ -> None*)

let match_type mono_type ty =
    let subst = Unif.Ty.matching ~pattern:(mono_type, 0) (ty, 0) in
    subst
    (*Subst.Ty.apply Subst.Renaming.none subst (ty, 0)*)

let generate_subst mono_term term =
    let mono_fun_sym = [] in
    let fun_sym = [] in
    (*for each fun_sym, find all corresponding mono_fun_sym and derive a substitution*)
    (*combine all substitutions*)
    ()


(*given a term and a set of monomorphically instantiated function symbols, will return a set of substitutions
 * that (partially) monomorphise the term *)
let mono_sub mono_fun_symbols term =
    let all_sym = T.Seq.typed_symbols term in
    let non_mono_sym = Iter.filter (fun (_, ty) -> not (is_monomorphic_type ty)) all_sym in ()


(* given a term, returns the set of function symbols that occur in that term*)
let function_symbols term = T.symbols term

(* given a function symbol, will return true iff all its type variables
 * are instantiated at least once in the problem*)
let fun_sym_instantiated fun_sym problem_terms = []

(*instantiates type variable in term with given type*)
(*look into apply1 *)
let instantiate_ty_var ty_var new_ty term = ()

(*type variables of a term*)
let type_vars term = T.Seq.ty_vars


(*is term monomorhic*)
let is_monomorphic_term term = T.monomorphic term

(*types of term*)
let types_of_term term = T.ty_vars term

(*given a set of terms, returns all the types that appear in those terms*)
let types_of_terms terms = []


(* given sets of polymorphic and monomorphic terms,
 * computes the new terms generated in a single monomorphisation step*)
let new_terms mono_terms poly_terms = TermSet.empty

(* given a set of terms, returns two sets, the first has all the monomorphic terms
 * the second one has all the polymorphic terms *)
let separate_terms term_set =
    let monomorphic_terms = TermSet.filter is_monomorphic_term term_set in
    let polymorphic_terms = TermSet.filter (fun t -> not (is_monomorphic_term t)) term_set in
    monomorphic_terms, polymorphic_terms*)
