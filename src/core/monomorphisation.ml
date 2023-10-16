
module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm 
module Subst = Subst

module TermSet = T.Set
module TypeSet = Ty.Set
(*make a map that takes a type variable and returns a set of types*)

(* TODO make a neat little module with an ergonomic interface *)

(* TODO gather all monomorphic instantiations of functions in a given set of terms*)

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
    
exception InvalidUnif

let rec unify_mono mono_type ty =
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
    | _ -> None
    
    
let mono_sub_fun mono_fun_symbols fun_sym fun_ty =
    (*keeps all monomorphic instations of functions that have fun_sym as symbol*)
    let mono_template_candidate = Iter.filter_map (fun (fun_id, ty) -> if fun_id == fun_sym then Some ty else None) mono_fun_symbols in
    (*unifies when possible the types of the non-monomorphic fun_ty and the monomorphic type in mono_template_candidate*)
    ()



(*given a term and a set of monomorphically instantiated function symbols, will return a set of substitutions
 * that (partially) monomorphise the term *)
let mono_sub mono_fun_symbols term =
    let all_sym = T.Seq.typed_symbols term in
    let non_mono_sym = Iter.filter (fun (_, ty) -> not (is_monomorphic_type ty)) all_sym in ()

    

(* given a monomorphic function and a term, computes the term obtained by the substitutions induced
 * by the monomorphic function*)
let new_term mono_fun term = term


(* given two lists of type arguments the second one being monomorphic, returns a substition
 * (if it exists) unifying both lists*)
let unify_mono type_args mono_types_args = Some([])

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
    monomorphic_terms, polymorphic_terms
