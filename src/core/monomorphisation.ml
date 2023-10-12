
module T = Term
module Lit = Literal
module Ty = Type
module IT = InnerTerm 

module TermSet = IT.Set

(* TODO make a neat little module with an ergonomic interface *)

(*axilliary functions, here so I remember the names*)

(* given a set of terms, returns the set of function symbols such that all their type
 * variables are instantiated at least once in the problem*)
let instantiated_fun_sym term_set = []

(*instantiates type variable in term with given type*)
(*look into apply1 *)
let instantiate_ty_var ty_var new_ty term = ()

(*type variables of a term*)
let type_vars term = T.Seq.ty_vars

(*given a type, returns true iff it is monomorphic and false otherwise*)
(*don't understand what this does yet, copied off of raise PolymorphismDetected*)
let is_monomorphic_type ty = not (Ty.Seq.sub ty |> Iter.exists Ty.is_tType)

(*is term monomorhic*)
let is_monomorphic_term term = T.monomorphic term

(*types of term*)
let types_of_term term = T.ty_vars term

(*given a set of terms, returns all the types that appear in those terms*)
let types_of_terms terms = []


(* given sets of polymorphic and monomorphic terms,
 * computes the new terms generated in a single monomorphisation step*)
let new_terms mono_terms poly_terms = []


