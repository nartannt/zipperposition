(* This file is free software, part of Zipperposition. See file "license" for more details. *)

open Logtk

module type S = sig
  val sk_ctx : unit -> Skolem.ctx

  val ord : unit -> Ordering.t
  (** current ordering on terms *)

  val selection_fun : unit -> Selection.t
  (** selection function for clauses *)

  val set_selection_fun : Selection.t -> unit
  val set_ord : Ordering.t -> unit

  val signature : unit -> Signature.t
  (** Current signature *)

  val renaming : Subst.Renaming.t

  (** {2 Utils} *)

  val compare : Term.t -> Term.t -> Comparison.t
  (** Compare two terms *)

  val select : Selection.t
  val bool_select : Bool_selection.t

  val lost_completeness : unit -> unit
  (** To be called when completeness is not preserved *)

  val is_completeness_preserved : unit -> bool
  (** Check whether completeness was preserved so far *)

  val add_signature : Signature.t -> unit
  (** Merge  the given signature with the context's one *)

  val find_signature : ID.t -> Type.t option
  (** Find the type of the given symbol *)

  val find_signature_exn : ID.t -> Type.t
  (** Unsafe version of {!find_signature}.
      @raise Not_found for unknown symbols *)

  val declare : ID.t -> Type.t -> unit
  (** Declare the type of a symbol (updates signature) *)

  val declare_syms : (ID.t * Type.t) list -> unit
  (** Declare multiple symbols (more efficient that calling
      declare function incrementally) *)

  val on_new_symbol : (ID.t * Type.t) Signal.t
  val on_signature_update : Signature.t Signal.t
  val set_injective_for_arg : ID.t -> int -> unit
  val is_injective_for_arg : ID.t -> int -> bool

  (** {2 Literals} *)

  module Lit : sig
    val from_hooks : unit -> Literal.Conv.hook_from list
    val add_from_hook : Literal.Conv.hook_from -> unit
    val to_hooks : unit -> Literal.Conv.hook_to list
    val add_to_hook : Literal.Conv.hook_to -> unit

    val of_form : Term.t SLiteral.t -> Literal.t
    (** @raise Invalid_argument if the formula is not atomic *)

    val to_form : Literal.t -> Term.t SLiteral.t
  end
end
