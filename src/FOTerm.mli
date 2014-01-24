(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 First-order terms}
Terms use ScopedTerm with kind "FOTerm".
*)

type symbol = Symbol.t

(** {2 Typed Constant}

A typed constant is a symbol with its type. It is also repreented
as a ScopedTerm.*)

module Cst : sig
  type t = private ScopedTerm.t

  val ty : t -> Type.t
  val sym : t -> Symbol.t

  val make : ty:Type.t -> symbol -> t

  val of_const : ScopedTerm.t -> t option
  val of_const_exn : ScopedTerm.t -> t
  val is_const : ScopedTerm.t -> bool

  include Interfaces.HASH with type t := t
  include Interfaces.ORD with type t := t
  include Interfaces.PRINT with type t := t

  module TPTP : sig
    val true_ : t
    val false_ : t
  end
end

(** {2 Term} *)

type t = private ScopedTerm.t

type term = t

type view = private
  | Var of int                (** Term variable *)
  | BVar of int               (** Bound variable (De Bruijn index) *)
  | App of Cst.t * Type.t list * t list (** Function application *)

type sourced_term =
  t * string * string           (** Term + file,name *)

val view : t -> view

(** {2 Comparison, equality, containers} *)

val subterm : sub:t -> t -> bool
  (** checks whether [sub] is a (non-strict) subterm of [t] *)

include Interfaces.HASH with type t := t
include Interfaces.ORD with type t := t

val ty : t -> Type.t                (** Obtain the type of a term.. *)

module Tbl : sig
  include Hashtbl.S with type key = t
  val to_list : unit t -> term list
  val from_list : term list -> unit t
  val to_seq : unit t -> term Sequence.t
  val from_seq : term Sequence.t -> unit t
  val add_list : unit t -> term list -> unit
  val add_seq : unit t -> term Sequence.t -> unit
end

module Set : Sequence.Set.S with type elt = t
module Map : Sequence.Map.S with type key = t

module TCache : Cache.S with type key = t
module T2Cache : Cache.S2 with type key1 = t and type key2 = t

(** {2 Constructors} *)

val var : ty:Type.t -> int -> t
  (** Create a variable. Providing a type is mandatory.
      The index must be non-negative,
      @raise Invalid_argument otherwise. *)

val bvar : ty:Type.t -> int -> t
  (** Create a bound variable. Providing a type is mandatory.
      {b Warning}: be careful and try not to use this function directly*)

val app : ?tyargs:Type.t list -> Cst.t -> t list -> t
  (** Apply a typed symbol to a list of type arguments (optional) and
      a list of term arguments. Partial application is not
      supported and will raise a type error. The type is automatically
      computed.
      @raise Type.Error if types do not match. *)

val const : ?tyargs:Type.t list -> Cst.t -> t
  (** Create a typed constant. Specialization of [app]. *)

val cast : ty:Type.t -> t -> t
  (** Change the type. Only works for variables and bound variables. *)

val of_term : ScopedTerm.t -> t option
val is_term : ScopedTerm.t -> bool

val is_var : t -> bool
val is_bvar : t -> bool
val is_app : t -> bool
val is_const : t -> bool

module TPTP : sig
  val true_ : t     (** tautology term *)
  val false_ : t    (** antilogy term *)

  include Interfaces.PRINT with type t := t
end

(** {2 Subterms and Positions} *)

module Pos : sig
  val at : t -> Position.t -> t
  (** retrieve subterm at pos
      @raise Invalid_argument if the position is invalid *)

  val replace_at : t -> Position.t -> by:t -> t
  (** [replace_at t pos ~by] replaces the subterm at position [pos]
      in [t] by the term [by]. The two terms should have the same type.
      @raise Invalid_argument if the position is not valid *)
end

val replace : t -> old:t -> by:t -> t
  (** [replace t ~old ~by] syntactically replaces all occurrences of [old]
      in [t] by the term [by]. *)

(** {2 Sequences} *)

module Seq : sig
  val vars : t -> t Sequence.t
  val subterms : t -> t Sequence.t
  val subterms_depth : t -> (t * int) Sequence.t  (* subterms with their depth *)
  val symbols : t -> Symbol.t Sequence.t
  val add_symbols : Symbol.Set.t -> t Sequence.t -> Symbol.Set.t
  val max_var : t Sequence.t -> int
  val min_var : t Sequence.t -> int
  val add_vars : Set.t -> t Sequence.t -> Set.t
  val ty_vars : t -> Type.t Sequence.t
  val add_ty_vars : Type.Set.t -> t Sequence.t -> Type.Set.t
end

val var_occurs : var:t -> t -> bool     (** [var_occurs ~var t] true iff [var] in t *)
val is_ground : t -> bool               (** is the term ground? (no free vars) *)
val monomorphic : t -> bool             (** true if the term contains no type var *)
val max_var : Set.t -> int              (** find the maximum variable index, or 0 *)
val min_var : Set.t -> int              (** minimum variable, or 0 if ground *)
val add_vars : unit Tbl.t -> t -> unit  (** add variables of the term to the set *)
val vars : t Sequence.t -> Set.t        (** compute variables of the terms *)
val vars_prefix_order : t -> t list     (** variables of the term in prefix traversal order *)
val depth : t -> int                    (** depth of the term *)
val head : t -> Symbol.t                (** head symbol (or Invalid_argument) *)
val size : t -> int                     (** Size (number of nodes) *)

val ty_vars : t -> Type.Set.t
  (** Set of free type variables *)

(** {2 High-level operations} *)

val symbols : ?init:Symbol.Set.t -> t -> Symbol.Set.t
  (** Symbols of the term (keys of signature) *)

val contains_symbol : Symbol.t -> t -> bool
  (** Does the term contain this given symbol? *)

(** {2 Fold} *)

(** High level fold-like combinators *)

val all_positions : ?vars:bool -> ?pos:Position.t ->
                    t -> 'a ->
                    ('a -> t -> Position.t -> 'a) -> 'a
  (** apply f to all non-variable positions in t, accumulating the
      results along.
      [vars] specifies whether variables are folded on (default true). *)

(** {2 Some AC-utils} *)

module type AC_SPEC = sig
  val is_ac : Symbol.t -> bool
  val is_comm : Symbol.t -> bool
end

module AC(A : AC_SPEC) : sig
  val flatten : Symbol.t -> t list -> t list
    (** [flatten_ac f l] flattens the list of terms [l] by deconstructing all its
        elements that have [f] as head symbol. For instance, if l=[1+2; 3+(4+5)]
        with f="+", this will return [1;2;3;4;5], perhaps in a different order *)

  val normal_form : t -> t
    (** normal form of the term modulo AC *)

  val eq : t -> t -> bool
    (** Check whether the two terms are AC-equal. Optional arguments specify
        which symbols are AC or commutative (by default by looking at
        attr_ac and attr_commut). *)

  val symbols : t Sequence.t -> Symbol.Set.t
    (** Set of symbols occurring in the terms, that are AC *)
end

(** {2 Printing/parsing} *)

type print_hook = (Buffer.t -> t -> unit) -> Buffer.t -> t -> bool
  (** User-provided hook that can be used to print terms (the {!Node} case)
      before the default printing occurs.
      A hook takes as first argument the recursive printing function
      that it can use to print subterms.
      A hook should return [true] if it fired, [false] to fall back
      on the default printing. *)

val pp_depth : ?hooks:print_hook list -> int -> Buffer.t -> t -> unit
val pp_tstp_depth : int -> Buffer.t -> t -> unit

val pp_debug : Buffer.t -> t -> unit
val pp_tstp : Buffer.t -> t -> unit

val arith_hook : print_hook           (* hook to print arithmetic expressions *)
val pp_arith : Buffer.t -> t -> unit  (* use arith_hook with pp_debug *)

include Interfaces.PRINT with type t := t
include Interfaces.PRINT_OVERLOAD with type t := t

val print_var_types : bool ref
  (** If true, {!pp_debug} will print types of all vars, except those of type $i *)

val print_all_types : bool ref
  (** If true, {!pp_debug} will print the types of all annotated terms *)

include Interfaces.SERIALIZABLE with type t := t

val debug : Format.formatter -> t -> unit
  (** debug printing, with sorts *)

(** {2 Misc} *)

val __var : ty:Type.t -> int -> t
  (** create vars even with negative indices. Caution. *)
