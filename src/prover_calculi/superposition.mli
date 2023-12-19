(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Inference and simplification rules for the superposition calculus} *)

open Logtk
open Libzipperposition

(** {2 Inference rules} *)

val section : Util.Section.t

module type S = Superposition_intf.S

val key : (module S) Flex_state.key
(** key to access the {!Env.flex_state}. After registration (after
    calling [register]), the Env's state contains
    a mapping from "superposition" to the packed module. *)

val k_unif_alg : (Term.t Scoped.t -> Term.t Scoped.t -> Unif_subst.t CCOpt.t OSeq.t) Flex_state.key
val k_ho_basic_rules : bool Flex_state.key
val get_unif_module : (module Env.S) -> (module UnifFramework.US)

val register : sup:(module S) -> unit
(** Register the superposition module to its Environment's
    mixtbl. Done automatically by the {!extension}. *)

module Make (Env : Env.S) : S with module Env = Env

(** {2 As Extension}
    Extension named "superposition" *)

val extension : Extensions.t
