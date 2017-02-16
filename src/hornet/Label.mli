
(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Label for Horn Clauses} *)

open Libzipperposition
open Hornet_types

type t = Hornet_types.label
(** Set of labelled clauses. Invariant: sorted *)

val return : labelled_clause -> t

val make : labelled_clause list -> t

val all_empty : t -> bool
(** All labelled clauses have empty labels. See {!Labelled_clause.is_empty} *)

val is_absurd : t -> bool
(** Some labelled clause has unsatisfiable constraints *)

val apply_subst :
  renaming:Subst.Renaming.t ->
  Subst.t ->
  t Scoped.t ->
  t

val variant :
  ?subst:Subst.t ->
  t Scoped.t ->
  t Scoped.t ->
  Subst.t Sequence.t

val merge : t -> t -> t

val to_list : t -> labelled_clause list
val to_seq: t -> labelled_clause Sequence.t

include Interfaces.PRINT with type t := t
