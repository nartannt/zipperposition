
(*
Zipperposition: a functional superposition prover for prototyping
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

(** {1 Meta Prover for zipperposition} *)

open Logtk
open Logtk_meta

type result =
  | Deduced of PFormula.t * source list
  | Theory of string * HOTerm.t list * source list
  (** Feedback from the meta-prover *)

and source =
  | FromClause of Clause.t
  | FromForm of PFormula.t

type t

val create : unit -> t
  (** Fresh meta-prover *)

val has_new_patterns : t -> bool
  (** Are there some new patterns that should be lookud up for in
      the active set? *)

val scan_formula : t -> PFormula.t -> result list
  (** Scan a formula for patterns *)

val scan_clause : t -> Clause.t -> result list
  (** Scan a clause for patterns *)

val scan_set : t -> Clause.CSet.t -> result list
  (** Scan the set of clauses for patterns that are new. This should
      be called on the active set every time [has_new_patterns prover]
      returns true. After this, [has_new_patterns prover] returns false
      at least until the next call to [scan_clause]. *)

val proof_of_source : source -> Proof.t
  (** Extract the proof of a source *)

val explain : t -> Logtk_meta.Reasoner.fact -> Proof.t list
  (** Find why the given literal is true.
      @raise Invalid_argument if the literal is not true in Datalog
      @raise Not_found if the literal's premises are not explained by
        previous scan_clause/scan_formula *)

val theories : t -> (string * HOTerm.t list) Sequence.t
  (** List of theories detected so far *)

val results : t -> result Sequence.t
  (** All results *)

val reasoner : t -> Logtk_meta.Reasoner.t
  (** Datalog reasoner *)

val prover : t -> Logtk_meta.Prover.t
  (** meta-prover  *)

val parse_theory_file : t -> string -> unit Monad.Err.t
  (** Update KB with the content of this file *)

val pp_result : Buffer.t -> result -> unit
val pp_theory : Buffer.t -> (string * HOTerm.t list) -> unit