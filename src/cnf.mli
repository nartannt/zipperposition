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

(** {1 Reduction to CNF and simplifications} *)

(** See "computing small normal forms", in the handbook of automated reasoning.
    All transformations are made on curried terms and formulas. *)

val is_cnf : FOFormula.t -> bool
  (** Is the formula in CNF? *)

val is_lit : FOFormula.t -> bool
  (** Literal? *)

val is_clause : FOFormula.t list -> bool
  (** Is it a clause, ie a list of literals? *)

val miniscope : FOFormula.t -> FOFormula.t
  (** Apply miniscoping transformation to the term *)

type clause = FOFormula.t list
  (** Basic clause representation, as list of literals *)

val cnf_of : ?ctx:Skolem.ctx -> FOFormula.t -> clause list
  (** Transform the clause into proper CNF; returns a list of clauses *)

val cnf_of_list : ?ctx:Skolem.ctx -> FOFormula.t list -> clause list
