/*
Zipperposition: a functional superposition prover for prototyping
Copyright (C) 2012 Simon Cruanes

This file is part of the first order theorem prover Darwin
Copyright (C) 2006  The University of Iowa

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/


%{
  (** TSTP parser. It parses into Simple.term and Simple.formula *)

  open Const
  open Symbols
  open Types

  module Utils = FoUtils

  type term = Simple.term
  type variable = Simple.term
  type literal = Simple.formula
  type clause = Simple.formula

  (* includes from input *)
  let include_files: string list ref =
    ref []

  (* these are only valid for the current clause
     and have to be invalidated with init_clause for every new clause *)

  (* the variable id counter for the currently read term/clause *)
  let var_id_counter = ref 0
      
  (* mapping of the variable names (e.g. "X") of the currently read term/clause
     to variables. *)
  let (var_map: (string * sort * variable) list ref) =
    ref []

  (** is the current clause a conjecture? *)
  let conjecture = ref false

  (* reset everything in order to parse a new term/clause *)
  let init_clause () =
    var_id_counter := 0;
    var_map := [];
    conjecture := false
        
  (* gets the variables associated with a string from the variable mapping
     creates a new mapping for a new variable with the given sort *)
  let get_var ?(sort=univ_sort) (var_name: string) =
    try 
      (* way faster than List.assoc *)
      match (
        List.find
          (fun (var_name', var_sort, _) ->
             var_name = var_name' && var_sort == sort
          )
          !var_map
      ) with (_, _, t) -> t
    with
      | Not_found ->
          let new_var = 
            Simple.mk_var !var_id_counter sort
          in
            incr var_id_counter;
            var_map := (var_name, sort, new_var) :: !var_map;
            new_var

  (** table that maps symbols into sorts *)
  let sort_table = SHashtbl.create 5

  (* get the infered sort for the given constant *)
  let get_sort constant =
    try
      SHashtbl.find sort_table constant
    with Not_found -> univ_sort

  let set_sort constant sort = SHashtbl.replace sort_table constant sort
%}
  
%token LEFT_PARENTHESIS
%token RIGHT_PARENTHESIS
%token LEFT_BRACKET
%token RIGHT_BRACKET
%token DOT
%token NEGATION
%token COLON
%token COMMA
%token EQUALITY
%token DISEQUALITY
%token EOI
%token FOF
%token CNF
%token THF
%token INCLUDE
%token <string> SINGLE_QUOTED
%token <string> DOLLAR_WORD
%token <string> DOLLAR_DOLLAR_WORD
%token <string> DISTINCT_OBJECT
%token <string> LOWER_WORD
%token <string> UPPER_WORD
%token <string> UNSIGNED_INTEGER
%token <string> SIGNED_INTEGER
%token <string> REAL
%token DOLLAR_TRUE
%token DOLLAR_FALSE
%token DOLLAR
%token AND
%token OR
%token FORALL
%token EXISTS
%token BIJECTION
%token XOR
%token LEFT_IMPLICATION
%token RIGHT_IMPLICATION
%token UNKNOWN

%token IS
%token THEORY
%token LEMMA
%token IF
%token AND

%start parse_file
%type <Simple.sourced_formula list * string list> parse_file

%start parse_clause
%type <Simple.formula> parse_clause

%start parse_theory_file
%type <Theories.disjunction list> parse_theory_file

%%

/* start rules */

parse_file:
  | file EOI 
      {
        let clauses = $1 in
        let includes = !include_files in

        (* reset for next parser run *)
        include_files := [];
        Const.reset ();
        
        clauses, includes
      }

  | EOI
      { Const.parse_error "empty problem specification" }

parse_clause:
  | fof_formula EOI { Const.reset(); $1 }
  | EOI { Const.parse_error "could no parse clause" }

parse_theory_file:
  | theory_disjunctions EOI { Const.reset (); $1 }
  | EOI { Const.reset(); [] }

/* parse rules */

file:
  | tptp_input
      { match $1 with
        | Some clause -> [clause]
        | None        -> []
      }

  | tptp_input file
      { match $1 with
        | Some clause -> clause :: $2
        | None        -> $2
      }

tptp_input:
  | annotated_formula
      { Some $1 }

  | include_
      { None }



annotated_formula:
  | fof_annotated
      { $1 }

  | cnf_annotated
      { $1 }

  | thf_annotated
      { $1 }

thf_annotated:
  | THF LEFT_PARENTHESIS name COMMA formula_role COMMA
    fof_formula annotations RIGHT_PARENTHESIS DOT
    { failwith "Parser_tptp: tfh syntax not supported." }

fof_annotated:
  | FOF LEFT_PARENTHESIS name COMMA formula_role COMMA
    fof_formula annotations RIGHT_PARENTHESIS DOT
    { 
      let clause = 
        let filename = !Const.cur_filename in  (* ugly *)
        let source = Simple.Axiom (filename, $3) in
        if !conjecture
          then Simple.mk_not $7, source
          else $7, source
      in
      init_clause ();  (* reset global state *)
      clause
    }

fof_formula:
  | binary_formula
    { $1 }
  | unitary_formula
    { $1 }


binary_formula:
  | nonassoc_binary
    { $1 }

  | assoc_binary
    { $1 }

nonassoc_binary:
  | unitary_formula binary_connective unitary_formula
    { $2 $1 $3 }

binary_connective:
  | BIJECTION
    { Simple.mk_equiv }
  | LEFT_IMPLICATION
    { Simple.mk_imply }
  | RIGHT_IMPLICATION
    { fun x y -> Simple.mk_imply y x }
  | XOR
    { Simple.mk_xor }
  | NEGATION OR
    { fun x y -> Simple.mk_not (Simple.mk_or [x; y]) }
  | NEGATION AND
    { fun x y -> Simple.mk_not (Simple.mk_and [x; y]) }

assoc_binary:
  | or_formula
    { $1 }
  | and_formula
    { $1 }

or_formula:
  | unitary_formula OR more_or_formula
    { Simple.mk_or ($1 :: $3) }

more_or_formula:
  | unitary_formula
    { [$1] }
  | unitary_formula OR more_or_formula
    { $1 :: $3 }

and_formula:
  | unitary_formula AND more_and_formula
    { Simple.mk_and ($1 :: $3) }

more_and_formula:
  | unitary_formula
    { [$1] }
  | unitary_formula AND more_and_formula
    { $1 :: $3 }

unitary_formula:
  | quantified_formula
    { $1 }
  | unary_formula
    { $1 }
  | LEFT_PARENTHESIS fof_formula RIGHT_PARENTHESIS
    { $2 }
  | atomic_formula
    { $1 }

quantified_formula:
  | quantifier LEFT_BRACKET variable_list RIGHT_BRACKET
    COLON unitary_formula
    { 
      List.fold_left (fun form v -> $1 v form) $6 $3
    }

quantifier:
  | FORALL
    { Simple.mk_forall }
  | EXISTS
    { Simple.mk_exists }

variable_list:
  | variable
    { [$1] }
  | variable COMMA variable_list
    { $1 :: $3 }

unary_formula:
  | unary_connective unitary_formula
    { $1 $2 }

unary_connective:
  | NEGATION
    { Simple.mk_not }


cnf_annotated:
  | CNF LEFT_PARENTHESIS name COMMA formula_role COMMA
  cnf_formula annotations RIGHT_PARENTHESIS DOT
      // ignore everything except for the formula
      {
        let clause = 
          let filename = !Const.cur_filename in  (* ugly *)
          let source = Simple.Axiom (filename, $3) in
          $7, source
        in
        init_clause ();
        clause
      }

formula_role:
  | LOWER_WORD
    { let role = $1 in
      (if role = "conjecture" then
        conjecture := true);
      $1
    }
  | LEMMA { "lemma" }

annotations:
  | null
      { "" }

  | COMMA source optional_info
      { "" }



cnf_formula:
  | LEFT_PARENTHESIS disjunction RIGHT_PARENTHESIS
      { Simple.mk_or $2 }

  | disjunction
      { Simple.mk_or $1 }

disjunction:
  | literal
      { [$1] }

  | literal OR disjunction
      { $1 :: $3 }


literal:
  | atomic_formula
      { $1 }

  | NEGATION atomic_formula
      { Simple.mk_not $2 }

atomic_formula:
  | plain_atom
      { $1 }

  | defined_atom
      { $1 }

  | system_atom
      { $1 }

plain_atom:
  | plain_term_top
      { let t = Simple.cast $1 bool_sort in (* cast term to bool *)
        (match t with
        | Simple.Node (s, _, _) -> set_sort s bool_sort
        | Simple.Var _ -> failwith "variable at top level");
        Simple.mk_atom t
      }

arguments:
  | term
      { [ $1 ] }

  | term COMMA arguments
      { $1 :: $3 }

defined_atom:
  | DOLLAR_TRUE
      { Simple.mk_true }

  | DOLLAR_FALSE
      { Simple.mk_false }

  | term EQUALITY term
      { Simple.mk_eq $1 $3 }
  | term DISEQUALITY term
      { Simple.mk_neq $1 $3 }

system_atom:
  | system_term_top
      { let t = Simple.cast $1 bool_sort in
        (match t with
        | Simple.Node (s, _, _) -> set_sort s bool_sort
        | Simple.Var _ -> assert false);
        Simple.mk_atom t
      }

term:
  | function_term
      { $1 }

  | variable
      { $1 }

function_term:
  | plain_term
      { $1 }

  | defined_term
      { $1 }

  | system_term
      { $1 }

plain_term_top:
  | constant
      { let sort = get_sort $1 in
        Simple.mk_const $1 sort }

  | functor_ LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let sort = get_sort $1 in
        Simple.mk_node $1 sort $3
      }

plain_term:
  | constant
      { let sort = get_sort $1 in
        Simple.mk_const $1 sort }

  | functor_ LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let sort = get_sort $1 in
        Simple.mk_node $1 sort $3
      }

constant:
  | atomic_word
      { mk_symbol $1 }

functor_:
  | atomic_word
      { mk_symbol $1 }

defined_term:
  | number
      { Const.parse_error ("<defined_term: number> not supported: " ^ $1) }

  | DISTINCT_OBJECT
      { Const.parse_error ("<defined_term: distinct_object> not supported: " ^ $1) }

system_term_top:
  | system_constant
      { let sort = get_sort $1 in
        Simple.mk_const $1 sort }

  | system_functor LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { 
        Simple.mk_node $1 univ_sort $3
      }

system_term:
  | system_constant
      { let sort = get_sort $1 in
        Simple.mk_const $1 sort }

  | system_functor LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let sort = get_sort $1 in
        Simple.mk_node $1 sort $3
      }

system_functor:
  | atomic_system_word
      { mk_symbol $1 }
      
system_constant:
  | atomic_system_word
      { mk_symbol $1 }



variable:
  | UPPER_WORD
      { get_var $1 }


source:
  | general_term
      { "" }

optional_info:
  | COMMA useful_info
      { "" }

  | null
      { "" }

useful_info:
  | general_term_list
      { "" }
      

include_:
  | INCLUDE LEFT_PARENTHESIS file_name formula_selection RIGHT_PARENTHESIS DOT
      { include_files := $3 :: !include_files }

formula_selection:
  | COMMA '[' name_list ']'
      { $3 }

  | null
      { [] }

name_list:
  | name
      { [$1] }

  | name COMMA name_list
      { $1 :: $3 }



general_term:
  | general_data
      { "" }

  | general_data COLON general_term
      { "" }

  | general_list
      { "" }

general_data:
  | atomic_word
      { "" }

  | atomic_word LEFT_PARENTHESIS general_arguments RIGHT_PARENTHESIS
      { "" }

  | number
      { "" }

  | DISTINCT_OBJECT
      { "" }

general_arguments:
  | general_term
      { [$1] }

  | general_term COMMA general_arguments
      { $1 :: $3 }

general_list:
  | '[' ']'
      { [] }

  | '[' general_term_list ']'
      { $2 }

general_term_list:
  | general_term
      { [$1] }

  | general_term COMMA general_term_list
      { $1 :: $3 }


name:
  | atomic_word
      { $1 }

  | UNSIGNED_INTEGER
      { $1 }

atomic_word:
  | LOWER_WORD
      { $1 }

  | SINGLE_QUOTED
      { $1 }

atomic_system_word:
  | DOLLAR_DOLLAR_WORD
      { $1 }

number:
  | REAL
      { $1 }

  | SIGNED_INTEGER
      { $1 }

  | UNSIGNED_INTEGER
      { $1 }

file_name:
  | SINGLE_QUOTED
      { let quoted = $1 in
        String.sub quoted 1 (String.length quoted - 2)
      }

null:
      { }


/* Theory parsing stuff */

theory_disjunctions:
  | theory_disjunction { [$1] }
  | theory_disjunction theory_disjunctions { $1 :: $2 }

theory_disjunction:
  | theory_named_formula { Theories.Named $1 }
  | theory_theory { Theories.Theory $1 }
  | theory_lemma { Theories.Lemma $1 }

theory_named_formula:
  | datalog_atom IS fof_formula DOT
    {
      let open Patterns in let open Theories in
      let atom_name, atom_args = $1 in
      let f = $3 in
      (* transform to hclause *)
      let ord = Orderings.default_ordering (Simple.signature [f]) in
      let ctx = {ctx_ord=ord; ctx_select=no_select; } in
      let hc = Clauses.from_simple ~ctx (f, Simple.Axiom ("theory", "theory")) in
      (* transform f into a pattern *)
      let rev_map = empty_rev_mapping () in
      let pc = pclause_of_clause ~rev_map hc in
      (* translate symbols of the atom *)
      let atom_args = List.map
        (fun s ->
          try SHashtbl.find rev_map.rm_symbol s
          with Not_found -> failwith ("symbol not found " ^ (name_symbol s)))
        atom_args in
      (* ensure the order of atom symbols is the same as in the pclause *)
      let pc = { pc with pc_vars = atom_args; } in
      let nf = { np_pattern = pc; np_name = atom_name; } in
      (* ready for next thing to parse *)
      SHashtbl.clear sort_table;
      nf
    }

theory_theory:
  | THEORY datalog_atom IS datalog_atoms DOT
    {
      let open Theories in
      (* map symbols to variables *)
      let get_var =
        let table = SHashtbl.create 3 in
        fun name ->
          try `Var (SHashtbl.find table name)
          with Not_found ->
            let n = -(SHashtbl.length table)-1 in
            SHashtbl.replace table name n;
            `Var n
      in
      let convert_atom (head, args) = head, List.map get_var args in
      { th_atom = convert_atom $2;
        th_definition = List.map convert_atom $4;
      }
    }

theory_lemma:
  | LEMMA datalog_atom IF datalog_atoms DOT
    {
      let open Theories in
      (* map symbols to variables *)
      let get_var =
        let table = SHashtbl.create 3 in
        fun name ->
          try `Var (SHashtbl.find table name)
          with Not_found ->
            let n = -(SHashtbl.length table)-1 in
            SHashtbl.replace table name n;
            `Var n
      in
      let convert_atom (head, args) = head, List.map get_var args in
      { lemma_conclusion = convert_atom $2;
        lemma_premises = List.map convert_atom $4;
      }
    }

datalog_atoms:
  | datalog_atom { [$1] }
  | datalog_atom AND datalog_atoms { $1 :: $3 }

datalog_atom:
  | LOWER_WORD { mk_symbol $1, [] }
  | LOWER_WORD LEFT_PARENTHESIS datalog_args RIGHT_PARENTHESIS
    { mk_symbol $1, $3 }

datalog_args:
  | datalog_arg { [$1] }
  | datalog_arg COMMA datalog_args { $1 :: $3 }

datalog_arg:
  | LOWER_WORD { let s = mk_symbol $1 in s }


%%




