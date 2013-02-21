(*
Zipperposition: a functional superposition prover for prototyping
Copyright (C) 2012 Simon Cruanes

This is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.
*)

(** {1 Persistent Knowledge Base} *)

open Types

module T = Terms
module Utils = FoUtils

(** {2 Knowledge Item} *)

(** Definitions at the meta-level, that respectively state that
    a lemma is true, that define a theory, or that bind a ground
    convergent system to a theory *)
type definition =
| Named of string * Pattern.t
| Theory of string parametrized * premise list
| Lemma of Pattern.t parametrized * premise list
| GC of gnd_convergent_spec * premise list
(** Condition for some meta-level assertion *)
and premise =
| IfNamed of string parametrized
| IfTheory of string parametrized
| IfPattern of Pattern.t parametrized
(** Assertions about the problem *)
and fact =
| ThenPattern of Pattern.t parametrized
| ThenTheory of string parametrized
| ThenNamed of string parametrized
| ThenGC of gnd_convergent_spec
and gnd_convergent_spec = {
  gc_vars : varlist;
  gc_ord : string;
  gc_prec : varlist;
  gc_eqns : Pattern.t list;
} (** Abstract equations that form a ground convergent rewriting system
      when instantiated. It is parametrized by the theory it decides.
      gc_ord and gc_prec (once instantiated), give a constraint on the ordering
      that must be satisfied for the system to be a decision procedure. *)

(** {2 Printing/parsing} *)

let rec pp_definition formatter definition =
  match definition with
  | Named (name, p) ->
    Format.fprintf formatter "@[<h>%s is %a]@." name Pattern.pp_pattern p
  | Lemma ((concl, vars), premises) ->
    Format.fprintf formatter "@[<hov2>%a(%a) if@ %a@]"
      Pattern.pp_pattern concl
      (Utils.pp_list !T.pp_term#pp) vars
      (Utils.pp_list pp_premise) premises
  | Theory ((name,args), premises) ->
    Format.fprintf formatter "@[<hov2>theory %s(%a) if@ %a@]" name
      (Utils.pp_list !T.pp_term#pp) args
      (Utils.pp_list pp_premise) premises
  | GC (gc, premises) ->
    Format.fprintf formatter
      "@[<hov2>gc %a@ @[<h>with %s(%a) if@ %a@]@]"
      (Utils.pp_list ~sep:" and " Pattern.pp_pattern) gc.gc_eqns
      gc.gc_ord (Utils.pp_list !T.pp_term#pp) gc.gc_prec
      (Utils.pp_list pp_premise) premises
and pp_premise formatter premise =
  match premise with
  | _ -> failwith "TODO: kb.pp_premise"
and pp_fact formatter fact =
  failwith "TODO: kb.pp_fact"

let definition_to_json definition : json =
  match definition with
  | _ -> `Null (* TODO *)
  (*
  | Lemma (concl,premises) ->
    `Assoc ["conclusion", Pattern.to_json concl;
            "premises", `List (List.map Pattern.to_json premises);]
  | Theory ((th, args), premises) ->
    `List (`String "theory" :: `String th :: List.map T.to_json args)
  | _ -> failwith "todo: definition to json"
  *)

let definition_of_json (json : json) : definition =
  match json with
  | _ -> failwith "TODO: KB.definition_of_json" (* TODO *)
  (*
  | `Assoc ["conclusion", concl; "premises", `List premises] ->
    Lemma (Pattern.of_json concl, List.map Pattern.of_json premises)
  | `List (`String "theory" :: `String th :: args) ->
    Theory (th, List.map T.of_json args)
  | _ -> failwith "todo: item_of_json"
  *)

(** {2 Datalog atoms} *)

type atom =
| MString of string
| MPattern of Pattern.t
| MTerm of term

let rec eq_atom a1 a2 = match a1, a2 with
  | MString s1, MString s2 -> s1 = s2
  | MPattern p1, MPattern p2 -> Pattern.eq_pattern p1 p2
  | MTerm t1, MTerm t2 -> t1 == t2
  | _ -> false

let rec hash_atom = function
  | MString s -> Hash.hash_string s
  | MPattern p -> Pattern.hash_pattern p
  | MTerm t -> T.hash_term t

let rec pp_atom formatter a = match a with
  | MString s -> Format.pp_print_string formatter s
  | MPattern p -> Pattern.pp_pattern formatter p
  | MTerm t -> T.pp_term_debug#pp formatter t

let rec atom_to_json a : json = match a with
  | MString s -> `String s
  | MPattern p -> `Assoc ["pattern", Pattern.to_json p]
  | MTerm t -> `Assoc ["term", T.to_json t]

let rec atom_of_json (json : json) : atom = match json with
  | `String s -> MString s
  | `Assoc ["pattern", p] -> MPattern (Pattern.of_json p)
  | `Assoc ["term", t] -> MTerm (T.of_json t)
  | _ -> raise (Json.Util.Type_error ("expected atom", json))

(** The Datalog prover that reasons over atoms. *)
module Logic = Datalog.Logic.Make(struct
  type t = atom
  let equal = eq_atom
  let hash = hash_atom
  let to_string a = Utils.sprintf "%a" pp_atom a
  let of_string s = atom_of_json (Json.from_string s)  (* XXX should not happen *)
  let lock () = ()
  let unlock () = ()
end)
  
(** {2 Conversion to Datalog} *)

(** Encode term into a Datalog atom *)
let encode_term t = match t.term with
  | Var i when i >= 0 -> `Var (-(i*2)-1)
  | Var i when i < 0 -> `Var (i*2)
  | _ -> `Symbol (MTerm t)

(** Convert a Datalog atom back to a term of given sort, or raise Failure *)
let deencode_term t sort = match t with
  | `Var i when (i mod 2) = 0 -> T.mk_var (i/2) sort
  | `Var i -> T.mk_var (-(i+1)/2) sort
  | `Symbol (MTerm t) ->
    assert (t.sort == sort);
    t
  | `Symbol s -> failwith (Utils.sprintf "Datalog atom %a not a term" pp_atom s)

(** {3 Construction of atoms} *)

let atom_named name args =
  Logic.mk_literal (MString "named") (`Symbol (MString name) :: args)

let atom_theory name args =
  Logic.mk_literal (MString "theory") (`Symbol (MString name) :: args)

let atom_pattern pat args =
  Logic.mk_literal (MString "pattern") (`Symbol (MPattern pat) :: args)

let atom_gc ?(offset=(-1)) gc =
  let args = [`Symbol (MString gc.gc_ord)] in
  let args = args @ List.map encode_term gc.gc_prec in
  let args = args @ List.map (fun pat -> `Symbol (MPattern pat)) gc.gc_eqns in
  let args = args @ List.map encode_term gc.gc_vars in
  Logic.mk_literal (MString "gc") args

(** Convert the arguments into terms. Expected sorts are given and
    must match. *)
let extract_terms sorts args =
  assert (List.length sorts = List.length args);
  let terms = List.fold_left2
    (fun acc sort arg -> match arg with
      | `Symbol (MPattern _)
      | `Symbol (MString _) -> assert false
      | `Symbol (MTerm t) ->
        assert (t.sort == sort);
        t::acc
      | `Var i -> (T.mk_var i sort) :: acc)
    [] sorts args in
  List.rev terms

(** Extract only constant terms. It expects a list of
    `Symbol (MTerm constant). *)
let extract_consts args =
  List.map
    (function
      | `Symbol (MTerm t) when not (T.is_var t) -> t
      | _ -> assert false)
    args

(** Translate a premise to a Datalog literal *)
let premise_to_datalog premise =
  match premise with
  | IfNamed (name, args) -> atom_named name (List.map encode_term args)
  | IfTheory (name, args) -> atom_theory name (List.map encode_term args)
  | IfPattern (p, args) -> atom_pattern p (List.map encode_term args)

(** Translate a definition into a Datalog clause *)
let definition_to_datalog definition =
  match definition with
  | Named (name, ((p, sorts) as pattern)) ->
    let vars = List.mapi (fun i sort -> encode_term (T.mk_var i sort)) sorts in
    let concl = atom_named name vars in
    let premises = [atom_pattern pattern vars] in
    Logic.mk_clause concl premises
  | Lemma ((p, args), premises) ->
    let premises = List.map premise_to_datalog premises in 
    let concl = atom_pattern p (List.map encode_term args) in
    Logic.mk_clause concl premises
  | Theory ((name, args), premises) ->
    let premises = List.map premise_to_datalog premises in 
    let concl = atom_theory name (List.map encode_term args) in
    Logic.mk_clause concl premises
  | GC (gc, premises) ->
    let premises = List.map premise_to_datalog premises in 
    let concl = atom_gc gc in
    Logic.mk_clause concl premises

(** Convert a meta-fact to a Datalog fact *)
let fact_to_datalog fact =
  match fact with
  | ThenPattern (p, args) -> atom_pattern p (List.map encode_term args)
  | ThenTheory (name, args) -> atom_theory name (List.map encode_term args)
  | ThenGC _ ->
    failwith "Meta.KB.fact_to_datalog makes no sense for ThenGC"
  | ThenNamed _ ->
    failwith "Meta.KB.fact_to_datalog makes no sense for ThenNamed"

(** Try to convert back a Datalog fact into a meta-fact *)
let of_datalog lit =
  match Logic.open_literal lit with
  | MString "pattern", (`Symbol (MPattern p) :: args) ->
    let terms = extract_terms (snd p) args in
    Some (ThenPattern (p, terms))
  | MString "named", (`Symbol (MString name) :: args) ->
    let terms = extract_consts args in
    Some (ThenNamed (name, terms))
  | MString "theory", (`Symbol (MString name) :: args) ->
    let terms = extract_consts args in
    Some (ThenTheory (name, terms))
  | MString "gc", (`Symbol (MString gc_ord) :: args) ->
    (* extract (list of terms, list of patterns, list of terms) *) 
    let rec extract at_prec (prec,pats,vars) l = match l with
    | [] -> List.rev prec, List.rev pats, List.rev vars
    | (`Symbol (MPattern p))::l' -> extract false (prec,p::pats,vars) l'
    | (`Symbol (MTerm t))::l' when at_prec -> extract true (t::prec,pats,vars) l'
    | (`Symbol (MTerm t))::l' -> extract false (prec,pats,t::vars) l'
    | _ -> assert false
    in
    let gc_prec, gc_eqns, gc_vars = extract true ([],[],[]) args in
    Some (ThenGC { gc_prec; gc_eqns; gc_vars; gc_ord; })
  | _ -> None 

(** {2 Knowledge Base} *)

type t = definition list
  (** The knowledge base. *)

let empty = []

let add_definition kb d = d :: kb

let to_seq kb = Sequence.of_list kb

let of_seq kb definitions =
  Sequence.fold add_definition kb definitions

(** {2 Printing/parsing} *)

let pp formatter kb =
  Utils.pp_list pp_definition formatter kb 

let to_json kb : json = `List (List.map definition_to_json kb)

let of_json kb (json : json) : t =
  let l = Json.Util.to_list json in
  of_seq kb (Sequence.map definition_of_json (Sequence.of_list l))

(** {2 Saving/restoring KB from disk} *)

let save ~file kb =
  let json = to_json kb in
  Json.to_file file json

let restore ~file kb =
  let json = Json.from_file file in
  of_json kb json
