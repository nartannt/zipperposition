
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

(** {1 Basic Splitting à la Avatar} *)

module T = Logtk.FOTerm
module Lit = Literal
module Util = Logtk.Util

type 'a printer = Format.formatter -> 'a -> unit

let section = Logtk.Util.Section.make ~parent:Const.section "avatar"

(** {2 Sat-Solvers} *)

module BoolLit = struct
  type t = int
  let neg i = - i
  let to_int i = abs i
  let of_int i = i
end

(** A running SAT-solver *)
type sat_solver_instance = {
  add_lits : BoolLit.t list -> unit;
  add_clauses : BoolLit.t list list -> unit;
  check : unit -> [`Sat | `Unsat];
  set_printer : int printer -> unit;
}

(** A factory of SAT-solver instances *)
type sat_solver = {
  create : unit -> sat_solver_instance;
  name : string;
}

let _solvers = Hashtbl.create 5
let _default = ref None

let register_solver s =
  if Hashtbl.mem _solvers s.name
    then failwith (Printf.sprintf "Avatar: solver \"%s\" already registered" s.name);
  (* be sure we have a default solver *)
  if !_default = None
    then _default := Some s;
  Hashtbl.add _solvers s.name s

let solver_by_name n =
  try Some (Hashtbl.find _solvers n)
  with Not_found -> None

let current_solver () = !_default

let set_current_solver s =
  if not (Hashtbl.mem _solvers s.name)
    then register_solver s;
  _default := Some s

(** {2 Avatar} *)

let prof_splits = Util.mk_profiler "avatar.split"
let prof_check = Util.mk_profiler "avatar.check"

let stat_splits = Util.mk_stat "avatar.splits"

module Make(E : Env.S) = struct
  module Ctx = E.Ctx
  module C = E.C
  module BoolLit = Ctx.BoolLit

  let _pp_bclause buf lits =
    Printf.bprintf buf "%a" (Util.pp_list ~sep:" ⊔ " BoolLit.pp) lits

  let _solver = ref None

  let _get_solver () = match !_solver with
    | None -> failwith "error, solver shouldn't be None"
    | Some s -> s

  let _add_lits l = (_get_solver()).add_lits l
  let _add_clauses l = (_get_solver()).add_clauses l

  (* union-find that maps terms to list of literals, used for splitting *)
  module UF = UnionFind.Make(struct
    type key = T.t
    type value = Lit.t list
    let equal = T.eq
    let hash = T.hash
    let zero = []
    let merge = List.rev_append
  end)

  module LitSet = Sequence.Set.Make(Lit)

  let _infer_split c =
    let lits = C.lits c in
    (* maps each variable to a list of literals. Sets can be merged whenever
      two variables occur in the same literal.  *)
    let uf_vars =
      C.Seq.vars c |> T.Seq.add_set T.Set.empty |> T.Set.elements |> UF.create
    (* set of ground literals (each one is its own component) *)
    and cluster_ground = ref LitSet.empty in

    (* literals belong to either their own ground component, or to every
        sets in [uf_vars] associated to their variables *)
    Array.iter
      (fun lit ->
        let v_opt = Lit.Seq.vars lit |> Sequence.head in
        match v_opt with
        | None -> (* ground, lit has its own component *)
            cluster_ground := LitSet.add lit !cluster_ground
        | Some v ->
            (* merge other variables of the literal with [v] *)
            Lit.Seq.vars lit
              |> Sequence.iter
                (fun v' ->
                  UF.add uf_vars v' [lit];  (* lit is in the equiv class of [v'] *)
                  UF.union uf_vars v v'
                );
      ) lits;

    (* now gather all the components as a literal list list *)
    let components = ref [] in
    LitSet.iter (fun lit -> components := [lit] :: !components) !cluster_ground;
    UF.iter uf_vars (fun _ comp -> components := comp :: !components);

    match !components with
    | [] -> assert (Array.length lits=0); None
    | [_] -> None
    | _::_ ->
        (* do a simplification! *)
        Util.incr_stat stat_splits;
        let clauses_and_names = List.map
          (fun lits ->
            let proof cc = Proof.mk_c_esa ~rule:"split" cc [C.proof c] in
            let lits = Array.of_list lits in
            let bool_name = BoolLit.inject_lits lits in
            let trail = C.Trail.singleton bool_name in
            let c = C.create_a ~parents:[c] ~trail lits proof in
            C.set_bool_name c bool_name;
            c, bool_name
          ) !components
        in
        let clauses, bool_clause = List.split clauses_and_names in
        Util.debug ~section 4 "split of %a yields %a" C.pp c (Util.pp_list C.pp) clauses;
        (* add boolean constraint: trail(c) => bigor_{name in clauses} name *)
        _add_lits bool_clause;
        let bool_guard = C.get_trail c |> C.Trail.to_list |> List.map BoolLit.neg in
        let bool_clause = List.append bool_clause bool_guard in 
        _add_clauses [bool_clause];
        Util.debug ~section 4 "constraint clause is %a" _pp_bclause bool_clause;
        (* return the clauses *)
        Some clauses

  (* Hyper-splitting *)
  let split c =
    Util.enter_prof prof_splits;
    let res = if Array.length (C.lits c) <= 1
      then None
      else _infer_split c
    in
    Util.exit_prof prof_splits;
    res

  (* if c.lits = [], negate c.trail *)
  let check_empty c =
    if Array.length (C.lits c) = 0
    then (
      assert (not (C.Trail.is_empty (C.get_trail c)));
      let b_lits = C.get_trail c |> C.Trail.to_list  in
      let b_clause = List.map BoolLit.neg b_lits in
      Util.debug ~section 4 "negate trail of %a with %a" C.pp c _pp_bclause b_clause;
      _add_clauses [b_clause];
    );
    [] (* never infers anything! *)

  (* Just check the solver *)
  let check_satisfiability () =
    Util.enter_prof prof_check;
    let s = _get_solver () in
    if Util.Section.cur_level section >= 5 then (
      Printf.printf "Boolean formula: TODO@."
    );
    let res = match s.check () with
    | `Sat ->
        Util.debug ~section 3 "SAT-solver reports \"SAT\"";
        []
    | `Unsat ->
        Util.debug ~section 1 "SAT-solver reports \"UNSAT\"";
        (* TODO: proper proof handling (collect unsat core? collect all clauses?)*)
        let proof cc = Proof.mk_c_inference ~rule:"avatar" ~theories:["sat"] cc [] in
        let c = C.create [] proof in
        [c]
    in
    Util.exit_prof prof_check;
    res

  let register () =
    Util.debug ~section:Const.section 2 "register extension Avatar";
    begin match current_solver() with
      | None -> failwith "Avatar: expect a default SAT solver to be defined."
      | Some s ->
          Util.debug ~section 2 "create a new solver (kind %s)" s.name;
          let solver = s.create() in
          solver.set_printer BoolLit.print;
          _solver := Some solver
    end;
    E.add_multi_simpl_rule split;
    E.add_unary_inf "avatar_check_empty" check_empty;
    E.add_generate "avatar_check_sat" check_satisfiability;
    ()
end

let extension =
  let action env =
    let module E = (val env : Env.S) in
    let module A = Make(E) in
    A.register()
  in
  Extensions.({default with name="avatar"; actions=[Do action]})

let _enabled = ref false
let _enable_avatar () =
  if not !_enabled then (
    _enabled := true;
    Extensions.register extension
  )

let () =
  Params.add_opts
    [ "-avatar", Arg.Unit _enable_avatar, "enable Avatar-like splitting (based on SAT)"
    ]