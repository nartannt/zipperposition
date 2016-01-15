
(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Priority Queue of clauses} *)

open Libzipperposition

module O = Ordering
module Lit = Literal
module Lits = Literals

module type S = ClauseQueue_intf.S

type profile = ClauseQueue_intf.profile

let profile_of_string s =
  let open ClauseQueue_intf in
  match s |> String.trim |> String.lowercase with
  | "default" -> P_default
  | "bfs" -> P_bfs
  | "explore" -> P_explore
  | "ground" -> P_ground
  | "goal" -> P_goal
  | s -> invalid_arg ("unknown queue profile: " ^ s)

let _profile = ref ClauseQueue_intf.P_default
let get_profile () = !_profile
let set_profile p = _profile := p
let parse_profile s = _profile := (profile_of_string s)

let () =
  Params.add_opts
    [ "--clause-queue"
      , Arg.String parse_profile
      , " choose which set of clause queues to use \
         (for selecting next active clause): choices: default,bfs,explore,ground,goal"
    ]

module Make(C : Clause.S) = struct
  module C = C

  (* weight of a term [t], using the precedence's weight *)
  let term_weight t = FOTerm.size t

  (** {6 Weight functions} *)
  module WeightFun = struct
    type t = C.t -> int

    let weight_lits_ l =
      Array.fold_left
        (fun acc lit -> acc + Lit.heuristic_weight term_weight lit)
        0 l

    let default c =
      (* maximum depth of types. Avoids reasoning on list (list (list .... (list int))) *)
      let _depth_ty =
        Lits.Seq.terms (C.lits c)
        |> Sequence.map FOTerm.ty
        |> Sequence.map Type.depth
        |> Sequence.max ?lt:None
        |> CCOpt.maybe CCFun.id 0
      in
      let trail = C.trail c in
      let w_lits = weight_lits_ (C.lits c) in
      let w_trail =
        Trail.fold
          (fun acc t -> match C.Ctx.BoolBox.extract_exn (Sat_solver.Lit.abs t) with
             | C.Ctx.BoolBox.Clause_component lits -> acc + weight_lits_ lits
             | C.Ctx.BoolBox.Case (_,_) ->
                 (* generic penalty for each inductive hypothesis *)
                 acc + 10)
          0 trail
      in
      w_lits * Array.length (C.lits c) + w_trail * (Trail.length trail) + _depth_ty

    let penalty_coeff_ = 20

    let favor_pos_unit c =
      let is_unit_pos c = match C.lits c with
        | [| lit |] when Lit.is_pos lit -> true
        | _ -> false
      in
      if is_unit_pos c then 0 else penalty_coeff_

    let favor_horn c =
      if Lits.is_horn (C.lits c) then 0 else penalty_coeff_

    let age c =
      if C.is_empty c then 0
      else C.id c

    let _conjecture_threshold = 15

    let favor_conjecture c =
      if C.is_empty c then 0
      else
        let d = match C.distance_to_conjecture c with
          | Some d -> min d _conjecture_threshold
          | None -> _conjecture_threshold
        in
        1+d

    let favor_goal c =
      (* check whether a literal is a goal *)
      let is_goal_lit lit = Lit.is_neg lit in
      let is_goal_clause c = CCArray.for_all is_goal_lit (C.lits c) in
      if is_goal_clause c then 0 else penalty_coeff_

    let favor_ground c = if C.is_ground c then 0 else penalty_coeff_

    let favor_non_goal c =
      (* check whether a literal is a goal *)
      let is_goal_lit lit = Lit.is_neg lit in
      let is_non_goal_clause c =
        CCArray.for_all
          (fun x -> not (is_goal_lit x))
          (C.lits c)
      in
      if is_non_goal_clause c then 0 else penalty_coeff_

    let combine ws =
      assert (ws <> []);
      assert (List.for_all (fun (_,c) -> c > 0) ws);
      fun c ->
        List.fold_left
          (fun sum (w,coeff) -> sum + coeff * w c)
          0 ws
  end

  module H = CCHeap.Make(struct
      type t = (int * C.t)
      let leq (i1, c1) (i2, c2) = i1 <= i2 || (i1 = i2 && C.compare c1 c2 <= 0)
    end)

  (** A priority queue of clauses, purely functional *)
  type t = {
    heap : H.t;
    functions : functions;
  }
  and functions = {
    weight : C.t -> int;
    name : string;
  }

  (** generic clause queue based on some ordering on clauses, given
      by a weight function *)
  let make ~weight name =
    let functions = {
      weight;
      name;
    } in
    { heap = H.empty; functions; }

  let is_empty q =
    H.is_empty q.heap

  let add q c =
    let w = q.functions.weight c in
    let heap = H.insert (w, c) q.heap in
    { q with heap; }

  let adds q hcs =
    let heap =
      Sequence.fold
        (fun heap c ->
           let w = q.functions.weight c in
           H.insert (w,c) heap)
        q.heap hcs in
    { q with heap; }

  let take_first q =
    if is_empty q then raise Not_found;
    let new_h, (_, c) = H.take_exn q.heap in
    let q' = { q with heap=new_h; } in
    q', c

  let name q = q.functions.name

  (** {6 Combination of queues} *)

  type queues = (t * int) list

  let goal_oriented =
    let open WeightFun in
    let weight = combine [age, 1; default, 4; favor_conjecture, 1; favor_goal, 1] in
    let name = "goal_oriented" in
    make ~weight name

  let bfs =
    let open WeightFun in
    let weight = combine [age, 5; default, 1] in
    make ~weight "bfs"

  let explore =
    let open WeightFun in
    let weight = combine [age, 1; default, 4; favor_goal, 1] in
    make ~weight "explore"

  let ground =
    let open WeightFun in
    let weight = combine [age, 1; favor_pos_unit, 1; favor_ground, 2] in
    make ~weight "ground"

  let default =
    let open WeightFun in
    let weight =
      combine
      [ age, 4; default, 3; favor_goal, 1
      ; favor_conjecture, 1; favor_pos_unit, 1]
    in
    make ~weight "default"

  let of_profile p =
    let open ClauseQueue_intf in
    match p with
    | P_default -> default
    | P_bfs -> bfs
    | P_explore -> explore
    | P_ground -> ground
    | P_goal -> goal_oriented

  let pp out q = CCFormat.fprintf out "queue %s" (name q)
  let to_string = CCFormat.to_string pp
end
