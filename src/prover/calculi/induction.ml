
(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Induction through Cut} *)

open Logtk

module Lits = Literals
module T = FOTerm
module Ty = Type
module Fmt = CCFormat
module RW = Rewrite

module type S = Induction_intf.S

type term = T.t
type var = T.var

let section = Util.Section.make ~parent:Const.section "induction"

let stats_lemmas = Util.mk_stat "induction.inductive_lemmas"
let stats_trivial_lemmas = Util.mk_stat "induction.trivial_lemmas"
let stats_absurd_lemmas = Util.mk_stat "induction.absurd_lemmas"
let stats_inductions = Util.mk_stat "induction.inductions"

let k_enable : bool Flex_state.key = Flex_state.create_key()
let k_ind_depth : int Flex_state.key = Flex_state.create_key()
let k_test_limit : int Flex_state.key = Flex_state.create_key()
let k_limit_to_active : bool Flex_state.key = Flex_state.create_key()
let k_coverset_depth : int Flex_state.key = Flex_state.create_key()

(** {2 Formula to be Proved Inductively *)
module Make_goal(E : Env_intf.S) : sig
  type t

  val trivial : t
  (** trivial goal *)

  val make : Literals.t list -> t

  val form : t -> Cut_form.t
  val cs : t -> Literals.t list
  val vars : t -> T.VarSet.t

  val ind_vars : t -> var list
  (** the inductive variables *)

  val pp : t CCFormat.printer

  type status =
    | S_trivial
    | S_ok
    | S_falsifiable of Subst.t

  val test : t -> status
  (** Testing using {!Test_prop} *)

  val check_not_absurd_or_trivial : t -> bool
  (** More thorough testing *)

  val is_acceptable_goal : t -> bool
end = struct
  type status =
    | S_trivial
    | S_ok
    | S_falsifiable of Subst.t

  (* formula to be proved inductively. The clauses share some variables,
     they are not independent *)
  type t = {
    cut: Cut_form.t;
    test_res: status lazy_t;
  }

  let trivial: t =
    {cut=Cut_form.trivial; test_res=Lazy.from_val S_trivial}

  (* trivial clause? *)
  let trivial_c (c:Literals.t): bool = Literals.is_trivial c

  let test_ (cs:Literals.t list): status =
    (* test and save *)
    if List.for_all trivial_c cs then S_trivial
    else begin match Test_prop.check_form cs with
      | Test_prop.R_ok -> S_ok
      | Test_prop.R_fail subst -> S_falsifiable subst
    end

  let make cs: t =
    let cut = Cut_form.make cs in
    let test_res = lazy (test_ cs) in
    {cut; test_res}

  let form t = t.cut
  let cs t = Cut_form.cs t.cut
  let vars t = Cut_form.vars t.cut
  let test (t:t): status = Lazy.force t.test_res
  let ind_vars t = Cut_form.ind_vars t.cut

  let pp out (f:t): unit = Cut_form.pp out f.cut

  module C = E.C

  let test_goal_is_ok (g:t): bool =
    begin match test g with
      | S_ok -> true
      | S_trivial ->
        Util.incr_stat stats_trivial_lemmas;
        Util.debugf ~section 2 "(@[<2>lemma_trivial@ @[%a@]@@])" (fun k->k pp g);
        false
      | S_falsifiable subst ->
        Util.debugf ~section 2
          "(@[<2>lemma_absurd@ @[%a@]@ :subst %a@])"
          (fun k->k pp g Subst.pp subst);
        Util.incr_stat stats_absurd_lemmas;
        false
    end

  exception Yield_false of C.t

  (* TODO: re-establish this, but only do it if smallcheck failed
      (also, do the 20 steps of resolution only in last resort)

      → if goal passes tests, can we use the demod/sup steps to infer active
         positions? (e.g. looking at which variables were substituted with
         cstor terms) *)

  (* check that [lemma] is not obviously absurd or trivial, by using
     the corresponding inference rules from env [E].

     We do not try to refute it with a few superposition steps because
     in cases it would work (lemma is wrong, attempted nonetheless,
     and refutable in a few steps), the lemma will be disproved and
     simplified away by saturation anyway.
  *)
  let check_not_absurd_or_trivial (g:t): bool =
    Util.debugf ~section 2 "@[<2>@{<green>assess goal@}@ %a@]"
      (fun k->k pp g);
    let trivial = ref true in
    try
      (* fully simplify each goal's clause, check if absurd or trivial *)
      List.iter
        (fun lits ->
           let c = C.create_a ~trail:Trail.empty lits ProofStep.mk_trivial in
           let cs, _ = E.all_simplify c in
           begin match CCList.find_pred C.is_empty cs with
             | Some c_empty -> raise (Yield_false c_empty)
             | None ->
               if not (List.for_all E.is_trivial cs) then trivial := false
           end)
        (cs g);
      Util.debugf ~section 2
        "@[<2>lemma @[%a@]@ apparently not absurd (trivial:%B)@]"
        (fun k->k pp g !trivial);
      if !trivial then Util.incr_stat stats_trivial_lemmas;
      not !trivial
    with Yield_false c ->
      assert (C.is_empty c);
      Util.debugf ~section 2
        "@[<2>lemma @[%a@] absurd:@ leads to empty clause `%a`@]"
        (fun k->k pp g C.pp c);
      Util.incr_stat stats_absurd_lemmas;
      false

  (* some checks that [g] should be considered as a goal *)
  let is_acceptable_goal (g:t) : bool =
    test_goal_is_ok g &&
    check_not_absurd_or_trivial g
end

module T_view : sig
  type 'a t =
    | T_var of T.var
    | T_app_defined of ID.t * Rewrite.Defined_cst.t * 'a list
    | T_app_cstor of ID.t * 'a list
    | T_app_unin of ID.t * 'a list
    | T_app of 'a * 'a list
    | T_builtin of Builtin.t * 'a list

  val view : term -> term t

  val active_subterms : term -> term Sequence.t
  (** Visit all active subterms in the given term.
      A subterm is active if it's under a cstor, uninterpreted symbol,
      builtin, or under a defined function at an active position *)
end = struct
  type 'a t =
    | T_var of T.var
    | T_app_defined of ID.t * Rewrite.Defined_cst.t * 'a list
    | T_app_cstor of ID.t * 'a list
    | T_app_unin of ID.t * 'a list
    | T_app of 'a * 'a list
    | T_builtin of Builtin.t * 'a list

  let view (t:term): term t = match T.view t with
    | T.AppBuiltin (b, l) -> T_builtin (b,l)
    | T.Var v -> T_var v
    | T.Const id when Ind_ty.is_constructor id -> T_app_cstor (id, [])
    | T.Const id when Classify_cst.id_is_defined id ->
      begin match RW.as_defined_cst id with
        | Some c -> T_app_defined (id, c, [])
        | None -> T_app_unin (id, [])
      end
    | T.Const id -> T_app_unin (id, [])
    | T.App (f, l) ->
      begin match T.view f with
        | T.Const id when Ind_ty.is_constructor id -> T_app_cstor (id, l)
        | T.Const id when Classify_cst.id_is_defined id ->
          begin match RW.as_defined_cst id with
            | Some c -> T_app_defined (id, c, l)
            | None -> T_app_unin (id, l)
          end
        | T.Const id -> T_app_unin (id, l)
        | _ -> T_app (f,l)
      end
    | T.DB _ -> assert false

  let active_subterms t yield: unit =
    let rec aux t =
      yield t;
      begin match view t with
        | T_app_defined (_, c, l) ->
          let pos = RW.Defined_cst.defined_positions c in
          assert (IArray.length pos >= List.length l);
          (* only look under active positions *)
          List.iteri
            (fun i sub ->
               if IArray.get pos i = Defined_pos.P_active then aux sub)
            l
        | T_var _ -> ()
        | T_app (f,l) ->
          aux f;
          List.iter aux l
        | T_app_cstor (_,l) -> List.iter aux l
        | T_builtin (_,l)
        | T_app_unin (_,l) -> List.iter aux l
      end
    in aux t
end

(* data flow for induction:

   1) Introduce lemmas
     - some lemmas come directly from the input, and are directly
       asserted in Avatar
     - some other lemmas are "guessed" from regular clauses that
       contain inductive skolems. From these clauses (where we do not know
       what to do with these skolems in general), a lemma is
       built by negating the clauses and replacing the skolems by fresh
       variables.

       The goals obtained from this second source (given clauses)
       are pre-processed:
       - they are tested (see {!Test_prop}) to avoid trying to prove
         trivially false lemmas
       - they might be generalized using a collection of heuristics.
         Each generalization is also tested.

       Then, the surviving goals are added to Avatar using [A.introduce_cut].

   2) new lemmas from Avatar (coming from 1)) are checked for {b variables}
      with an inductive type.
      For each such variable satisfying some side condition (e.g. occurring
      at least once in active position), a fresh coverset of the variable's
      type is built, and fresh skolems are created for the other variables.

      Clauses of the goal (they share variables) are then instantiated
      to the ground with these skolems (and each case of the coverset)
      and then negated. We add a trail to them. The trail contains [not lemma]
        and the corresponding case literal.
      The resulting formulas are re-normalized  into CNF and added to
      the resulting set of clauses.
      In addition, for each recursive case of the coverset, induction
      hypothesis are added (instantiating the goal with this case,
      keeping the other variables identical).

    3) the resulting set of clauses
*)

(* TODO: strong induction? instead of using sub-constants of the case
   in the induction hypothesis, use a constraint [x < top] *)

(** {2 Calculus of Induction} *)
module Make
    (E : Env.S)
    (A : Avatar_intf.S with module E = E)
= struct
  module Env = E
  module Ctx = E.Ctx
  module C = E.C
  module BoolBox = BBox
  module BoolLit = BoolBox.Lit
  module Goal = Make_goal(E)

  let max_depth = Env.flex_get k_ind_depth
  let cover_set_depth = Env.flex_get k_coverset_depth

  let is_ind_conjecture_ c =
    match C.distance_to_goal c with
      | Some (0 | 1) -> true
      | Some _
      | None -> false

  let has_pos_lit_ c = CCArray.exists Literal.is_pos (C.lits c)

  (* TODO: readapt? *)
  let generalizable_subterms c: term list =
    let count = T.Tbl.create 16 in
    C.Seq.terms c
    |> Sequence.flat_map T.Seq.subterms
    |> Sequence.filter
      (fun t -> Ind_ty.is_inductive_type (T.ty t) && not (T.is_const t))
    |> Sequence.iter
      (fun t ->
         let n = try T.Tbl.find count t with Not_found -> 0 in
         T.Tbl.replace count t (n+1));
    (* terms that occur more than once *)
    T.Tbl.to_seq count
    |> Sequence.filter_map (fun (t,n) -> if n>1 then Some t else None)
    |> Sequence.to_rev_list

  (* fresh var generator *)
  let fresh_var_gen_ (): Type.t -> T.t =
    let r = ref 0 in
    fun ty ->
      let v = T.var_of_int ~ty !r in
      incr r;
      v

  (* scan terms for inductive skolems. *)
  let scan_terms ~mode (seq:term Sequence.t) : Ind_cst.ind_skolem list =
    seq
    |> Sequence.flat_map Ind_cst.find_ind_skolems
    |> Sequence.filter
      (fun (id,_) ->
         begin match Ind_cst.id_as_cst id, mode with
           | None, _ -> true
           | Some _, `All -> true
           | Some c, `No_sub_cst ->
             (* do not generalize on sub-constants,
                there are induction hypothesis on them that we will need *)
             not (Ind_cst.is_sub c)
         end)
    |> Sequence.to_rev_list
    |> CCList.sort_uniq ~cmp:Ind_cst.ind_skolem_compare

  (* scan clauses for ground terms of an inductive type,
     and perform induction on these terms.
      @return a list of ways to generalize the given clause *)
  let scan_clause (c:C.t) : Ind_cst.ind_skolem list list =
    let l1 =
      C.lits c |> Lits.Seq.terms |> scan_terms ~mode:`All
    and l2 =
      C.lits c |> Lits.Seq.terms |> scan_terms ~mode:`No_sub_cst
    in
    (* remove duplicates, empty lists, etc. *)
    begin
      [l1; l2]
      |> CCList.sort_uniq ~cmp:(CCList.compare Ind_cst.ind_skolem_compare)
      |> List.filter (fun l -> not (CCList.is_empty l))
    end

  (* goal for induction *)
  (* ensure the proper declarations are done for this coverset *)
  let decl_cst_of_set (set:Cover_set.t): unit =
    Util.debugf ~section 3
      "@[<2>declare coverset@ `%a`@]" (fun k->k Cover_set.pp set);
    begin
      Cover_set.declarations set
      |> Sequence.iter (fun (id,ty) -> Ctx.declare id ty)
    end

  (* induction on the given variables *)
  let ind_on_vars (cut:A.cut_res)(vars:T.var list): C.t list =
    assert (vars<>[]);
    let g = A.cut_form cut in
    let depth = A.cut_depth cut in
    let cut_blit = A.cut_lit cut in
    (* proof step *)
    let proof =
      ProofStep.mk_inference (List.map C.proof (A.cut_pos cut))
        ~rule:(ProofStep.mk_rulef "induction(@[<h>%a@])" (Util.pp_list HVar.pp) vars)
    in
    let c_sets =
      List.map
        (fun v ->
           let ty = HVar.ty v in
           v, Cover_set.make ~cover_set_depth ~depth ty)
        vars
    in
    List.iter (fun (_,set) -> decl_cst_of_set set) c_sets;
    Util.debugf ~section 2
      "(@[<hv2>ind_on_vars (@[%a@])@ :form %a@ :cover_sets (@[<hv>%a@])@])"
      (fun k->k (Util.pp_list HVar.pp) vars Cut_form.pp g
          (Util.pp_list (Fmt.Dump.pair HVar.pp Cover_set.pp)) c_sets);
    (* other variables -> become skolems *)
    let subst_skolems: Subst.t =
      Cut_form.vars g
      |> (fun set -> T.VarSet.diff set (T.VarSet.of_list vars))
      |> T.VarSet.to_list
      |> List.map
        (fun v ->
           let ty_v = HVar.ty v in
           let id = Ind_cst.make_skolem ty_v in
           Ctx.declare id ty_v;
           (v,0), (T.const ~ty:ty_v id,1))
      |> Subst.FO.of_list' ?init:None
    in
    (* set of boolean literal. We will add their exclusive disjonction to
       the SAT solver. *)
    let b_lits = ref [] in
    (* build clauses for the induction on [v] *)
    let clauses =
      Util.map_product c_sets
        ~f:(fun (v,set) ->
          Cover_set.cases ~which:`All set
          |> Sequence.to_list
          |> List.map (fun case -> [v,case]))
      |> CCList.flat_map
        (fun (cases:(T.var * Cover_set.case) list) ->
           assert (cases<>[]);
           (* literal for this case *)
           let b_lit_case = BBox.inject_case (List.map snd cases) in
           CCList.Ref.push b_lits b_lit_case;
           (* clauses [goal[v := t'] <- b_lit(case), ¬cut.blit]
              for every [t'] sub-constant of [case] *)
           let pos_clauses =
             Util.seq_map_l cases
               ~f:(fun (v,case) ->
                 Cover_set.Case.sub_constants case
                 |> CCList.filter_map
                   (fun sub_cst ->
                      (* only keep sub-constants that have the same type as [v] *)
                      if Type.equal (Ind_cst.ty sub_cst) (HVar.ty v) then (
                        let t = Ind_cst.to_term sub_cst in
                        Some (v,t)
                      ) else None))
             |> Sequence.flat_map_l
               (fun v_and_t_list ->
                  let subst =
                    v_and_t_list
                    |> List.map (fun (v,t) -> (v,0),(t,1))
                    |> Subst.FO.of_list' ?init:None
                  in
                  let renaming = Ctx.renaming_clear () in
                  let g' = Cut_form.apply_subst ~renaming subst (g,0) in
                  Cut_form.cs g'
                  |> List.map
                    (fun lits ->
                       let trail =
                         [ b_lit_case;
                           BoolLit.neg cut_blit;
                         ] |> Trail.of_list
                       in
                       C.create_a lits proof ~trail))
             |> Sequence.to_list
           in
           (* clauses [CNF[¬goal[case]) <- b_lit(case), ¬cut.blit] with
              other variables being replaced by skolem symbols *)
           let neg_clauses =
             let subst =
               cases
               |> List.map (fun (v,c) -> (v,0),(Cover_set.Case.to_term c,1))
               |> Subst.FO.of_list' ~init:subst_skolems
             in
             let renaming = Ctx.renaming_clear () in
             (* for each clause, apply [subst] to it and negate its
                literals, obtaining a DNF of [¬ And_i ctx_i[case]];
                then turn DNF into CNF *)
             begin
               Cut_form.apply_subst ~renaming subst (g,0)
               |> Cut_form.cs
               |> Util.map_product
                 ~f:(fun lits ->
                   let lits = Array.map (fun l -> [Literal.negate l]) lits in
                   Array.to_list lits)
               |> List.map
                 (fun l ->
                    let lits = Array.of_list l in
                    let trail =
                      [ BoolLit.neg cut_blit;
                        b_lit_case;
                      ] |> Trail.of_list
                    in
                    C.create_a lits proof ~trail)
             end
           in
           (* all new clauses *)
           let res = List.rev_append pos_clauses neg_clauses in
           Util.debugf ~section 2
             "(@[<2>induction on (@[%a@])@ :form %a@ @[<2>:cases (@[%a@])@]@ \
              :depth %d@ @[<2>:res [@[<hv>%a@]]@]@])"
             (fun k-> k (Util.pp_list HVar.pp) vars Cut_form.pp g
                 (Util.pp_list Fmt.(pair ~sep:(return ":=@ ") HVar.pp Cover_set.Case.pp)) cases
                 depth (Util.pp_list C.pp) res);
           res)
    in
    (* FIXME: should do CNF here, too *)
    (* boolean constraint(s) *)
    let b_clauses =
      (* [\Or_{t in cases} b_lit(t)] *)
      let b_at_least_one = !b_lits
      (* for each case t!=u, [¬b_lit(t) ∨ ¬b_lit(u)] *)
      and b_at_most_one =
        CCList.diagonal !b_lits
        |> List.rev_map
          (fun (l1,l2) -> [BoolLit.neg l1; BoolLit.neg l2])
      in
      b_at_least_one :: b_at_most_one
    in
    A.Solver.add_clauses ~proof b_clauses;
    Util.debugf ~section 2 "@[<2>add boolean constraints@ @[<hv>%a@]@ :proof %a@]"
      (fun k->k (Util.pp_list BBox.pp_bclause) b_clauses
          ProofPrint.pp_normal_step proof);
    Util.incr_stat stats_inductions;
    (* return the clauses *)
    clauses

  (* does the variable occur in an active position in [f],
     or under some uninterpreted position? *)
  let var_occurs_under_active_pos (f:Cut_form.t)(x:T.var): bool =
    let open T_view in
    let is_x (t:term): bool = match T.view t with
      | T.Var y -> HVar.equal Type.equal x y
      | _ -> false
    in
    (* true if [x] occurs in active positions somewhere in [t] *)
    let rec check_sub(t:term): bool = match T_view.view t with
      | T_app_defined (_, c, l) ->
        let pos = RW.Defined_cst.defined_positions c in
        assert (IArray.length pos >= List.length l);
        (* only look under active positions *)
        begin
          Sequence.of_list l
          |> Sequence.zip_i |> Sequence.zip
          |> Sequence.exists
            (fun (i,u) ->
               IArray.get pos i = Defined_pos.P_active &&
               ( is_x u || check_sub u ))
        end
      | T_var _ -> false
      | T_app (f,l) -> check_sub f || List.exists check_eq_or_sub l
      | T_app_cstor (_,l) -> List.exists check_sub l
      | T_builtin (_,l)
      | T_app_unin (_,l) -> List.exists check_eq_or_sub l (* approx *)
    (* true if [t=x] or if [x] occurs in active positions somewhere in [t] *)
    and check_eq_or_sub (t:term): bool =
      is_x t || check_sub t
    in
    begin
      Cut_form.cs f
      |> Sequence.of_list
      |> Sequence.flat_map Sequence.of_array
      |> Sequence.flat_map Literal.Seq.terms
      |> Sequence.exists check_sub
    end

  let active_subterms_form (f:Cut_form.t): T.t Sequence.t =
    Cut_form.cs f
    |> Sequence.of_list
    |> Sequence.flat_map Sequence.of_array
    |> Sequence.flat_map Literal.Seq.terms
    |> Sequence.flat_map T_view.active_subterms

  (* should we do induction on [x] in [c]? *)
  let should_do_ind_on_var (f:Cut_form.t) (x:T.var): bool =
    not (E.flex_get k_limit_to_active) ||
    var_occurs_under_active_pos f x

  module UF_vars =
    UnionFind.Make(struct
      type key = T.var
      type value = T.var list
      let equal = HVar.equal Type.equal
      let hash = HVar.hash
      let zero = []
      let merge = List.rev_append
    end)

  let eq_var = HVar.equal Type.equal

  (* group together variables that occur at active positions under
     the same subterm *)
  let find_var_clusters (f:Cut_form.t) (vars:T.var list): T.var list list =
    let uf = UF_vars.create [] in
    List.iter (fun v -> UF_vars.add uf v [v]) vars;
    begin
      active_subterms_form f
      |> Sequence.iter
        (fun t -> match T_view.view t with
           | T_view.T_app_defined (_,c,l) ->
             let pos = RW.Defined_cst.defined_positions c in
             Sequence.of_list l
             |> Sequence.zip_i |> Sequence.zip
             |> Sequence.diagonal
             |> Sequence.filter_map
               (fun ((i1,t1),(i2,t2)) ->
                  match T.as_var t1, T.as_var t2 with
                    | Some x, Some y
                      when
                        i1 < i2 &&
                        IArray.get pos i1 = Defined_pos.P_active &&
                        IArray.get pos i2 = Defined_pos.P_active &&
                        not (eq_var x y) &&
                        CCList.mem ~eq:eq_var x vars &&
                        CCList.mem ~eq:eq_var y vars
                      ->
                      Some (x,y)
                    | _ -> None)
             |> Sequence.iter
               (fun (x,y) ->
                  assert (not (eq_var x y));
                  UF_vars.union uf x y)
           | _ -> ())
    end;
    let res =
      UF_vars.to_seq uf
      |> Sequence.map snd
      |> Sequence.to_rev_list
    in
    Util.debugf ~section 3
      "(@[<hv2>induction_clusters@ :in %a@ :clusters (@[<hv>%a@])@])"
      (fun k->k Cut_form.pp f
          (Util.pp_list Fmt.(within "(" ")" @@ hvbox @@ Util.pp_list HVar.pp))
          res);
    res

  (* main inductive proof of lemmas that have inductive variables *)
  let prove_lemma (cut:A.cut_res): C.t list =
    let g = A.cut_form cut in
    Util.debugf ~section 5 "(@[<hv>prove_lemma@ %a@])" (fun k->k Cut_form.pp g);
    begin match Cut_form.ind_vars g with
      | [] -> []
      | ivars ->
        (* filter on which variables we do induction *)
        let ivars =
          List.filter
            (fun v ->
               let ok = should_do_ind_on_var g v in
               if not ok then (
                 Util.debugf ~section 3
                   "(@[<hv>ind: inactive variable `%a`@ :in %a@])"
                   (fun k->k HVar.pp v Cut_form.pp g);
               );
               ok)
            ivars
        in
        let clusters = find_var_clusters g ivars in
        (* for each variable, build a coverset of its type,
           and do a case distinction on the [top] constant of this
           coverset. *)
        CCList.flat_map (ind_on_vars cut) clusters
    end

  (* replace the constants by fresh variables in the given clauses,
     returning a goal. *)
  let generalize_clauses
      (cs:Lits.t list)
      ~(generalize_on:Ind_cst.ind_skolem list) : Goal.t =
    if generalize_on=[] then Goal.trivial
    else (
      (* offset to allocate new variables *)
      let offset =
        Sequence.of_list cs
        |> Sequence.flat_map Lits.Seq.vars
        |> T.Seq.max_var
        |> succ
      in
      (* (constant -> variable) list *)
      let pairs =
        List.mapi
          (fun i (id,ty) ->
             T.const ~ty id, T.var (HVar.make ~ty (i+offset)))
          generalize_on
        |> T.Map.of_list
      in
      Util.debugf ~section 5
        "@[<hv2>generalize_lits@ :in `@[<hv>%a@]`@ :subst (@[%a@])@]"
        (fun k->k (Util.pp_list ~sep:"∧" Lits.pp) cs
            (T.Map.pp T.pp T.pp) pairs);
      (* replace skolems by the new variables, then negate the formula
         and re-CNF the negation *)
      begin
        cs
        |> Util.map_product
          ~f:(fun lits ->
             lits
             |> Array.map
               (fun lit ->
                  lit
                  |> Literal.map (fun t -> T.replace_m t pairs)
                  |> Literal.negate
                  |> CCList.return)
             |> Array.to_list)
        |> List.map Array.of_list
        |> Goal.make
      end
    )

  (* try to prove theses clauses by turning the given constants into
     variables, negating the clauses, adn introducing the result
     as a lemma to be proved by induction.

      @param generalize_on the set of (skolem) constants that are replaced
       by free variables in the negation of [clauses] *)
  let prove_by_ind (clauses:C.t list) ~generalize_on : unit =
    Util.debugf ~section 5
      "(@[<2>consider_proving_by_induction@ \
       :clauses [@[%a@]]@ :generalize_on (@[%a@])@]"
      (fun k->k (Util.pp_list C.pp) clauses
          (Util.pp_list Fmt.(pair ~sep:(return ":@ ") ID.pp Type.pp))
          generalize_on);
    let goal =
      generalize_clauses
        (List.map C.lits clauses)
        ~generalize_on
    in
    let depth =
      Sequence.of_list generalize_on
      |> Sequence.map (fun (id,_) -> Ind_cst.ind_skolem_depth id)
      |> Sequence.max
      |> CCOpt.get_or ~default:0
    (* the trail should not contain a positive "lemma" atom.
       We accept negative lemma atoms because the induction can be used to
       prove the lemma *)
    and no_pos_lemma_in_trail () =
      Sequence.of_list clauses
      |> Sequence.map C.trail
      |> Sequence.flat_map Trail.to_seq
      |> Sequence.for_all
        (fun lit -> not (BoolLit.sign lit && BBox.is_lemma lit))
    in
    if depth <= max_depth && no_pos_lemma_in_trail () then (
      (* check if goal is worth the effort *)
      if Goal.is_acceptable_goal goal then (
        Util.debugf ~section 1
          "(@[<2>@{<green>prove_by_induction@}@ :clauses (@[%a@])@ :goal %a@])"
          (fun k->k (Util.pp_list C.pp) clauses Goal.pp goal);
        let proof = ProofStep.mk_lemma in
        let cut = A.introduce_cut ~depth (Goal.form goal) proof in
        A.add_lemma cut
      );
    );
    ()

  (* Try to prove the given clause by introducing an inductive lemma. *)
  let inf_prove_by_ind (c:C.t): C.t list =
    List.iter
      (fun consts ->
         assert (consts<>[]);
         prove_by_ind [c] ~generalize_on:consts)
      (scan_clause c);
    []

  (* hook for converting some statements to clauses.
     It check if [Negated_goal l] contains clauses with inductive skolems,
     in which case it tries to prove these clauses by induction in a lemma.
  *)
  let convert_statement st =
    begin match Statement.view st with
      | Statement.NegatedGoal (skolems, _) ->
        (* find inductive skolems in there *)
        let ind_skolems =
          List.filter
            (fun (id,ty) -> Ind_cst.id_is_ind_skolem id ty)
            skolems
        in
        begin match ind_skolems with
          | [] -> E.CR_skip
          | consts ->
            (* introduce one lemma where all the skolems are
               replaced by variables. But first, simplify these clauses
               because otherwise the inductive subgoals
               (which are simplified) will not match
               the inductive hypothesis. *)
            let clauses =
              C.of_statement st
              |> CCList.flat_map (fun c -> fst (E.all_simplify c))
            in
            prove_by_ind clauses ~generalize_on:consts;
            (* "skip" in any case, because the proof is done in a cut anyway *)
            E.CR_skip
        end
      | _ -> E.cr_skip
    end

  (* checks whether the trail is trivial, that is, it contains
     two literals [i = t1] and [i = t2] with [t1], [t2] distinct cover set cases *)
  let trail_is_trivial_cases trail =
    let seq = Trail.to_seq trail in
    (* all boolean literals that express paths *)
    let relevant_cases = Sequence.filter_map BoolBox.as_case seq in
    (* are there two distinct incompatible cases in the trail? *)
    Sequence.diagonal relevant_cases
    |> Sequence.exists
      (fun (c1, c2) ->
         let res =
           not (List.length c1 = List.length c2) ||
           not (CCList.equal Cover_set.Case.equal c1 c2)
         in
         if res then (
           Util.debugf ~section 4
             "(@[<2>trail@ @[%a@]@ is trivial because of@ \
              {@[(@[%a@]),@,(@[%a@])}@]@])"
             (fun k->k C.pp_trail trail
                 (Util.pp_list Cover_set.Case.pp) c1
                 (Util.pp_list Cover_set.Case.pp )c2)
         );
         res)

  (* make trails with several lemmas in them trivial, so that we have to wait
     for a lemma to be proved before we can  use it to prove another lemma *)
  let trail_is_trivial_lemmas trail =
    let seq = Trail.to_seq trail in
    (* all boolean literals that express paths *)
    let relevant_cases =
      seq
      |> Sequence.filter_map
        (fun lit ->
           BoolBox.as_lemma lit
           |> CCOpt.map (fun lemma -> lemma, BoolLit.sign lit))
    in
    (* are there two distinct positive lemma literals in the trail? *)
    Sequence.diagonal relevant_cases
    |> Sequence.exists
      (fun ((c1,sign1), (c2,sign2)) ->
         let res = sign1 && sign2 && not (Cut_form.equal c1 c2) in
         if res then (
           Util.debugf ~section 4
             "(@[<2>trail@ @[%a@]@ is trivial because of lemmas@ \
              {@[(@[%a@]),@,(@[%a@])}@]@])"
             (fun k->k C.pp_trail trail Cut_form.pp c1 Cut_form.pp c2);
         );
         res)

  let new_clauses_from_lemmas_ : C.t list ref = ref []

  (* look whether, to prove the lemma, we need induction *)
  let on_lemma cut =
    let l = prove_lemma cut in
    if l<>[] then (
      Util.incr_stat stats_lemmas;
      new_clauses_from_lemmas_ := List.rev_append l !new_clauses_from_lemmas_;
    )

  (* return the list of new lemmas *)
  let inf_new_lemmas ~full:_ () =
    let l = !new_clauses_from_lemmas_ in
    new_clauses_from_lemmas_ := [];
    l

  let register () =
    Util.debug ~section 2 "register induction";
    let d = Env.flex_get k_ind_depth in
    Util.debugf ~section 2 "maximum induction depth: %d" (fun k->k d);
    Ind_cst.max_depth_ := d;
    Env.add_unary_inf "induction.ind" inf_prove_by_ind;
    Env.add_clause_conversion convert_statement;
    Env.add_is_trivial_trail trail_is_trivial_cases;
    if E.flex_get Avatar.k_simplify_trail then (
      Env.add_is_trivial_trail trail_is_trivial_lemmas;
    );
    Signal.on_every A.on_lemma on_lemma;
    Env.add_generate "ind.lemmas" inf_new_lemmas;
    ()
end

let enabled_ = ref true
let depth_ = ref !Ind_cst.max_depth_
let test_limit = ref Test_prop.default_limit
let limit_to_active = ref true
let coverset_depth = ref 1

(* if induction is enabled AND there are some inductive types,
   then perform some setup after typing, including setting the key
   [k_enable].
   It will update the parameters. *)
let post_typing_hook stmts state =
  (* only enable if there are inductive types *)
  let should_enable =
    CCVector.exists
      (fun st -> match Statement.view st with
         | Statement.Data _ -> true
         | _ -> false)
      stmts
  in
  if !enabled_ && should_enable then (
    Util.debug ~section 1 "Enable induction";
    state
    |> Flex_state.add k_enable true
    |> Flex_state.add k_ind_depth !depth_
    |> Flex_state.add k_test_limit !test_limit
    |> Flex_state.add k_limit_to_active !limit_to_active
    |> Flex_state.add k_coverset_depth !coverset_depth
    |> Flex_state.add Ctx.Key.lost_completeness true
  ) else Flex_state.add k_enable false state

(* if enabled: register the main functor, with inference rules, etc. *)
let env_action (module E : Env.S) =
  let is_enabled = E.flex_get k_enable in
  if is_enabled then (
    let (module A) = Avatar.get_env (module E) in
    (* XXX here we do not use E anymore, because we do not know
       that A.E = E. Therefore, it is simpler to use A.E. *)
    let module E = A.E in
    E.Ctx.lost_completeness ();
    E.Ctx.set_selection_fun Selection.no_select;
    let module M = Make(A.E)(A) in
    M.register ();
  )

let extension =
  Extensions.(
    {default with
       name="induction_simple";
       post_typing_actions=[post_typing_hook];
       env_actions=[env_action];
    })

let () =
  Params.add_opts
    [ "--induction", Options.switch_set true enabled_, " enable induction"
    ; "--no-induction", Options.switch_set false enabled_, " enable induction"
    ; "--induction-depth", Arg.Set_int depth_, " maximum depth of nested induction"
    ; "--ind-test-limit",
      Arg.Set_int test_limit,
      " set limit for property testing in induction"
    ; "--ind-only-active-pos", Arg.Set limit_to_active, " limit induction to active positions"
    ; "--no-ind-only-active-pos", Arg.Clear limit_to_active, " limit induction to active positions"
    ; "--ind-coverset-depth", Arg.Set_int coverset_depth, " coverset depth in induction"
    ]
