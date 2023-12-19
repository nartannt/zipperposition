(* This file is free software, part of Zipperposition. See file "license" for more details. *)

(** {1 Universally Quantified Conjunction of Clauses} *)

open Logtk
module Fmt = CCFormat
module T = Term

type var = Term.var
type term = Term.t
type clause = Literals.t
type form = clause list
type t = { vars : T.VarSet.t; cs : form }
type cut_form = t

let trivial = { cs = []; vars = T.VarSet.empty }

let make cs =
    if cs = [] then trivial
    else
      let vars = Iter.of_list cs |> Iter.flat_map Literals.Seq.vars |> T.VarSet.of_iter
      and cs = CCList.sort_uniq ~cmp:Literals.compare cs in
          { cs; vars }

let vars t = t.vars
let cs t = t.cs
let hash (f : t) : int = Hash.list Literals.hash f.cs
let equal f1 f2 : bool = CCList.equal Literals.equal f1.cs f2.cs
let compare f1 f2 = CCList.compare Literals.compare f1.cs f2.cs

let pp out (f : t) : unit =
    let pp_c = Literals.pp in
    let pp_body out () =
        match f.cs with
            | [ c ] -> pp_c out c
            | _ -> Fmt.fprintf out "@<1>∧{@[<hv>%a@]}" (Util.pp_list ~sep:"," pp_c) f.cs
    in
        if T.VarSet.is_empty f.vars then pp_body out ()
        else
          Fmt.fprintf out "(@[<2>forall %a.@ %a@])"
            (Util.pp_list ~sep:" " Type.pp_typed_var)
            (T.VarSet.to_list f.vars) pp_body ()

let to_string = Fmt.to_string pp

let pp_tstp out (f : t) : unit =
    let pp_c = Fmt.within "(" ")" Literals.pp_tstp in
    let pp_body out () =
        match f.cs with
            | [ c ] -> pp_c out c
            | _ -> Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" & " pp_c) f.cs
    in
        if T.VarSet.is_empty f.vars then pp_body out ()
        else
          Fmt.fprintf out "(@[<2>![%a]:@ (%a)@])" (Util.pp_list Type.TPTP.pp_typed_var)
            (T.VarSet.to_list f.vars) pp_body ()

let pp_zf out (f : t) : unit =
    let pp_c = Fmt.within "(" ")" Literals.pp_zf in
    let pp_body out () =
        match f.cs with
            | [ c ] -> pp_c out c
            | _ -> Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" && " pp_c) f.cs
    in
        if T.VarSet.is_empty f.vars then pp_body out ()
        else
          Fmt.fprintf out "(@[<2>forall %a.@ (%a)@])" (Util.pp_list Type.ZF.pp_typed_var)
            (T.VarSet.to_list f.vars) pp_body ()

let ind_vars t =
    vars t |> T.VarSet.to_list
    |> List.filter (fun v ->
           let ty = HVar.ty v in
               (* only do induction on variables of infinite types *)
               match Ind_ty.as_inductive_type ty with Some (ity, _) -> Ind_ty.is_recursive ity | None -> false)

let apply_subst renaming subst (f, sc) : t =
    let cs = List.map (fun lits -> Literals.apply_subst renaming subst (lits, sc)) f.cs in
        make cs

let subst1 (v : var) (t : term) (f : t) : t =
    let renaming = Subst.Renaming.create () in
    let subst = Subst.FO.bind Subst.empty ((v : var :> InnerTerm.t HVar.t), 0) (t, 1) in
        apply_subst renaming subst (f, 0)

(* find substitutions making [f1] and [f2] variants, if possible *)
let variant_ ~subst (f1, sc1) (f2, sc2) : _ Iter.t =
    Unif.unif_list_com ~size:`Same subst
      ~op:(fun subst c1 c2 k -> Literals.variant ~subst c1 c2 (fun (subst, _tags) -> k subst))
      (f1.cs, sc1) (f2.cs, sc2)

let are_variant f1 f2 : bool = not @@ Iter.is_empty @@ variant_ ~subst:Subst.empty (f1, 1) (f2, 0)

let normalize_form (f : form) : form =
    let module RW = Rewrite in
    let rec simplify c =
        let lit_abs = CCArray.find_idx Literal.is_absurd c in
            match lit_abs with
                | None -> c
                | Some (i, _) ->
                    let new_c = CCArray.except_idx c i |> Array.of_list in
                        simplify new_c
    in
    (* fixpoint of rewriting *)
    let rec normalize_up_to fuel (c : clause) : clause Iter.t =
        assert (fuel >= 0);
        if fuel = 0 then Iter.return c else normalize_step (fuel - 1) c
    and normalize_step fuel c =
        let progress = ref false in
        (* how to normalize a term/lit (with restricted resources) *)
        let rw_term t =
            let t', rules = RW.Term.normalize_term ~max_steps:10 t in
                if not (RW.Term.Rule_inst_set.is_empty rules) then progress := true;
                t'
        in
        let rw_terms c = Literals.map rw_term c
        and rw_clause c =
            match RW.Lit.normalize_clause c with
                | None -> [ c ]
                | Some (cs, _, _, _, _, _) ->
                    progress := true;
                    cs
        and rm_trivial = List.filter (fun c -> not (Literals.is_trivial c)) in
        let cs = c |> rw_terms |> rw_clause |> rm_trivial in
            if !progress then normalize_form fuel cs (* normalize each result recursively *)
            else (* done, just simplify *)
              Iter.of_list cs |> Iter.map simplify
    and normalize_form fuel (f : form) : clause Iter.t =
        Iter.of_list f |> Iter.flat_map (normalize_up_to fuel)
    in
        normalize_form 3 f |> Iter.to_rev_list

let normalize (f : t) : t = cs f |> normalize_form |> make

let to_s_form (f : t) =
    let module F = TypedSTerm.Form in
    (* convert all clauses with the same variable bindings *)
    let ctx = Term.Conv.create () in
    let l = List.map (Literals.Conv.to_s_form ~ctx) (cs f) in
        F.and_ l |> F.close_forall

module Pos = struct
  module P = Position

  let bad_pos f p = Util.invalid_argf "invalid pos `%a`@ in %a" P.pp p pp f

  let clause_at f p =
      match p with
          | P.Stop -> bad_pos f p
          | P.Arg (n, p') ->
              let cs = cs f in
                  if n < 0 || n >= List.length cs then bad_pos f p;
                  (List.nth cs n, p')
          | _ -> bad_pos f p

  let lit_at f p =
      let c, p = clause_at f p in
          Literals.Pos.lit_at c p

  let at f p : term =
      let lit, p = lit_at f p in
          Literal.Pos.at lit p

  let replace_many f m : t =
      let l = cs f in
          P.Map.fold
            (fun p by l ->
              let n, p_c = match p with P.Arg (n, p') -> (n, p') | _ -> assert false in
              let c = List.nth l n in
              let c' = Array.copy c in
                  Literals.Pos.replace c' ~at:p_c ~by;
                  CCList.set_at_idx n c' l)
            m l
          |> make

  let replace f ~at ~by = replace_many f (P.Map.singleton at by)
end

module Seq = struct
  let terms f = cs f |> Iter.of_list |> Iter.flat_map Literals.Seq.terms

  let terms_with_pos ?(subterms = true) f =
      cs f |> Iter.of_list |> Util.seq_zipi
      |> Iter.flat_map (fun (i, c) -> Iter.of_array_i c |> Iter.map (fun (j, lit) -> (i, j, lit)))
      |> Iter.flat_map (fun (i, j, lit) ->
             let position = Position.(arg i @@ arg j @@ stop) in
                 Literal.fold_terms lit ~position ~ord:Ordering.none ~which:`All ~vars:true ~subterms)
end

module FV_tbl (X : Map.OrderedType) = struct
  type value = X.t

  (* approximation here, we represent it as a clause, losing the
         boolean structure. monotonicity w.r.t features should still apply *)
  let to_lits (f : cut_form) = cs f |> Iter.of_list |> Iter.flat_map_l Literals.to_form

  (* index for lemmas, to ensure α-equivalent lemmas have the same lit *)
  module FV = FV_tree.Make (struct
    type t = cut_form * X.t

    let compare (l1, v1) (l2, v2) =
        let open CCOrd.Infix in
        compare l1 l2 <?> (X.compare, v1, v2)

    let to_lits (l, _) = to_lits l
    let labels _ = Util.Int_set.empty
  end)

  type t = { mutable fv : FV.t }

  let create () = { fv = FV.empty () }
  let add t k v = t.fv <- FV.add t.fv (k, v)

  let get t k =
      FV.retrieve_alpha_equiv t.fv (to_lits k) Util.Int_set.empty
      |> Iter.find_map (fun (k', v) -> if are_variant k k' then Some v else None)

  let mem t k = get t k |> CCOpt.is_some
  let to_iter t = FV.iter t.fv
end
