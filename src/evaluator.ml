
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

(** {1 Evaluation of terms and formulas}
This module provides utilities to register functions to evaluate terms
on a per-symbol basis. Each symbol can have its own evaluator, that is
called to normalize terms whose head is the symbol. That is especially
handy for arithmetic, where there are many distinct interpreted symbols.
*)

(** {2 Signature of evaluator for some terms} *)

module type S = sig
  type term

  type eval_fun = tyargs:Type.t list -> Symbol.t -> term list -> term option
    (** An  evaluation function takes a symbol application, and a list of
        arguments, and can decide to return a new term based on that.
        If it returns None, it means that the term is already evaluated. *)

  type t
    (** An evaluator. It maps symbols to evaluators *)

  val create : unit -> t
    (** New evaluator *)

  val copy : t -> t
    (** Copy the evaluator *)

  val register : t -> Symbol.t -> eval_fun -> unit
    (** Add an evaluation function to the evaluator. If another function
        was already registered *)

  val register_list : t -> (Symbol.t * eval_fun) list -> unit

  val interpreted : t -> Symbol.t -> bool
    (** Is there a registered evaluation function for this symbol? *)

  val eval_head : t -> term -> term
    (** Evaluate the term's root, but not subterms *)

  val eval : t -> term -> term
    (** Recursively evaluate the term *)
end

module FO = struct
  module T = FOTerm
  type term = T.t

  type eval_fun = tyargs:Type.t list -> Symbol.t -> term list -> term option

  type t = eval_fun Symbol.Tbl.t

  let create () = Symbol.Tbl.create 13

  let copy = Symbol.Tbl.copy

  let register t s f = Symbol.Tbl.replace t s f

  let register_list t l =
    List.iter (fun (s, f) -> register t s f) l

  let interpreted t s = Symbol.Tbl.mem t s

  (* non-recursive evaluation *)
  let rec eval_head ev t = match t.T.term with
    | T.Var _
    | T.BoundVar _ -> t
    | T.Node (s, tyargs, l) ->
      let t' =
        try
          (* evaluate constant *)
          let f = Symbol.Tbl.find ev s in
          f ~tyargs s l
        with Not_found -> None
      in
      begin match t' with
        | None -> t
        | Some t' -> eval_head ev t'
      end

  (* recursive evaluation *)
  let rec eval ev t = match t.T.term with
    | T.Var _
    | T.BoundVar _ -> t
    | T.Node (s, tyargs, []) ->
      eval_head ev t
    | T.Node (s, tyargs, l) ->
      (* evaluate subterms, then the term itself *)
      let l' = List.map (eval ev) l in
      let t' = 
        try
          let f = Symbol.Tbl.find ev s in
          f ~tyargs s l'
        with
        | Not_found -> None
        | Type.Error _ as e ->
          Util.debug 0 "type error when evaluating %a" T.pp t;
          raise e
      in
      begin match t' with
        | None -> T.mk_node ~tyargs s l'  (* replace *)
        | Some t' -> eval ev t'
      end

  let eval_form ev f =
    FOFormula.map_depth (fun _ t -> eval ev t) f

  let app ?tyargs ev s l = eval_head ev (T.mk_node ?tyargs s l)

  module S = Symbol

  (* helpers *)

  let _unary l = match l with
    | [{T.term=T.Node(s,_,l')}] -> `Unary (s, l')
    | _ -> `None
  let _binary l = match l with
    | [{T.term=T.Node(s1,tys1,l1')}; {T.term=T.Node(s2,tys2,l2')}] ->
      `Binary (s1, tys1, l1', s2, tys2, l2')
    | _ -> `None

  let _ev_uminus ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.uminus n))  (* - n ----> -n *)
    | `Unary (s', [t']) when S.eq s' S.Arith.uminus ->
      Some t'  (* -(-t) --> t *)
    | _ -> None

  let _ev_floor ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.floor n))
    | _ -> None

  let _ev_ceiling ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.ceiling n))
    | _ -> None

  let _ev_round ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.round n))
    | _ -> None

  let _ev_truncate ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.truncate n))
    | _ -> None

  let _ev_is_int ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (if S.is_int n then T.true_term else T.false_term)
    | _ -> None

  let _ev_is_rat ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (if S.is_rat n then T.true_term else T.false_term)
    | _ -> None

  let _ev_is_real ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (if S.is_real n then T.true_term else T.false_term)
    | _ -> None

  let _ev_to_int ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.to_int n))
    | _ -> None

  let _ev_to_rat ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.to_rat n))
    | _ -> None

  let _ev_to_real ~tyargs s l = match _unary l with
    | `Unary (n, []) when S.is_numeric n ->
      Some (T.mk_const (S.Arith.Op.to_real n))
    | _ -> None

  let _ev_sum ~tyargs _ l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.sum n1 n2))
    | `Binary (n1, _, [], n2, tys2, l2) when S.Arith.is_zero n1 ->
      Some (T.mk_node ~tyargs:tys2 n2 l2) (* 0+x --> x *)
    | `Binary (n1, tys1, l1, n2, _, []) when S.Arith.is_zero n2 ->
      Some (T.mk_node ~tyargs:tys1 n1 l1) (* x+0 --> x *)
    | _ ->
      begin match l with
      | [t1; t2] when t1.T.tag > t2.T.tag ->
        (* AC-normalization *)
        Some (T.mk_node ~tyargs S.Arith.sum [t2; t1])
      | _ -> None
      end

  let mk_sum ~tyargs l =
    match _ev_sum ~tyargs S.Arith.sum l with
    | None -> T.mk_node ~tyargs S.Arith.sum l
    | Some t' -> t'

  let _ev_difference ~tyargs _ l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.difference n1 n2))
    | `Binary (n1, _, [], n2, tys2, l2) when S.Arith.is_zero n1 ->
      Some (T.mk_node ~tyargs S.Arith.uminus [T.mk_node ~tyargs:tys2 n2 l2])  (* 0-x --> -x *)
    | `Binary (n1, tys1, l1, n2, _, []) when S.Arith.is_zero n2 ->
      Some (T.mk_node ~tyargs:tys1 n1 l1)  (* x-0 ---> x *)
    | _ -> None

  let mk_difference ~tyargs l =
    match _ev_difference ~tyargs S.Arith.difference l with
    | None -> T.mk_node ~tyargs S.Arith.difference l
    | Some t' -> t'

  let rec _ev_product ~tyargs _ l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.product n1 n2))
    | `Binary (n1, [], [], n2, _, l2) when S.Arith.is_zero n1 ->
      Some (T.mk_const n1) (* 0*x --> 0 *)
    | `Binary (n1, _, l1, n2, [], []) when S.Arith.is_zero n2 ->
      Some (T.mk_const n2)  (* x*0 --> 0 *)
    | `Binary (n1, _, [], n2, tys2, l2) when S.Arith.is_one n1 ->
      Some (T.mk_node ~tyargs:tys2 n2 l2) (* 1*x --> x *)
    | `Binary (n1, tys1, l1, n2, _, []) when S.Arith.is_one n2 ->
      Some (T.mk_node ~tyargs:tys1 n1 l1) (* x*1 --> x *)
    | _ ->
      begin match l with
      | [{T.term=T.Node (S.Const ("$sum",_), _, [a;b])}; c]
      | [c; {T.term=T.Node (S.Const ("$sum",_), _, [a;b])}] ->
        (* distributivity over sum *)
        Some (mk_sum ~tyargs
          [ mk_product ~tyargs [a; c]
          ; mk_product ~tyargs [b; c]
          ])
      | [{T.term=T.Node (S.Const ("$difference",_), _, [a;b])}; c]
      | [c; {T.term=T.Node (S.Const ("$difference",_), _, [a;b])}] ->
        (* distributivity over difference *)
        Some (mk_difference ~tyargs
          [ mk_product ~tyargs [a; c]
          ; mk_product ~tyargs [b; c]
          ])
      | [t1; t2] when t1.T.tag > t2.T.tag ->
        (* AC-normalization *)
        Some (T.mk_node ~tyargs S.Arith.product [t2; t1])
      | _ -> None
      end
  and mk_product ~tyargs l =
    match _ev_product ~tyargs S.Arith.product l with
    | None -> T.mk_node ~tyargs S.Arith.product l
    | Some t' -> t'

  let _ev_quotient ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      begin try
        Some (T.mk_const ~tyargs (S.Arith.Op.quotient n1 n2))
      with Division_by_zero -> None
      end
    | `Binary (n1, tys1, l1, n2, _, []) when S.Arith.is_one n2 ->
      Some (T.mk_node ~tyargs:tys1 n1 l1)
    | _ -> None

  let _ev_quotient_e ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.quotient_e n1 n2))
    | _ -> None

  let _ev_quotient_f ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.quotient_f n1 n2))
    | _ -> None

  let _ev_quotient_t ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.quotient_t n1 n2))
    | _ -> None

  let _ev_remainder_e ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.remainder_e n1 n2))
    | _ -> None

  let _ev_remainder_f ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.remainder_f n1 n2))
    | _ -> None

  let _ev_remainder_t ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (T.mk_const (S.Arith.Op.remainder_t n1 n2))
    | _ -> None

  let _ev_less ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (if S.Arith.Op.less n1 n2 then T.true_term else T.false_term)
    | _ -> None

  let _ev_lesseq ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (if S.Arith.Op.lesseq n1 n2 then T.true_term else T.false_term)
    | _ -> None

  let _ev_greater ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (if S.Arith.Op.greater n1 n2 then T.true_term else T.false_term)
    | _ -> None

  let _ev_greatereq ~tyargs s l = match _binary l with
    | `Binary (n1, _, [], n2, _, []) when S.is_numeric n1 && S.is_numeric n2 ->
      Some (if S.Arith.Op.greatereq n1 n2 then T.true_term else T.false_term)
    | _ -> None

  let arith =
    [ S.Arith.uminus, _ev_uminus
    ; S.Arith.floor, _ev_floor
    ; S.Arith.ceiling, _ev_ceiling
    ; S.Arith.round, _ev_round
    ; S.Arith.truncate, _ev_truncate
    ; S.Arith.is_int, _ev_is_int
    ; S.Arith.is_rat, _ev_is_rat
    ; S.Arith.is_real, _ev_is_real
    ; S.Arith.to_int, _ev_to_int
    ; S.Arith.to_rat, _ev_to_rat
    ; S.Arith.to_real, _ev_to_real
    ; S.Arith.sum, _ev_sum
    ; S.Arith.difference, _ev_difference
    ; S.Arith.product, _ev_product
    ; S.Arith.quotient, _ev_quotient
    ; S.Arith.quotient_e, _ev_quotient_e
    ; S.Arith.quotient_f, _ev_quotient_f
    ; S.Arith.quotient_t, _ev_quotient_t
    ; S.Arith.remainder_e, _ev_remainder_e
    ; S.Arith.remainder_f, _ev_remainder_f
    ; S.Arith.remainder_t, _ev_remainder_t
    ; S.Arith.less, _ev_less
    ; S.Arith.lesseq, _ev_lesseq
    ; S.Arith.greater, _ev_greater
    ; S.Arith.greatereq, _ev_greatereq
    ]

  let with_arith ev =
    register_list ev arith
end
