(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2016  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Syntax of explicit LF *)

type id = string

type lfkind =
  | Type
  | Kpi    of lfkind abs
  | Karrow of lftype * lfkind

and lftype =
  | Atom   of id * lfterm list
  | Pi     of lftype abs
  | Arrow  of lftype * lftype

and lfterm =
  | Const  of id
  | Idx    of int
  | App    of lfterm * lfterm
  | Lam    of lfterm abs

and 'a abs = id * lftype * 'a

and lfsub =
  | Shift  of int
  | Cons   of lfsub * lfterm

and lfctx = (id * lftype) list

type lfsig =
  | Empty
  | Typedecl  of lfsig * id * lfkind
  | Constdecl of lfsig * id * lftype

type lferror =
  | Redeclaration of lfsig * id
  | No_sugh_typedecl of id
  | No_such_constdecl of id
  | Kind_check of lfsig * lfctx * lfterm list * lfkind
  | Type_check_arg of lfsig * lfctx * lftype * lftype
  | Infer_type_target of lfsig * lfctx * lftype * lfterm
  | Type_equality of lfsig * lfctx * lftype * lftype
  | Term_equality of lfsig * lfctx * lfterm * lfterm

exception LF_failure of lferror

let lf_failwith err = raise (LF_failure err)

let rec subst_kind ss k =
  match k with
  | Type -> Type
  | Karrow (a, k) ->
      let a = subst_type ss a in
      let k = subst_kind ss k in
      Karrow (a, k)
  | Kpi (x, a, k) ->
      let a = subst_type ss a in
      let ss = bump ss in
      let k = subst_kind ss k in
      Kpi (x, a, k)

and subst_type ss a =
  match a with
  | Atom (a, ts) ->
      let ts = List.map (subst_term ss) ts in
      Atom (a, ts)
  | Arrow (a, b) ->
      let a = subst_type ss a in
      let b = subst_type ss b in
      Arrow (a, b)
  | Pi (x, a, b) ->
      let a = subst_type ss a in
      let ss = bump ss in
      let b = subst_type ss b in
      Pi (x, a, b)

and subst_term ss t =
  match t with
  | Idx n -> subst_idx ss n
  | Const k -> Const k
  | App (s, t) ->
      let s = subst_term ss s in
      let t = subst_term ss t in
      apply s t
  | Lam (x, a, t) ->
      let a = subst_type ss a in
      let ss = bump ss in
      let t = subst_term ss t in
      Lam (x, a, t)

and apply s t =
  match s with
  | Lam (_, _, s) ->
      subst_term (Cons (Shift 0, t)) s
  | _ ->
      App (s, t)

and subst_idx ss n =
  match ss, n with
  | Shift j, _ -> Idx (j + n)
  | Cons (_, t), 0 -> t
  | Cons (ss, _), _ -> subst_idx ss (n - 1)

and compose ss tt =
  match ss, tt with
  | Shift 0, _ -> tt
  | _, Shift 0 -> ss
  | Shift j, Shift k -> Shift (j + k)
  | Cons (ss, _), Shift k -> compose ss (Shift (k - 1))
  | ss, Cons (tt, t) -> Cons (compose ss tt, subst_term ss t)

and bump ?(n = 0) ss =
  match ss with
  | Shift 0 -> Shift 0
  | ss -> bump_tail (compose ss (Shift n)) n

and bump_tail ss n =
  match n with
  | 0 -> ss
  | n ->
      let ss = Cons (ss, Idx n) in
      bump_tail ss (n - 1)

(* assumes: check_wfsig sg *)
let rec is_declared sg id =
  match sg with
  | Empty -> false
  | Typedecl (sg, x, _)
  | Constdecl (sg, x, _) ->
      x = id || is_declared sg id

(* assumes: check_wfsig sg *)
and lookup_typedecl sg id =
  match sg with
  | Typedecl (_, x, k) when x = id -> k
  | Typedecl (sg, _, _)
  | Constdecl (sg, _, _) ->
      lookup_typedecl sg id
  | Empty -> lf_failwith (No_sugh_typedecl id)

(* assumes: check_wfsig sg *)
and lookup_constdecl sg id =
  match sg with
  | Constdecl (_, x, a) when x = id -> a
  | Typedecl (sg, _, _)
  | Constdecl (sg, _, _) ->
      lookup_constdecl sg id
  | Empty -> lf_failwith (No_such_constdecl id)

(* assumes: nothing *)
let rec check_wfsig sg =
  match sg with
  | Empty -> ()
  | Typedecl (sg, a, k) ->
      if is_declared sg a then
        lf_failwith (Redeclaration (sg, a)) ;
      check_wfkind sg [] k
  | Constdecl (sg, c, a) ->
      if is_declared sg c then
        lf_failwith (Redeclaration (sg, c)) ;
      check_wftype sg [] a

(* assumes: check_wfsig sg *)
and check_wfctx sg cx =
  match cx with
  | [] -> ()
  | (x, a) :: cx ->
      (* these two must be done in the opposite order for the
         invariants, but that would not be tail-recursive. *)
      check_wftype sg cx a ;
      check_wfctx sg cx

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_wfkind sg cx k =
  match k with
  | Type -> ()
  | Karrow (a, k) ->
      check_wftype sg cx a ;
      check_wfkind sg cx k
  | Kpi (x, a, k) ->
      check_wftype sg cx a ;
      let cx = (x, a) :: cx in
      check_wfkind sg cx k

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_wftype sg cx a =
  match a with
  | Atom (a, ts) ->
      let k = lookup_typedecl sg a in
      check_kargs sg cx ts k
  | Arrow (a, b) ->
      check_wftype sg cx a ;
      check_wftype sg cx b
  | Pi (x, a, b) ->
      check_wftype sg cx a ;
      check_wftype sg ((x, a) :: cx) b

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_kargs sg cx ts k =
  match ts, k with
  | [], Type -> ()
  | (t :: ts), Karrow (a, k) ->
      check_type sg cx t a ;
      check_kargs sg cx ts k
  | (t :: ts), Kpi (x, a, k) ->
      check_type sg cx t a ;
      let k = subst_kind (Cons (Shift 0, t)) k in
      check_kargs sg cx ts k
  | _, _ ->
      lf_failwith (Kind_check (sg, cx, ts, k))

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_type sg cx t a =
  match t with
  | Lam (x, b, t) ->
      let a = match a with
        | Arrow (b1, a) ->
            check_type_eq sg cx b b1 ; a
        | Pi (_, b1, a) ->
            check_type_eq sg cx b b1 ; a
        | _ ->
            lf_failwith (Type_check_arg (sg, cx, b, a))
      in
      check_type sg ((x, b) :: cx) t a
  | _ ->
      let a1 = infer_type sg cx t in
      check_type_eq sg cx a a1

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and infer_type sg cx t =
  match t with
  | Const c -> lookup_constdecl sg c
  | Idx n -> snd (List.nth cx n)
  | App (s, t) ->
      let a = infer_type sg cx s in
      infer_type_target sg cx a t
  | Lam _ ->
      invalid_arg "lambda expressions are not atomic"

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and infer_type_target sg cx a t =
  match a with
  | Arrow (a, b) ->
      check_type sg cx t a ; b
  | Pi (x, a, b) ->
      check_type sg cx t a ;
      subst_type (Cons (Shift 0, t)) b
  | _ ->
      lf_failwith (Infer_type_target (sg, cx, a, t))

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_type_eq sg cx a0 b0 =
  match a0, b0 with
  | Atom (a, a_args), Atom (b, b_args) ->
      if a <> b then
        lf_failwith (Type_equality (sg, cx, a0, b0)) ;
      if List.length a_args <> List.length b_args then
        assert false ;
      List.iter2 (check_term_eq sg cx) a_args b_args
  | Arrow (a1, a2), Arrow (b1, b2)
  | Pi (_, a1, a2), Pi (_, b1, b2) ->
      check_type_eq sg cx a1 b1 ;
      check_type_eq sg cx a2 b2
  | _ ->
      lf_failwith (Type_equality (sg, cx, a0, b0))

(* assumes: check_wfsig sg && check_wfctx sg cx *)
and check_term_eq sg cx s0 t0 =
  match s0, t0 with
  | Const c, Const d ->
      if c <> d then
        lf_failwith (Term_equality (sg, cx, s0, t0))
  | Idx m, Idx n ->
      if m <> n then
        lf_failwith (Term_equality (sg, cx, s0, t0))
  | App (s1, s2), App (t1, t2) ->
      check_term_eq sg cx s1 t1 ;
      check_term_eq sg cx s2 t2
  | Lam (x, a1, s1), Lam (y, b1, t1) ->
      check_type_eq sg cx a1 b1 ;
      check_term_eq sg ((x, a1) :: cx) s1 t1
  | Lam (_, _, s1), _ ->
      check_term_eq sg cx s1 (eta_expanded_body t0)
  | _, Lam (_, _, t1) ->
      check_term_eq sg cx (eta_expanded_body s0) t1
  | _ ->
      lf_failwith (Term_equality (sg, cx, s0, t0))

and eta_expanded_body s =
  apply (subst_term (Shift 1) s) (Idx 1)
