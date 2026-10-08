(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

module Cbor = CBOR.Simple

module Magic = struct
  let args = 0
  let head = 1
  let tyvar = 2
  let tycons = 3
  let name = 4
  let ty = 5
  let var = 6
  let tag = 7
  let ts = 8
  let db = 9
  let lam = 10
  let ctx = 11
  let body = 12
  let app = 13
  let eigen = 14
  let constant = 15
  let logic = 16
  let nominal = 17
  let kind = 18
  let problem = 19
  let left = 20
  let right = 21
  let used = 22
  let result = 23
  let success = 24
  let failure = 25
  let solution = 26
  let term = 27
end

module Immut = struct
  exception CborError of string

  type ty = Ty of ty list * aty

  and aty =
    | Tyvar of Term.tyvar
    | Tycons of Term.id * ty list

  type tyctx = (Term.id * ty) list

  type tm =
    | Var of Term.var
    | DB of int
    | Lam of tyctx * tm
    | App of tm * tm list

  let rec of_ty (ty : Term.ty) : ty =
    match Term.observe_ty ty with
    | Term.Ty (args, aty) ->
        let Ty (args', head) = of_aty aty in
        Ty (List.map of_ty args @ args', head)

  and of_aty (aty : Term.aty) : ty =
    match aty with
    | Term.Tygenvar v -> Ty ([], Tyvar v)
    | Term.Tycons (c, args) -> Ty ([], Tycons (c, List.map of_ty args))
    | Term.Typtr {contents = Term.TV v} -> Ty ([], Tyvar v)
    | Term.Typtr {contents = Term.TT t} -> of_ty t

  let of_tyctx (ctx : Term.tyctx) : tyctx =
    List.map (fun (id, ty) -> (id, of_ty ty)) ctx

  let rec to_ty (Ty (args, aty)) : Term.ty =
    Term.Ty (List.map to_ty args, to_aty aty)

  and to_aty (aty : aty) : Term.aty =
    match aty with
    | Tyvar v -> Term.Tygenvar v
    | Tycons (c, args) -> Term.Tycons (c, List.map to_ty args)

  let rec of_tm (tm : Term.term) : tm =
    match Term.observe (Term.hnorm tm) with
    | Term.Var v -> Var v
    | Term.DB i -> DB i
    | Term.Lam (ctx, body) -> Lam (of_tyctx ctx, of_tm body)
    | Term.App (head, args) -> App (of_tm head, List.map of_tm args)
    | Term.Susp _ -> assert false
    | Term.Ptr _ -> assert false

  let tag_to_magic = function
    | Term.Eigen -> Magic.eigen
    | Term.Constant -> Magic.constant
    | Term.Logic -> Magic.logic
    | Term.Nominal -> Magic.nominal

  let rec ty_to_cbor (Ty (args, aty)) : Cbor.t =
    `Map [
      `Int Magic.args, `Array (List.map ty_to_cbor args) ;
      `Int Magic.head, aty_to_cbor aty ;
    ]

  and aty_to_cbor (aty : aty) : Cbor.t =
    match aty with
    | Tyvar v -> `Map [ `Int Magic.tyvar, `Text v ]
    | Tycons (c, args) ->
        `Map [
          `Int Magic.tycons, `Text c ;
          `Int Magic.args, `Array (List.map ty_to_cbor args) ;
        ]

  let tyctx_to_cbor (ctx : tyctx) : Cbor.t =
    `Array (List.map (fun (name, ty) ->
        `Map [ `Int Magic.name, `Text name ; `Int Magic.ty, ty_to_cbor ty ]) ctx)

  let rec tm_to_cbor (tm : tm) : Cbor.t =
    match tm with
    | Var v ->
        `Map [
          `Int Magic.var, `Text v.name ;
          `Int Magic.tag, `Int (tag_to_magic v.tag) ;
          `Int Magic.ts, `Int v.ts ;
          `Int Magic.ty, ty_to_cbor (of_ty v.ty) ;
        ]
    | DB i -> `Map [ `Int Magic.db, `Int i ]
    | Lam (ctx, body) ->
        `Map [
          `Int Magic.lam, `Map [
            `Int Magic.ctx, tyctx_to_cbor ctx ;
            `Int Magic.body, tm_to_cbor body ;
          ] ;
        ]
    | App (head, args) ->
        `Map [
          `Int Magic.app, `Map [
            `Int Magic.head, tm_to_cbor head ;
            `Int Magic.args, `Array (List.map tm_to_cbor args) ;
          ] ;
        ]

  let cbor_error fmt =
    Printf.ksprintf (fun msg -> raise (CborError msg)) fmt

  let get_field key = function
    | `Map fields -> begin
        match List.assoc_opt (`Int key) fields with
        | Some cbor -> cbor
        | None -> cbor_error "missing field %d" key
      end
    | _ -> cbor_error "expected a map to read field %d from" key

  let string_of_cbor = function
    | `Text s -> s
    | _ -> cbor_error "expected a string"

  let int_of_cbor = function
    | `Int i -> i
    | _ -> cbor_error "expected an integer"

  let list_of_cbor f = function
    | `Array cs -> List.map f cs
    | _ -> cbor_error "expected an array"

  let tag_of_magic = function
    | n when n = Magic.eigen -> Term.Eigen
    | n when n = Magic.constant -> Term.Constant
    | n when n = Magic.logic -> Term.Logic
    | n when n = Magic.nominal -> Term.Nominal
    | n -> cbor_error "unknown variable tag %d" n

  let rec ty_of_cbor (cbor : Cbor.t) : ty =
    Ty (list_of_cbor ty_of_cbor (get_field Magic.args cbor),
        aty_of_cbor (get_field Magic.head cbor))

  and aty_of_cbor (cbor : Cbor.t) : aty =
    match cbor with
    | `Map fields when List.mem_assoc (`Int Magic.tyvar) fields ->
        Tyvar (string_of_cbor (List.assoc (`Int Magic.tyvar) fields))
    | `Map _ ->
        Tycons (string_of_cbor (get_field Magic.tycons cbor),
                list_of_cbor ty_of_cbor (get_field Magic.args cbor))
    | _ -> cbor_error "expected a map for a type"

  let tyctx_of_cbor (cbor : Cbor.t) : tyctx =
    list_of_cbor (fun entry ->
        (string_of_cbor (get_field Magic.name entry),
         ty_of_cbor (get_field Magic.ty entry)))
      cbor

  let rec tm_of_cbor (cbor : Cbor.t) : tm =
    match cbor with
    | `Map fields when List.mem_assoc (`Int Magic.var) fields ->
        let name = string_of_cbor (List.assoc (`Int Magic.var) fields) in
        let tag = tag_of_magic (int_of_cbor (List.assoc (`Int Magic.tag) fields)) in
        let ts = int_of_cbor (get_field Magic.ts cbor) in
        let ty = to_ty (ty_of_cbor (get_field Magic.ty cbor)) in
        Var (Term.term_to_var (Term.var tag name ts ty))
    | `Map fields when List.mem_assoc (`Int Magic.db) fields ->
        DB (int_of_cbor (List.assoc (`Int Magic.db) fields))
    | `Map fields when List.mem_assoc (`Int Magic.lam) fields ->
        let lam = List.assoc (`Int Magic.lam) fields in
        Lam (tyctx_of_cbor (get_field Magic.ctx lam),
             tm_of_cbor (get_field Magic.body lam))
    | `Map fields when List.mem_assoc (`Int Magic.app) fields ->
        let app = List.assoc (`Int Magic.app) fields in
        App (tm_of_cbor (get_field Magic.head app),
             list_of_cbor tm_of_cbor (get_field Magic.args app))
    | `Map _ -> cbor_error "unknown term constructor"
    | _ -> cbor_error "expected a map for a term"
end

type named_term = { name : string ; term : Immut.tm }

type outcome =
  | Success of named_term list
  | Failure of string

type record = {
  kind    : string ;
  left    : Immut.tm ;
  right   : Immut.tm ;
  used    : named_term list ;
  outcome : outcome ;
}

let records : record list ref = ref []
let outfile : string option ref = ref None

let set_output filename = outfile := Some filename

let add r = records := r :: !records

let cbor_of_named_term ~key t =
  `Map [ `Int key, `Text t.name ; `Int Magic.term, Immut.tm_to_cbor t.term ]

let cbor_of_record r =
  let base = [
    `Int Magic.kind, `Text r.kind ;
    `Int Magic.problem, `Map [
      `Int Magic.left, Immut.tm_to_cbor r.left ;
      `Int Magic.right, Immut.tm_to_cbor r.right ;
    ] ;
    `Int Magic.used, `Array (List.map (cbor_of_named_term ~key:Magic.name) r.used) ;
  ] in
  let outcome = match r.outcome with
    | Success sol ->
        [ `Int Magic.result, `Int Magic.success ;
          `Int Magic.solution, `Array (List.map (cbor_of_named_term ~key:Magic.var) sol) ]
    | Failure msg ->
        [ `Int Magic.result, `Int Magic.failure ;
          `Int Magic.failure, `Text msg ;
          `Int Magic.solution, `Array [] ]
  in
  `Map (base @ outcome)

let write () =
  match !outfile with
  | None -> ()
  | Some f ->
      let oc = open_out_bin f in
      let cbor = `Array (List.rev_map cbor_of_record !records) in
      output_string oc (Cbor.encode cbor) ;
      close_out oc

let () = if Term.log_unifications then at_exit write
