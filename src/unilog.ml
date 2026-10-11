(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

module Immut = struct
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
end

type record = {
  kind  : string ;
  left  : Immut.tm ;
  right : Immut.tm ;
}

let records : record list ref = ref []
let outfile : string option ref = ref None
let origin : string ref = ref ""

let set_output ~origin:o filename =
  outfile := Some filename ;
  origin := o

let add r = records := r :: !records

(* The live Abella signature is supplied by the driver (abella.ml) to
   avoid a module dependency cycle through [Typing].  Each callback
   answers with [None] for names not in the signature. *)

let sig_tycon : (string -> int option) ref = ref (fun _ -> None)
let sig_const : (string -> Immut.ty option) ref = ref (fun _ -> None)

let set_lookup ~tycon ~const =
  sig_tycon := tycon ;
  sig_const := const

(* Rebella name mangling.  Rebella identifiers are lowercase for declared
   names and uppercase for type variables, over the character set
   [A-Za-z0-9_'-~]; a handful of words are reserved.  Abella names such
   as [::], [=>], or [?1] are not legal, so they are encoded with [_xx]
   hex escapes, with a fresh suffix on collision. *)

let is_lower c = c >= 'a' && c <= 'z'
let is_upper c = c >= 'A' && c <= 'Z'
let is_digit c = c >= '0' && c <= '9'

let is_ident_char c =
  is_lower c || is_upper c || is_digit c ||
  c = '-' || c = '_' || c = '\'' || c = '~'

let reserved =
  [ "type" ; "basic" ; "const" ; "unify" ; "left-unify" ; "right-unify" ]

let string_for_all f s =
  let ok = ref true in
  String.iter (fun c -> if not (f c) then ok := false) s ;
  !ok

let encode_char buf c =
  if is_ident_char c then Buffer.add_char buf c
  else Buffer.add_string buf (Printf.sprintf "_%02x" (Char.code c))

let sanitize_lower name =
  let buf = Buffer.create (String.length name + 4) in
  String.iter (encode_char buf) name ;
  let s = Buffer.contents buf in
  let s = if s = "" then "x" else s in
  let s =
    if is_lower s.[0] then s
    else if is_upper s.[0] then
      String.mapi (fun i c -> if i = 0 then Char.lowercase_ascii c else c) s
    else "c" ^ s
  in
  if List.mem s reserved then s ^ "_0" else s

let sanitize_upper name =
  let buf = Buffer.create (String.length name + 4) in
  String.iter (encode_char buf) name ;
  let s = Buffer.contents buf in
  let s = if s = "" then "A" else s in
  if is_upper s.[0] then s
  else if is_lower s.[0] then
    String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) s
  else "T" ^ s

let is_legal_lower name =
  String.length name > 0 && is_lower name.[0] &&
  string_for_all is_ident_char name && not (List.mem name reserved)

let is_legal_upper name =
  String.length name > 0 && is_upper name.[0] &&
  string_for_all is_ident_char name

let build_map ~legal ~sanitize names =
  let tbl = Hashtbl.create 32 in
  let used = Hashtbl.create 32 in
  List.iter begin fun original ->
    let base = if legal original then original else sanitize original in
    let rec fresh i =
      let cand = if i = 0 then base else Printf.sprintf "%s_%d" base i in
      if Hashtbl.mem used cand then fresh (i + 1) else cand
    in
    let name = fresh 0 in
    Hashtbl.add used name () ;
    Hashtbl.add tbl original name
  end names ;
  tbl

let const_map = Hashtbl.create 32
let tycon_map = Hashtbl.create 32
let tyvar_map = Hashtbl.create 32
let const_surface = Hashtbl.create 32

let install src dst =
  Hashtbl.reset dst ;
  Hashtbl.iter (fun k v -> Hashtbl.replace dst k v) src

let tycon_name c =
  match Hashtbl.find_opt tycon_map c with
  | Some n -> n
  | None -> sanitize_lower c

let const_name c =
  match Hashtbl.find_opt const_map c with
  | Some n -> n
  | None -> sanitize_lower c

let rec ren_ty (Immut.Ty (args, aty)) =
  Immut.Ty (List.map ren_ty args, ren_aty aty)

and ren_aty = function
  | Immut.Tyvar v ->
      let v = match Hashtbl.find_opt tyvar_map v with
        | Some n -> n
        | None -> sanitize_upper v
      in
      Immut.Tyvar v
  | Immut.Tycons (c, args) -> Immut.Tycons (tycon_name c, List.map ren_ty args)

let render_ty ty =
  Term.ty_to_string (Immut.to_ty (ren_ty ty))

type rctx = {
  mutable binders : string list ;
  vars          : (string, string) Hashtbl.t ;
  vars_used     : (string, unit) Hashtbl.t ;
  nominals      : (string, int) Hashtbl.t ;
  mutable next_nominal : int ;
  mutable used_binders : string list ;
}

let tag_key tag name =
  let p = match tag with
    | Term.Logic -> "l" | Term.Eigen -> "e" | _ -> "v"
  in
  p ^ name

let var_base rctx tag name =
  let key = tag_key tag name in
  match Hashtbl.find_opt rctx.vars key with
  | Some b -> b
  | None ->
      let base = sanitize_upper name in
      let rec fresh i =
        let cand = if i = 0 then base else Printf.sprintf "%s_%d" base i in
        if Hashtbl.mem rctx.vars_used cand then fresh (i + 1) else cand
      in
      let b = fresh 0 in
      Hashtbl.add rctx.vars key b ;
      Hashtbl.add rctx.vars_used b () ;
      b

let binder_candidate i =
  match i with
  | 0 -> "x"
  | 1 -> "y"
  | 2 -> "z"
  | _ -> "x" ^ string_of_int i

let fresh_binder rctx =
  let rec find i =
    let c = binder_candidate i in
    if List.mem c rctx.used_binders
       || List.mem c reserved
       || Hashtbl.mem const_surface c
    then find (i + 1)
    else c
  in
  let b = find 0 in
  rctx.used_binders <- b :: rctx.used_binders ;
  b

let rec render rctx (tm : Immut.tm) : string =
  match tm with
  | Immut.Var v -> render_var rctx v
  | Immut.DB i -> render_db rctx i
  | Immut.Lam (ctx, body) -> render_lam rctx ctx body
  | Immut.App (head, args) -> render_app rctx head args

and render_var rctx v =
  match v.Term.tag with
  | Term.Constant -> const_name v.Term.name
  | Term.Logic -> "?" ^ var_base rctx Term.Logic v.Term.name
  | Term.Eigen -> "_" ^ var_base rctx Term.Eigen v.Term.name
  | Term.Nominal ->
      let n = match Hashtbl.find_opt rctx.nominals v.Term.name with
        | Some n -> n
        | None ->
            let n = rctx.next_nominal in
            rctx.next_nominal <- n + 1 ;
            Hashtbl.add rctx.nominals v.Term.name n ;
            n
      in
      "#" ^ string_of_int n

and render_db rctx i =
  match List.nth_opt rctx.binders (i - 1) with
  | Some b -> b
  | None -> "__" ^ string_of_int (i - 1)

and render_lam rctx ctx body =
  let old = rctx.binders in
  let names = List.map (fun _ -> fresh_binder rctx) ctx in
  rctx.binders <- List.rev names @ old ;
  let rec build ctx names =
    match ctx, names with
    | [], [] -> render rctx body
    | (_, ty) :: ctx, n :: names ->
        Printf.sprintf "(%s : %s) \\ %s" n (render_ty ty) (build ctx names)
    | _ -> assert false
  in
  let result = build ctx names in
  rctx.binders <- old ;
  result

and render_atom rctx tm =
  match tm with
  | Immut.Var _ | Immut.DB _ -> render rctx tm
  | Immut.Lam _ | Immut.App _ -> "(" ^ render rctx tm ^ ")"

and render_app rctx head args =
  let h = render_atom rctx head in
  String.concat " " (h :: List.map (render_atom rctx) args)

let render_record r =
  let rctx = {
    binders = [] ;
    vars = Hashtbl.create 8 ;
    vars_used = Hashtbl.create 8 ;
    nominals = Hashtbl.create 8 ;
    next_nominal = 0 ;
    used_binders = [] ;
  } in
  let cmd = if r.kind = "right" then "right-unify" else "left-unify" in
  Printf.sprintf "%s %s = %s."
    cmd (render rctx r.left) (render rctx r.right)

let collect records =
  let consts = ref Term.Iset.empty in
  let tycons = ref Term.Iset.empty in
  let tyvars = ref Term.Iset.empty in
  let arities = Hashtbl.create 32 in
  let const_types = Hashtbl.create 32 in
  let rec walk_tm = function
    | Immut.Var v ->
        if v.Term.tag = Term.Constant then begin
          consts := Term.Iset.add v.Term.name !consts ;
          if not (Hashtbl.mem const_types v.Term.name) then
            Hashtbl.add const_types v.Term.name (Immut.of_ty v.Term.ty)
        end ;
        walk_ty (Immut.of_ty v.Term.ty)
    | Immut.DB _ -> ()
    | Immut.Lam (ctx, body) ->
        List.iter (fun (_, ty) -> walk_ty ty) ctx ;
        walk_tm body
    | Immut.App (head, args) ->
        walk_tm head ;
        List.iter walk_tm args
  and walk_ty (Immut.Ty (args, aty)) =
    List.iter walk_ty args ;
    match aty with
    | Immut.Tyvar v -> tyvars := Term.Iset.add v !tyvars
    | Immut.Tycons (c, args) ->
        let n = List.length args in
        let prev = match Hashtbl.find_opt arities c with Some m -> m | None -> 0 in
        if n > prev then Hashtbl.replace arities c n ;
        tycons := Term.Iset.add c !tycons ;
        List.iter walk_ty args
  in
  List.iter (fun r -> walk_tm r.left ; walk_tm r.right) records ;
  Term.Iset.iter begin fun c ->
    match !sig_const c with
    | Some ty -> walk_ty ty
    | None -> ()
  end !consts ;
  (!consts, !tycons, !tyvars, arities, const_types)

let tycon_arity arities c =
  match !sig_tycon c with
  | Some n -> n
  | None -> (match Hashtbl.find_opt arities c with Some n -> n | None -> 0)

let const_decl_ty const_types c =
  match !sig_const c with
  | Some ty -> ty
  | None ->
      (match Hashtbl.find_opt const_types c with
       | Some ty -> ty
       | None -> Immut.Ty ([], Immut.Tycons ("o", [])))

let write () =
  match !outfile with
  | None -> ()
  | Some f ->
      let all = List.rev !records in
      let records =
        List.filter (fun r -> r.kind = "right" || r.kind = "left") all in
      let consts, tycons, tyvars, arities, const_types = collect records in
      install
        (build_map ~legal:is_legal_lower ~sanitize:sanitize_lower
           (Term.Iset.elements consts))
        const_map ;
      install
        (build_map ~legal:is_legal_lower ~sanitize:sanitize_lower
           (Term.Iset.elements tycons))
        tycon_map ;
      install
        (build_map ~legal:is_legal_upper ~sanitize:sanitize_upper
           (Term.Iset.elements tyvars))
        tyvar_map ;
      Hashtbl.reset const_surface ;
      Hashtbl.iter (fun _ v -> Hashtbl.replace const_surface v ()) const_map ;
      let buf = Buffer.create 4096 in
      Buffer.add_string buf (Printf.sprintf "%% Generated from %s.\n" !origin) ;
      if records = [] then
        Buffer.add_string buf "% No unification problems were generated.\n"
      else begin
        Buffer.add_string buf
          (Printf.sprintf "%% %d unification problem(s).\n" (List.length records)) ;
        List.iter begin fun c ->
          let arity = tycon_arity arities c in
          let kind = String.concat " -> " (List.init (arity + 1) (fun _ -> "type")) in
          Buffer.add_string buf
            (Printf.sprintf "basic %s : %s.\n" (tycon_name c) kind)
        end (Term.Iset.elements tycons) ;
        Buffer.add_char buf '\n' ;
        List.iter begin fun c ->
          Buffer.add_string buf
            (Printf.sprintf "const %s : %s.\n"
               (const_name c) (render_ty (const_decl_ty const_types c)))
        end (Term.Iset.elements consts) ;
        Buffer.add_char buf '\n' ;
        List.iter (fun r -> Buffer.add_string buf (render_record r ^ "\n")) records
      end ;
      let oc = open_out_bin f in
      output_string oc (Buffer.contents buf) ;
      close_out oc

let () = at_exit write
