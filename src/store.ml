(****************************************************************************)
(* Copyright (C) 2014 INRIA                                                 *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Term
open Extensions

type pty = Poly of string list * ty
let pty_of_ty ty = Poly ([], ty)
let ty_of_pty = function
  | Poly ([], ty) -> ty
  | _ -> failwith "unpty: type is polymorphic"

module Ty = struct
  let o      = tybase "o"
  let olist  = tybase "olist"
  let prop   = tybase "prop"
end

type const = {
  cid   : string ;
  pty   : pty ;
  term  : term ;
}

module Const = struct
  let cons =
    let cid   = "::" in
    let ty    = tyarrow [Ty.o ; Ty.olist] Ty.olist in
    let term  = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let nil =
    let cid = "nil" in
    let ty    = Ty.olist in
    let term  = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let pi =
    let cid = "pi" in
    let ty    = tyarrow [tyarrow [tybase "A"] Ty.o] Ty.o in
    let term  = const cid ty in
    { cid ; pty = Poly (["A"], ty) ; term }

  let imp =
    let cid = "=>" in
    let ty    = tyarrow [Ty.o ; Ty.o] Ty.o in
    let term  = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let member =
    let cid = "member" in
    let ty    = tyarrow [Ty.o ; Ty.olist] Ty.prop in
    let term  = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let constr =
    let cid = "$" in
    let ty = tyarrow [Ty.prop] Ty.o in
    let term = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }
end

module Meta = struct
  let __binarym cid =
    let ty  = tyarrow [Ty.prop ; Ty.prop] Ty.prop in
    let term = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let andm = __binarym "/\\"
  let orm  = __binarym "\\/"
  let impm = __binarym "->"

  let __constm cid =
    let ty  = Ty.prop in
    let term = const cid ty in
    { cid ; pty = pty_of_ty ty ; term }

  let truem  = __constm "true"
  let falsem = __constm "false"

  let eqm =
    let cid = "=" in
    let ty  = tyarrow [tybase "A" ; tybase "A"] Ty.prop in
    let term = const cid ty in
    { cid ; pty = Poly(["A"], ty) ; term }

  let __quantm cid =
    let ty = tyarrow [tyarrow [tybase "A"] Ty.prop] Ty.prop in
    let term = const cid ty in
    { cid ; pty = Poly(["A"], ty) ; term }

  let forallm = __quantm "forall"
  let existsm = __quantm "exists"

  let __meta_cids =
    List.fold_right String.Set.add
      [ andm.cid ; truem.cid ;
        orm.cid ; falsem.cid ;
        impm.cid ;
        eqm.cid ;
        forallm.cid ; existsm.cid ]
      String.Set.empty

  let is_meta_const c =
    String.Set.mem c __meta_cids

end

let const_id    k = k.cid
let const_pty   k = k.pty
let const_ty    k = ty_of_pty k.pty
let const_term  k = const k.cid (const_ty k)

type sign = {
  ktable : id list ;
  ctable : const list ;
}

let target_ty (Ty (_, b)) = b

(** Pervasive signature *)

let pervasive_sign = {
  ktable = [target_ty Ty.o ; target_ty Ty.olist ; target_ty Ty.prop] ;
  ctable = [Const.pi ; Const.imp ; Const.cons ; Const.nil ; Const.member ; Const.constr] ;
}
