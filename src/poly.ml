(****************************************************************************)
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

open Extensions
open Abella_types

type ty =
  | Tv  of id
  | Kon of ty list * id
  | Arr of ty * ty

let __last_fresh_tv = ref 0
let rec freshen1 vmap ty =
  match ty with
  | Tv n ->
      if IdMap.mem n vmap then
        (vmap, IdMap.find n vmap)
      else begin
        let v = Tv ("?" ^ string_of_int !__last_fresh_tv) in
        let vmap = IdMap.add n v vmap in
        incr __last_fresh_tv ;
        (vmap, v)
      end
  | Kon (tys, k) ->
      let (vmap, tys) = List.fold_left begin
        fun (vmap, tys) ty ->
          let (vmap, ty) = freshen1 vmap ty in
          (vmap, ty :: tys)
      end (vmap, []) tys in
      let tys = List.rev tys in
      (vmap, Kon (tys, k))
  | Arr (tya, tyb) ->
      let (vmap, tya) = freshen1 vmap tya in
      let (vmap, tyb) = freshen1 vmap tyb in
      (vmap, Arr (tya, tyb))

let freshen ty = snd (freshen1 IdMap.empty ty)

let varify n =
  let rec digs k ds n =
    if n < 26 then (k, (n :: ds))
    else digs (k + 1) (n mod 26 :: ds) (n / 26 - 1)
  in
  let (k, ds) = digs 0 [] n in
  let ds = ref ds in
  let str = String.create (k + 1) in
  for i = 0 to k do
    match !ds with
    | d :: rest ->
        ds := rest ;
        str.[i] <- Char.chr (97 + d)
    | _ -> assert false
  done ;
  str

let rec abstract1 vnext vmap ty =
  match ty with
  | Tv n ->
      if IdMap.mem n vmap then
        (vnext, vmap, IdMap.find n vmap)
      else
        let ty = Tv (varify vnext) in
        let vmap = IdMap.add n ty vmap in
        let vnext = vnext + 1 in
        (vnext, vmap, ty)
  | Kon (tys, k) ->
      let (vnext, vmap, tys) = List.fold_left begin
        fun (vnext, vmap, tys) ty ->
          let (vnext, vmap, ty) = abstract1 vnext vmap ty in
          (vnext, vmap, ty :: tys)
      end (vnext, vmap, []) tys in
      let tys = List.rev tys in
      (vnext, vmap, Kon (tys, k))
  | Arr (tya, tyb) ->
      let (vnext, vmap, tya) = abstract1 vnext vmap tya in
      let (vnext, vmap, tyb) = abstract1 vnext vmap tyb in
      (vnext, vmap, Arr (tya, tyb))

let abstract ty =
  let (_, _, ty) = abstract1 0 IdMap.empty ty in
  ty

open Format
open Extensions.ExtFormat

let fmt_arrow ff =
  Format.pp_print_string ff " ->" ;
  Format.pp_print_space ff ()

let rec ty_to_fexp ty =
  match ty with
  | Tv v ->
      Fstr ("\'" ^ v)
  | Kon ([], n) ->
      Fstr n
  | Kon (tys, kon) ->
      Fatm begin fun ff ->
        pp_open_box ff 1 ; begin
          intercalate
            ~left:(fmt_of_string "(")
            ~right:(fmt_of_string ")")
            ~sep:(fmt_of_format ",@ ")
            pp_ty tys ff ;
          pp_print_break ff 1 1 ;
          pp_print_string ff kon
        end ; pp_close_box ff ()
      end
  | Arr (ta, tb) ->
      Fapp (1, Finfix (`Right, ty_to_fexp ta, fmt_arrow, ty_to_fexp tb))

and pp_ty ty ff =
  Format.fprintf ff "@[<b0>%t@]" (linearize (ty_to_fexp ty))

let to_buffer buf ty =
  let ff = Format.formatter_of_buffer buf in
  pp_ty ty ff ;
  Format.pp_print_flush ff ()

let ty_to_string ty =
  let buf = Buffer.create 19 in
  to_buffer buf ty ;
  Buffer.contents buf
  
let display ty = Format.printf "%t@." (pp_ty ty)
