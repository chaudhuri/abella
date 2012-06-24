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

type aty =
  | Tyvar of string
  | Tycon of string

let arep = function
  | Tyvar v -> v
  | Tycon c -> c

type ty = Ty of ty list * aty

let tyarrow tys ty =
  match ty with
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty =
  Ty([], Tycon bty)

let tyvar tv =
  Ty ([], Tyvar tv)

let oty = tybase "o"
let olistty = tybase "olist"

let is_tyvar = function
  | Tyvar _ -> true
  | _ -> false

let fresh_tyvar =
  let count = ref 0 in
    fun () ->
      incr count ;
      tyvar (string_of_int !count)

let aty_to_string aty =
  match aty with
  | Tyvar s -> "'" ^ s
  | Tycon s -> s

let to_string ty =
  let rec aux nested ty =
    match ty with
    | Ty([], bty) -> aty_to_string bty
    | Ty(tys, bty) ->
        let bty = aty_to_string bty in
        let res = String.concat " -> "(List.map (aux true) tys @ [bty]) in
        if nested then parenthesis res else res
  in
  aux false ty
