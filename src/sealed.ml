(****************************************************************************)
(* Copyright (C) 2026 Inria (Institut National de Recherche                 *)
(*                           en Informatique et en Automatique)             *)
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

type info = {
  name       : string ;
  typarams   : string list ;
  underlying : ty ;
  rel_name   : string ;
  rel_ty     : ty ;
}

let table : info Itab.t ref = State.rref Itab.empty

let add info =
  table := Itab.add info.name info !table

let lookup name =
  Itab.find_opt name !table

let is_sealed_type name =
  Itab.mem name !table

let is_sealed_ctor name =
  Itab.mem name !table

let is_sealed_target_ty ty =
  match observe_ty ty with
  | Ty (_, Tycons (c, _)) -> is_sealed_type c
  | _ -> false

exception Found_sealed

let contains_sealed_ty ty =
  let check = function
    | Tycons (c, _) when is_sealed_type c -> raise Found_sealed
    | _ -> ()
  in
  match iter_ty check ty with
  | () -> false
  | exception Found_sealed -> true
