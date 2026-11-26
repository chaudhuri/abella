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

(** Registry of sealed types (quotient types introduced by [Seal]). *)

type info = {
  name       : string ;
  typarams   : string list ;
  underlying : Term.ty ;
  rel_name   : string ;
  rel_ty     : Term.ty ;
}

val table : info Term.Itab.t ref

val add : info -> unit
val lookup : string -> info option
val is_sealed_type : string -> bool
val is_sealed_ctor : string -> bool
val is_sealed_target_ty : Term.ty -> bool
val contains_sealed_ty : Term.ty -> bool
