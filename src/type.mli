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

type ty = Ty of ty list * aty

and aty =
  | Tyvar of string
  | Tycon of string * ty list

val aty_head : aty -> string

val tyarrow : ty list -> ty -> ty
val tyvar   : string -> ty
val tybase  : string -> ty list -> ty

val is_tyvar    : aty -> bool
val fresh_tyvar : unit -> ty

(****************************************************************************)

val to_string : ty -> string

type ki = int
val ki_to_string : ki -> string

(****************************************************************************)

type tysub = ty IdMap.t

val apply_tysub : tysub -> ty -> ty

val freshen : ?using:tysub -> ty -> tysub * ty
val renumber : ?using:tysub -> ty -> tysub * ty

val equal_modulo : ty -> ty -> bool

(****************************************************************************)

type decl =
  | Kind of ki
  | Type of ty

type sign = {
  order : string list ;
  decls : decl IdMap.t ;
}

val get_kind   : sign -> string -> ki
val get_type   : sign -> string -> ty

val check_kind : sign -> ty -> unit

val process : sign -> (string list * decl) list -> sign

val spec_pervasives  : sign
val import_spec_sign : sign -> sign

(****************************************************************************)

val oty     : ty
val olistty : ty (** DEPRECATED *)
val propty  : ty
val listty  : ty -> ty


(****************************************************************************)

type typrob = {
  expected : ty ;
  actual   : ty ;
  position : Lexing.position * Lexing.position ;
  info     : [`Fun | `Arg] ;
}

exception Unsolvable of typrob

val typrobs_to_string : typrob list -> string

val typrob_apply_tysub : tysub -> typrob -> typrob

val solve : typrob list -> tysub
