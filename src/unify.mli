(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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

val seal : tycons -> tycons -> id -> unit
val get_seal_opt : ty -> (tycons * ty * id) option

type unify_failure =
  | OccursCheck
  | ConstClash of (term * term)
  | Generic
  | FailTrail of int * unify_failure

val explain_failure : unify_failure -> string

exception UnifyFailure of unify_failure

type unify_error =
  | NotLLambda
  | InstGenericTyvar of string * ty
  | InvalidSealing

val explain_error : unify_error -> string

exception UnifyError of unify_error

val right_unify : ?used:(id * term) list -> term -> term -> unit
val left_unify : ?used:(id * term) list -> term -> term -> unit

val try_with_state : fail:'a -> (unit -> 'a) -> 'a

val try_right_unify : ?used:(id * term) list -> term -> term -> bool
val try_left_unify : ?used:(id * term) list -> term -> term -> bool

type unify_result = {
  cpairs : (term * term) list ;
  equivs : term list ;
}

val try_left_unify_cpairs :
  used:(id * term) list -> term -> term -> unify_result option
val try_right_unify_cpairs : term -> term -> unify_result option

val left_flexible_heads :
  used:(id * term) list ->
  sr:Subordination.sr ->
  ((id*ty) list * term * term list) ->
  ((id*ty) list * term * term list) ->
    term list
