(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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

type context

val to_list  : context -> term list
val of_list  : term list -> context

val is_empty : context -> bool

val empty    : context
val add      : term -> context -> context

val size     : context -> int

val mem      : term -> context -> bool
val remove   : term -> context -> context

val equiv    : context -> context -> bool

val union    : context -> context -> context

val map      : (term -> term) -> context -> context

val iter     : (term -> unit) -> context -> unit

val to_term    : context -> term
val to_string  : context -> string

val normalize  : context -> context

val subcontext : context -> context -> bool


val wellformed : context -> bool

val reconcile  : (context * context) list -> unit

val backchain_reconcile : context -> context -> unit

type t = context
