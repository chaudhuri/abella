(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                                en Informatique et en Automatique)        *)
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


(* Kinds *)
type knd = Knd of int [@@unboxed]

val kind : int -> knd
val kincr : knd -> knd
val karity : knd -> int

(* Types *)

type tyvar = Id.t
type tycons = Id.t

type ty = Ty of ty list * aty
and aty =
  | Tygenvar of tyvar
  | Typtr of typtr
  | Tycons of tycons * ty list
and typtr = in_typtr ref
and in_typtr = TV of tyvar | TT of ty

val eq_ty : ty -> ty -> bool
val eq_tid : (Id.t * ty) -> (Id.t * ty) -> bool
val observe_ty : ty -> ty
val iter_ty : (aty -> unit) -> ty -> unit

val tyarrow : ty list -> ty -> ty
val tybase : aty -> ty

val oaty : aty
val olistaty : aty
val propaty : aty
val oty : ty
val olistty : ty
val propty : ty

val contains_prop : ty -> bool

(* Variables *)

type tag = Eigen | Constant | Logic | Nominal

type var = private {
  name : Id.t ;
  tag  : tag ;
  ts   : int ;
  ty   : ty ;
}

(* Terms. The use of references allow in-place normalization,
 * but is completely hidden by the interface. *)

type ptr
type tyctx = (Id.t * ty) list

type term = private
  | Var of var
  | DB of int
  | Lam of tyctx * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr (* Sorry about this one, hiding it is costly.. *)
and envitem = Dum of int | Binding of term * int
and env = envitem list

(* [observe t] is the way to analyze the structure of a term. *)
val observe : term -> term

(** [deep_copy t] copies the term t by duplicating all variables *)
val deep_copy : term -> term

(** Creation of terms.
  * There is probably more to come here. *)

val var : tag -> Id.t -> int -> ty -> term

val app : term -> term list -> term
val susp : term -> int -> int -> env -> term
val db : int -> term

module Notations :
sig
  val (//) : tyctx -> term -> term
  val (^^) : term -> term list -> term
end

(* get a list of tys from a type context *)
val get_ctx_tys : tyctx -> ty list

val eq : term -> term -> bool
val eq_idterm : (Id.t * term) -> (Id.t * term) -> bool

(* Binding a variable to a term or type . The *contents* of the cell
   representing the * variable is a reference which must be
   updated. Also the variable must * not be made a reference to
   itself. *)

val bind : term -> term -> unit
val bind_ty : aty -> ty -> unit

type bind_state
val get_bind_state : unit -> bind_state
val set_bind_state : bind_state -> unit

(* Scoped bind state is more efficient than regular bind state, but it
   must always be used in a lexically scoped fashion. The unwind_state
   wraps a function with a scoped get and set. *)

type scoped_bind_state
val get_scoped_bind_state : unit -> scoped_bind_state
val set_scoped_bind_state : scoped_bind_state -> unit

val unwind_state : ('a -> 'b) -> ('a -> 'b)

(* Raise the substitution *)
val add_dummies : env -> int -> int -> env

(* Add abstractions. *)
val lambda : tyctx -> term -> term

(** Abstract [t] over constant or variable named [Id.t]. *)
val abstract : Id.t -> ty -> term -> term

(** Abella specific additions and changes *)
val const : ?ts:int -> Id.t -> ty -> term
val fresh : ?tag:tag -> int -> ty -> term
val fresh_wrt : ts:int -> tag -> Id.t -> ty ->
                  (Id.t * term) list -> term * (Id.t * term) list

val nominal_var : Id.t -> ty -> term

val find_vars : tag -> term list -> var list
val find_var_refs : tag -> term list -> term list
val map_vars : (var -> 'a) -> term list -> 'a list

val term_to_var : term -> var
val term_to_name : term -> Id.t
val term_to_pair : term -> Id.t * term

val has_logic_head : term -> bool
val has_eigen_head : term -> bool

val hnorm : term -> term

val pretty_ty : ty -> Pretty.expr
val format_ty : Format.formatter -> ty -> unit
val ty_to_string : ty -> string
val aty_to_string : aty -> string
val knd_to_string : knd -> string

val var_to_string : var -> string

(** Presentation-only rewriting of constant and type-constructor names. *)
val display_name : (string -> string) ref

val pretty_term : tyctx -> term -> Pretty.expr

val format_term :  ?cx:tyctx ->
  Format.formatter -> term -> unit
val term_to_string : ?cx:tyctx ->
  term -> string

val prefix : tag -> string

(** Interned logical constants *)
val arrow_id : Id.t
val amp_id : Id.t
val cons_id : Id.t
val pi_id : Id.t
val sigma_id : Id.t

val get_used : term list -> (Id.t * term) list
val is_free : term -> bool

val is_nominal_name : Id.t -> bool
val is_nominal : term -> bool
val fresh_name : Id.t -> (Id.t * 'a) list -> Id.t
val term_head : term -> (term * term list) option
val is_head_name : Id.t -> term -> bool
val term_head_name : term -> Id.t
val term_head_ty : term -> ty

val is_capital_name : Id.t -> bool
val capital_tids : term list -> (Id.t * ty) list
val question_tids : term list -> (Id.t * ty) list
val nominal_tids : term list -> (Id.t * ty) list
val all_tids : term list -> (Id.t * ty) list

val tc : tyctx -> term -> ty

val atyvar : Id.t -> aty
val atybase : Id.t -> aty
val atyapp : aty -> ty -> aty
val tyvar : Id.t -> ty
val is_tyvar : Id.t -> bool
val fresh_tyvar : unit -> ty

val is_imp : term -> bool
val extract_imp : term -> term * term

val is_amp : term -> bool
val extract_amp : term -> term * term

val is_pi : term -> bool
val extract_pi : term -> term

val term_map_on_tys : (ty -> ty) -> term -> term
val term_iter_tys : (ty -> unit) -> term -> unit

val ty_tyvars : ty -> Id.t list
val ty_contains_tyvar : ty -> bool
val term_collect_tyvar_names : term -> Id.t list
val terms_contain_tyvar : term list -> bool

val ty_gentyvars : ty -> Id.t list
val ty_contains_gentyvar : ty -> bool
val term_collect_gentyvar_names : term -> Id.t list
val terms_contain_gentyvar : term list -> bool

(* Type substitutions *)
type tysub = (Id.t * ty) list
val apply_sub_ty : tysub -> ty -> ty
val apply_sub_ty_tyvar : tysub -> ty -> ty

(* Schematic instantiations pending audit for [prop] *)
val schematic_instantiations : tysub ref
val mark_schematic_tysub : tysub -> unit

(* Re-establish the interning invariant for unmarshalled values *)
val reintern_ty : ty -> ty
val reintern_aty : aty -> aty
val reintern_tyctx : tyctx -> tyctx
val reintern_term : term -> term
