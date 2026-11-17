(*
 * Author: Kaustuv Chaudhuri <kaustuv@chaudhuri.info>
 * Copyright (C) 2026  Inria
 * See LICENSE for licensing details.
 *)

type id
type t = id

val intern : string -> id
val reintern : id -> id
val value : id -> string
val key : id -> int
val to_string : id -> string
val pp : Format.formatter -> id -> unit
val equal : id -> id -> bool
val compare : id -> id -> int
val hash : id -> int

module Map : sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val cardinal : 'a t -> int
  val mem : id -> 'a t -> bool
  val find : id -> 'a t -> 'a
  val find_opt : id -> 'a t -> 'a option
  val add : id -> 'a -> 'a t -> 'a t
  val remove : id -> 'a t -> 'a t
  val singleton : id -> 'a -> 'a t
  val iter : (id -> 'a -> unit) -> 'a t -> unit
  val fold : (id -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val bindings : 'a t -> (id * 'a) list
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end

module Set : sig
  type t
  val empty : t
  val is_empty : t -> bool
  val cardinal : t -> int
  val mem : id -> t -> bool
  val add : id -> t -> t
  val remove : id -> t -> t
  val singleton : id -> t
  val of_list : id list -> t
  val elements : t -> id list
  val iter : (id -> unit) -> t -> unit
  val fold : (id -> 'a -> 'a) -> t -> 'a -> 'a
  val equal : t -> t -> bool
end
