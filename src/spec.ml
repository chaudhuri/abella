open Term

include (struct
  type bucket = string
  module BTab = Weak.Make (struct
    type t = bucket
    let hash : t -> int = Hashtbl.hash
    let equal (b1 : t) (b2 : t) = b1 = b2
  end)
  let __tab = BTab.create 7
  let bucket rep = BTab.merge __tab rep
end : sig
  type bucket = private string
  val bucket : string -> bucket
end)

type 'seq gen = {
  tys : ty list ;
  seq : 'seq
}

module type Basic =
sig
  type seq

  val make        : (bucket * term list) list -> seq

  val to_string   : seq -> string

  val map_terms   : (bucket -> term -> term) -> seq -> seq
  val iter_terms  : (bucket -> term -> unit) -> seq -> unit

  val cut         : seq -> seq -> seq

  val inst        : seq -> (id * term) list -> seq

  val async_phase : cont:(seq gen -> unit) -> seq -> unit
  val sync_phase  : cont:(seq gen list -> unit) -> seq -> unit
end

module type T =
sig
  include Basic

  val fold_async : ('a -> seq gen -> 'a) -> 'a -> seq -> 'a
  val async      : seq -> seq gen list

  val fold_sync  : ('a -> seq gen list -> 'a) -> 'a -> seq -> 'a
  val sync       : seq -> seq gen list list
end
  
module Complete (Basic : Basic) : T with type seq = Basic.seq =
struct
  include Basic

  let fold_async ffn acc0 orig =
    let acc = ref acc0 in
    let cont s = acc := ffn !acc s in
    async_phase ~cont orig ;
    !acc
    
  let async orig = 
    let results = ref [] in
    let cont s = results := s :: !results in
    async_phase ~cont orig ;
    List.rev !results

  let fold_sync ffn acc0 orig =
    let acc = ref acc0 in
    let cont s = acc := ffn !acc s in
    sync_phase ~cont orig ;
    !acc

  let sync orig =
    let results = ref [] in
    let cont s = results := s :: !results in
    sync_phase ~cont orig ;
    List.rev !results
end
