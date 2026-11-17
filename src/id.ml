(*
 * Author: Kaustuv Chaudhuri <kaustuv@chaudhuri.info>
 * Copyright (C) 2026  Inria
 * See LICENSE for licensing details.
 *)

type id = {
  key : int ;
  value : string ;
}
type t = id

let equal a b = a.key = b.key
let compare a b = Int.compare a.key b.key
let hash a = Hashtbl.hash a.key
let key id = id.key
let value id = id.value
let to_string id = id.value
let pp ppf id = Format.pp_print_string ppf id.value

module WeakIdSet = Weak.Make (struct
  type t = id
  let equal a b = String.equal a.value b.value
  let hash a = Hashtbl.hash a.value
end)

let pool = WeakIdSet.create 256
let next_key = ref (-1)

let intern (s : string) : id =
  let candidate = { key = -1 ; value = s } in
  match WeakIdSet.find_opt pool candidate with
  | Some existing -> existing
  | None ->
     incr next_key ;
     let id = { key = !next_key ; value = s } in
     WeakIdSet.add pool id ;
     id

let reintern id = intern id.value

module IntMap = Stdlib.Map.Make (struct
  type t = int
  let compare = Int.compare
end)

let large_threshold = 8

let compare_value a b = String.compare a.value b.value

module Map = struct
  type 'a alist =
    | Nil
    | Cons of id * 'a * 'a alist

  type 'a t =
    | Small of { size : int ; rep : 'a alist }
    | Large of (id * 'a) IntMap.t

  let empty = Small { size = 0 ; rep = Nil }

  let cardinal = function
    | Small { size ; _ } -> size
    | Large m -> IntMap.cardinal m

  let is_empty t = cardinal t = 0

  let rec mem_alist id = function
    | Nil -> false
    | Cons (id', _, rest) ->
       let c = Int.compare id.key id'.key in
       c = 0 || (c > 0 && mem_alist id rest)

  let mem id = function
    | Small { rep ; _ } -> mem_alist id rep
    | Large m -> IntMap.mem id.key m

  let rec find_alist id = function
    | Nil -> raise Not_found
    | Cons (id', v, rest) ->
       let c = Int.compare id.key id'.key in
       if c = 0 then v
       else if c < 0 then raise Not_found
       else find_alist id rest

  let find id t =
    match t with
    | Small { rep ; _ } -> find_alist id rep
    | Large m -> snd (IntMap.find id.key m)

  let find_opt id t =
    match t with
    | Small { rep ; _ } ->
       (match find_alist id rep with
        | v -> Some v
        | exception Not_found -> None)
    | Large m ->
       (match IntMap.find_opt id.key m with
        | None -> None
        | Some (_, v) -> Some v)

  let rec add_alist id v = function
    | Nil -> Cons (id, v, Nil)
    | Cons (id', v', rest) as node ->
       let c = Int.compare id.key id'.key in
       if c = 0 then Cons (id, v, rest)
       else if c < 0 then Cons (id, v, node)
       else Cons (id', v', add_alist id v rest)

  let rec remove_alist id = function
    | Nil -> Nil
    | Cons (id', v, rest) as node ->
       let c = Int.compare id.key id'.key in
       if c = 0 then rest
       else if c < 0 then node
       else Cons (id', v, remove_alist id rest)

  let of_alist size rep =
    if size > large_threshold then
      let m =
        let rec spin acc = function
          | Nil -> acc
          | Cons (id, v, rest) ->
             spin (IntMap.add id.key (id, v) acc) rest
        in
        spin IntMap.empty rep
      in
      Large m
    else
      Small { size ; rep }

  let add id v t =
    match t with
    | Small { size ; rep } ->
       let rep' = add_alist id v rep in
       let size' = if mem_alist id rep then size else size + 1 in
       of_alist size' rep'
    | Large m ->
       Large (IntMap.add id.key (id, v) m)

  let remove id = function
    | Small { size ; rep } as t ->
       if mem_alist id rep then
         Small { size = size - 1 ; rep = remove_alist id rep }
       else t
    | Large m -> Large (IntMap.remove id.key m)

  let singleton id v = add id v empty

  let to_list = function
    | Small { rep ; _ } ->
       let rec spin acc = function
         | Nil -> acc
         | Cons (id, v, rest) -> spin ((id, v) :: acc) rest
       in
       spin [] rep
    | Large m -> List.map snd (IntMap.bindings m)

  let sorted_bindings t =
    List.sort (fun (a, _) (b, _) -> compare_value a b) (to_list t)

  let iter f t = List.iter (fun (id, v) -> f id v) (sorted_bindings t)

  let fold f t acc =
    List.fold_left (fun acc (id, v) -> f id v acc)
      acc (sorted_bindings t)

  let bindings t = sorted_bindings t

  let equal eq t1 t2 =
    cardinal t1 = cardinal t2 &&
      List.for_all2 (fun (id1, v1) (id2, v2) ->
          equal id1 id2 && eq v1 v2)
        (sorted_bindings t1) (sorted_bindings t2)
end

module Set = struct
  type alist =
    | Nil
    | Cons of id * alist

  type t =
    | Small of { size : int ; rep : alist }
    | Large of id IntMap.t

  let empty = Small { size = 0 ; rep = Nil }

  let cardinal = function
    | Small { size ; _ } -> size
    | Large m -> IntMap.cardinal m

  let is_empty t = cardinal t = 0

  let rec mem_alist id = function
    | Nil -> false
    | Cons (id', rest) ->
       let c = Int.compare id.key id'.key in
       c = 0 || (c > 0 && mem_alist id rest)

  let mem id t =
    match t with
    | Small { rep ; _ } -> mem_alist id rep
    | Large m -> IntMap.mem id.key m

  let rec add_alist id = function
    | Nil -> Cons (id, Nil)
    | Cons (id', rest) as node ->
       let c = Int.compare id.key id'.key in
       if c = 0 then node
       else if c < 0 then Cons (id, node)
       else Cons (id', add_alist id rest)

  let rec remove_alist id = function
    | Nil -> Nil
    | Cons (id', rest) as node ->
       let c = Int.compare id.key id'.key in
       if c = 0 then rest
       else if c < 0 then node
       else Cons (id', remove_alist id rest)

  let of_alist size rep =
    if size > large_threshold then
      let m =
        let rec spin acc = function
          | Nil -> acc
          | Cons (id, rest) ->
             spin (IntMap.add id.key id acc) rest
        in
        spin IntMap.empty rep
      in
      Large m
    else
      Small { size ; rep }

  let add id t =
    match t with
    | Small { size ; rep } ->
       if mem_alist id rep then t
       else of_alist (size + 1) (add_alist id rep)
    | Large m -> Large (IntMap.add id.key id m)

  let remove id = function
    | Small { size ; rep } as t ->
       if mem_alist id rep then
         Small { size = size - 1 ; rep = remove_alist id rep }
       else t
    | Large m -> Large (IntMap.remove id.key m)

  let singleton id = add id empty

  let of_list l = List.fold_left (fun s x -> add x s) empty l

  let to_list = function
    | Small { rep ; _ } ->
       let rec spin acc = function
         | Nil -> acc
         | Cons (id, rest) -> spin (id :: acc) rest
       in
       spin [] rep
    | Large m -> List.map snd (IntMap.bindings m)

  let elements t =
    List.sort compare_value (to_list t)

  let iter f t = List.iter f (elements t)

  let fold f t acc = List.fold_left (fun acc id -> f id acc)
    acc (elements t)

  let equal t1 t2 =
    cardinal t1 = cardinal t2 &&
      List.for_all2 equal (elements t1) (elements t2)
end
