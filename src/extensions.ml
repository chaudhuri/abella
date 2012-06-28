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

let (>>) f g x = g (f x)
let (|>) x f = f x

let curry f (x,y) = f x y
let uncurry f x y = f (x,y)

let parenthesis x = "(" ^ x ^ ")"

module Option = struct
  let is_some x =
    match x with
      | Some _ -> true
      | None -> false

  let is_none x =
    match x with
      | Some _ -> false
      | None -> true

  let get x =
    match x with
      | Some v -> v
      | None -> failwith "Option.get called on None"

  let map_default f default x =
    match x with
      | Some v -> f v
      | None -> default

  let default default x =
    match x with
      | Some v -> v
      | None -> default
end

module String = struct
  include String

  let count str char =
    let count = ref 0 in
      String.iter (fun c -> if c = char then incr count) str ;
      !count
end

module StringOrd = struct
  type t = string
  let compare : t -> t -> int = Pervasives.compare
end
module StringSet = Set.Make (StringOrd)
module StringMap = Map.Make (StringOrd)

module List = struct
  include List

  let mem ?(cmp=(=)) elt list =
    let rec aux list =
      match list with
        | [] -> false
        | head::tail -> cmp elt head || aux tail
    in
      aux list

  let remove ?(cmp=(=)) elt list =
    let rec aux list =
      match list with
        | [] -> []
        | head::tail when cmp elt head -> aux tail
        | head::tail -> head::(aux tail)
    in
      aux list

  let unique ?(cmp=(=)) list =
    let rec aux list =
      match list with
        | [] -> []
        | head::tail -> head::(aux (remove ~cmp:cmp head tail))
    in
      aux list

  let is_unique ?(cmp=(=)) list =
    let rec aux list =
      match list with
        | [] -> true
        | head::tail -> not (mem ~cmp head tail) && aux tail
    in
      aux list

  let find_duplicate list =
    let rec aux list =
      match list with
        | [] -> None
        | head::tail when mem head tail -> Some head
        | _::tail -> aux tail
    in
      aux list

  let find_all f list =
    filter f list

  let find_some f list =
    let rec aux list =
      match list with
        | [] -> None
        | head::tail ->
            match f head with
              | Some v -> Some v
              | None -> aux tail
    in
      aux list

  let filter_map f list =
    map Option.get (find_all Option.is_some (map f list))

  let flatten_map f list =
    flatten (map f list)

  let remove_all f list =
    find_all (fun x -> not (f x)) list

  let minus ?(cmp=(=)) list1 list2 =
    remove_all (fun e -> mem ~cmp e list2) list1

  let intersect ?(cmp=(=)) list1 list2 =
    find_all (fun e -> mem ~cmp e list2) list1

  let rec take n list =
    match list, n with
      | [], _ -> []
      | _, n when n <= 0 -> []
      | x::xs, n -> x::(take (n-1) xs)

  let remove_assocs to_remove alist =
    let rec aux alist =
      match alist with
        | (a, b)::rest ->
            if mem a to_remove
            then aux rest
            else (a, b)::(aux rest)
        | [] -> []
    in
      aux alist

  let assoc_all ?(cmp=(=)) x list =
    let rec aux list =
      match list with
        | [] -> []
        | (a, b)::tail when cmp x a -> b::(aux tail)
        | _::tail -> aux tail
    in
      aux list

  let remove_all_assoc ?(cmp=(=)) x list =
    let rec aux list =
      match list with
        | [] -> []
        | (a, b)::tail when cmp x a -> aux tail
        | head::tail -> head::(aux tail)
    in
      aux list

  let max list =
    let rec aux list m =
      match list with
        | [] -> m
        | head::tail -> aux tail (max head m)
    in
      aux list 0

  let rec distribute elt list =
    match list with
      | [] -> [[elt]]
      | head::tail -> (elt::list) ::
          (map (fun x -> head::x) (distribute elt tail))

  (* Generate all permutations of all n element subsets of list *)
  let rec permute n list =
    if n = 0 then
      [[]]
    else
      match list with
        | [] -> []
        | head::tail ->
            (flatten_map (distribute head) (permute (n-1) tail))
            @ (permute n tail)

  (* Generate all n element subsets of list *)
  let rec choose n list =
    if n = 0 then
      [[]]
    else
      match list with
        | [] -> []
        | head::tail ->
            (map (fun t -> head::t) (choose (n-1) tail))
            @ (choose n tail)

  let rec range a b =
    if a > b then
      []
    else
      a :: range (a+1) b

  let number list =
    let rec aux i list =
      match list with
        | [] -> []
        | head::tail -> (i, head) :: (aux (i+1) tail)
    in
      aux 1 list

  let fold_left1 f list =
    match list with
      | x::xs -> fold_left f x xs
      | _ -> invalid_arg "Empty list"

  let rec drop n list =
    match list with
      | x::xs when n > 0 -> drop (n-1) xs
      | _ -> list

  let drop_last n list = rev (drop n (rev list))
  let take_last n list = rev (take n (rev list))

  let rev_map f list =
    let rec aux list acc =
      match list with
        | [] -> acc
        | x::xs -> aux xs (f x :: acc)
    in
      aux list []

  let rec rev_app xs ys =
    match xs with
      | [] -> ys
      | x::xs -> rev_app xs (x::ys)

  let replicate n x =
    let rec aux = function
      | 0 -> []
      | i -> x :: aux (i-1)
    in
      aux n

  let map_fst f list =
    map (fun (x,y) -> (f x, y)) list

  let map_snd f list =
    map (fun (x,y) -> (x, f y)) list

  let rec combine3 l1 l2 l3 =
    match l1, l2, l3 with
      | [], [], [] -> []
      | x::xs, y::ys, z::zs -> (x, y, z) :: (combine3 xs ys zs)
      | _ -> raise (Invalid_argument "List.combine3")

end

module Hashtbl = struct
  include Hashtbl

  let assign dest src =
    clear dest ;
    iter (fun a b -> add dest a b) src

end

module Either = struct
  type ('a, 'b) either = Left of 'a | Right of 'b

  let either left right e =
    match e with
      | Left x -> left x
      | Right x -> right x

  let rec partition_eithers eithers =
    let left x (l, r) = (x::l, r) in
    let right x (l, r) = (l, x::r) in
      List.fold_right (either left right) eithers ([], [])
end

module ExtFormat : sig
  type fmt = Format.formatter -> unit

  val intercalate : ?left:fmt -> ?right:fmt -> ?sep:fmt -> ('a -> fmt) -> 'a list -> fmt

  val paren : fmt -> fmt

  type prec = int

  type fexp =
    | Fstr of string
    | Fatm of fmt
    | Fapp of prec * fapp

  and fapp =
    | Finfix   of [`Left | `Right | `Non] * fexp * fmt * fexp
    | Fprefix  of fmt * fexp
    | Fpostfix of fexp * fmt

  val linearize : fexp -> fmt
end = struct
  open Format

  type fmt = formatter -> unit

  let rec intercalate1 sep elf l ff =
    match l with
    | [] -> ()
    | [x] -> elf x ff
    | x :: l ->
        elf x ff ;
        sep ff ;
        intercalate1 sep elf l ff
        
  let intercalate ?left ?right ?sep elf l ff =
    begin match left with Some left -> left ff | None -> () end ;
    pp_open_box ff 0 ;
    intercalate1 (match sep with Some sep -> sep | None -> fun ff -> ())
      elf l ff ;
    pp_close_box ff () ;
    begin match right with Some right -> right ff | None -> () end

  type prec = int

  type fexp =
    | Fstr of string
    | Fatm of fmt
    | Fapp of prec * fapp

  and fapp =
    | Finfix   of [`Left | `Right | `Non] * fexp * fmt * fexp
    | Fprefix  of fmt * fexp
    | Fpostfix of fexp * fmt

  let paren f =
    fun ff ->
      pp_print_string ff "(" ;
      f ff ;
      pp_print_string ff ")"

  let prec_same fe1 fe2 =
    match fe1, fe2 with
    | Fstr _, Fstr _
    | Fstr _, Fatm _
    | Fatm _, Fstr _
    | Fatm _, Fatm _ -> true
    | Fapp (p1, _), Fapp (p2, _) -> p1 = p2
    | _ -> false

  let prec_lt fe1 fe2 =
    match fe1, fe2 with
    | _, Fstr _
    | _, Fatm _ -> true
    | Fstr _, _
    | Fatm _, _ -> false
    | Fapp (p1, _), Fapp (p2, _) -> p1 < p2

  let assoc = function
    | Fapp (_, Finfix (asc, _, _, _)) -> asc
    | _ -> `Non

  let rec linearize fe : fmt =
    fun ff -> match fe with
    | Fatm fa -> fa ff
    | Fstr s -> pp_print_string ff s
    | Fapp (prec, fapp) -> begin
      match fapp with
      | Finfix (asc, fel, fo, fer) ->
          let fel =
            if (prec_lt fel fe 
                || (prec_same fel fe && asc = `Left
                    && assoc fel = `Left))
            then bracket fel
            else fel
          in
          let fer =
            if (prec_lt fer fe
                || (prec_same fel fe && asc = `Right
                    && assoc fer = `Right))
            then bracket fer
            else fer
          in
          linearize fel ff ;
          fo ff ;
          linearize fer ff
      | Fprefix (fo, fec) ->
          let fec = match fec with
          | Fapp (_, Fprefix _) -> fec
          | _ when prec_lt fec fe -> bracket fec
          | _ -> fec
          in
          fo ff ;
          linearize fec ff
      | Fpostfix (fec, fo) ->
          let fec = match fec with
          | Fapp (_, Fpostfix _) -> fec
          | _ when  prec_lt fec fe -> bracket fec
          | _ -> fec
          in
          linearize fec ff ;
          fo ff
    end

  and bracket fe = Fatm (paren (linearize fe))
    
end
