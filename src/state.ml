(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

open Extensions

type cell = unit -> unit
type snap = (unit -> unit) list

let __snappers : (unit -> unit -> unit) list ref = ref []

exception Killme

let rref x =
  let xr = ref x in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some xr) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some xr ->
        let y = !xr in
        fun () -> xr := y
  in
  __snappers := snap :: !__snappers ; xr

let table () =
  let ht = Hashtbl.create 19 in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some ht) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some ht ->
        let saved = Hashtbl.copy ht in
        fun () -> Hashtbl.assign ht saved
  in
  __snappers := snap :: !__snappers ; ht

let make ~copy ~assign x =
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some x) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some x ->
        let saved = copy x in
        fun () -> assign x saved
  in
  __snappers := snap :: !__snappers ;
  x

let snapshot () : snap =
  let (snap, snappers) = List.fold_left begin fun (snap, snappers) next ->
    try ((next () :: snap), (next :: snappers)) with
    | Killme -> (snap, snappers)
  end ([], []) !__snappers in
  __snappers := snappers ;
  snap

let reload (snap : snap) = List.iter (fun f -> f ()) snap

module Undo = struct
  let enabled = ref true

  let set_enabled en = enabled := en

  let stack : snap list ref = ref []

  let reset () =
    stack := []

  let undo () =
    if !enabled then begin
      match !stack with
      | [] -> failwith "Nothing left to undo"
      | prev :: older ->
          reload prev ;
          stack := older
    end

  let push () =
    if !enabled then begin
      stack := snapshot () :: !stack
    end

  let back n0 =
    if !enabled then begin
      let rec spin hist n =
        match hist, n with
        | (here :: hist), 1 ->
            reload here ;
            stack := hist
        | (_ :: hist), n ->
            spin hist (n - 1)
        | [], _ ->
            failwith "Cannot go that far back!"
      in
      spin !stack n0
    end
end
