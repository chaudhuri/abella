(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

type source =
  | Local of { path : string }
  | Http of { host : string ; path : string ; secure : bool }
  | Ipfs of { cid : string ; path : string }

let to_string = function
  | Local { path } -> path
  | Http { secure ; host ; path } ->
      Printf.sprintf "http%s://%s/%s"
        (if secure then "s" else "")
        host path
  | Ipfs { cid ; path } ->
      Printf.sprintf "ipfs://%s/%s" cid path

open struct
  let http_rex = "^http(s?)://([^/]+)(/.*)?$" |> Re.Pcre.regexp
  let ipfs_rex = "^ipfs:([^/]+)(/.*)?$" |> Re.Pcre.regexp
end

let of_string =
  let http src =
    match Re.Pcre.extract ~rex:http_rex src with
    | [| _ ; secure ; host ; path |] ->
        let secure = secure = "s" in
        let path = if String.length path > 0 && path.[0] = '/' then
            String.sub path 1 (String.length path - 1)
          else path in
        Option.some @@ Http { secure ; host ; path }
    | _
    | exception Not_found -> None in
  let ipfs src =
    match Re.Pcre.extract ~rex:ipfs_rex src with
    | [| _ ; cid ; path |] ->
        let path = if String.length path > 0 && path.[0] = '/' then
            String.sub path 1 (String.length path - 1)
          else path in
        Option.some @@ Ipfs { cid ; path }
    | _
    | exception Not_found -> None in
  fun path ->
    match Option.first [ http ; ipfs ] path with
    | Some src -> src
    | None -> Local { path }

let load_path = ref @@ Local { path = "." }

(*
let relativize ?(wrt = !load_path) thing =
  let[@inline] ( / ) x y = match x with
    | "." -> y
    | _ -> x ^ "/" ^ y in
  let[@inline] ( // ) x y = match x with
    | "." -> y
    | _ -> Filename.concat x y in
  (* [TODO] improve handling of choices *)
  if Re.Pcre.pmatch ~rex:http_rex thing then begin
    let strs = Re.Pcre.extract ~rex:http_rex thing in
    let secure = strs.(1) = "s" in
    let host = strs.(2) in
    let path = strs.(3) in
    Http { secure ; host ; path }
  end else if Re.Pcre.pmatch ~rex:ipfs_rex thing then begin
    let strs = Re.Pcre.extract ~rex:ipfs_rex thing in
    let cid = strs.(1) in
    Ipfs { cid }
  end else begin
    match wrt with
    | Http ht ->
        if Filename.is_relative thing then
          Http { ht with path = Filename.dirname ht.path / thing }
        else
          Http { ht with path = thing }
    | Ipfs { cid } ->
        if Filename.is_relative thing then
          Ipfs { cid = cid / thing }
        else begin
          Output.trace ~v:1 begin fun (module Trace) ->
            Trace.format ~kind:"Source.relativize"
              "@[<v2>Cannot relativize absolute path: %s@,relative to ipfs://%s@]"
              thing cid
          end ;
          failwith "relativizing: absolute paths wrt IPFS"
        end
    | Local { path } ->
        if Filename.is_relative thing then
          Local { path = Filename.dirname path // thing }
        else
          Local { path = thing }
  end
*)
