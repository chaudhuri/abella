(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

type source =
  | Local of { path : string }
  | Http  of { host : string ; path : string ; secure : bool }
  | Ipfs  of { cid : string ; path : string }

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
        let path = Filename.clean path in
        Option.some @@ Http { secure ; host ; path }
    | _
    | exception Not_found -> None in
  let ipfs src =
    match Re.Pcre.extract ~rex:ipfs_rex src with
    | [| _ ; cid ; path |] ->
        let path = Filename.clean path in
        Option.some @@ Ipfs { cid ; path }
    | _
    | exception Not_found -> None in
  fun path ->
    match Option.first [ http ; ipfs ] path with
    | Some src -> src
    | None -> Local { path }

let load_path = ref @@ Local { path = "." }

open struct
  let[@inline] ( / ) x y = match x with
    | "." -> y
    | _ -> x ^ "/" ^ y
  let[@inline] ( // ) x y = match x with
    | "." -> y
    | _ -> Filename.concat x y
end

let relativize ?(wrt = !load_path) thing =
  (* [TODO] improve handling of choices *)
  let src = of_string thing in
  match src with
  | Http _ | Ipfs _ -> src
  | Local { path = thing } ->
      match wrt with
      | Http ht ->
          if Filename.is_relative thing then
            Http { ht with path = Filename.dirname ht.path / thing }
          else
            Http { ht with path = thing }
      | Ipfs ip ->
          if Filename.is_relative thing then
            Ipfs { ip with path = Filename.dirname ip.path / thing }
          else begin
            Output.trace ~v:1 begin fun () ->
              Output.Trace.format ~kind:"Source.relativize"
                "@[<v2>Cannot relativize absolute path: %s@,relative to ipfs://%s/%s@]"
                thing ip.cid ip.path
            end ;
            failwith "relativizing: absolute paths wrt IPFS"
          end
      | Local { path } ->
          if Filename.is_relative thing then
            Local { path = Filename.dirname path // thing }
          else
            src

open struct
  let wdays = [| "Sun" ; "Mon" ; "Tue" ; "Wed" ; "Thu" ; "Fri" ; "Sat" |]

  let months = [| "Jan" ; "Feb" ; "Mar" ; "Apr" ; "May" ; "Jun" ;
                  "Jul" ; "Aug" ; "Sep" ; "Oct" ; "Nov" ; "Dec" |]

  let abella_agent =
    Printf.sprintf "Abella/%s (using %s)"
      Version.version
      (Curl.version ())

  let http_strftime t =
    let tm = Unix.gmtime t in
    Printf.sprintf "%s, %02d %s %04d %02d:%02d:%02d GMT"
      wdays.(tm.tm_wday)
      tm.tm_mday months.(tm.tm_mon) (tm.tm_year + 1900)
      tm.tm_hour tm.tm_min tm.tm_sec

  let fetch_with_cache url =
    let kind = "Source.fetch" in
    let cache_file = Filename.concat Xdg.cache_dir (Base64.encode_string url) in
    let cl = Curl.init () in
    Gc.finalise Curl.cleanup cl ;
    Curl.set_maxredirs cl 50 ;
    Curl.set_useragent cl abella_agent ;
    Curl.set_followlocation cl true ;
    if Sys.file_exists cache_file then begin
      let mtime = Unix.(stat cache_file).st_mtime |> http_strftime in
      Curl.set_httpheader cl [ "If-Modified-Since: " ^ mtime ]
    end ;
    Curl.set_url cl url ;
    Curl.set_httpget cl true ;
    Curl.set_headerfunction cl String.length ; (* ignore all headers *)
    let response_body = Buffer.create 19 in
    Curl.set_writefunction cl begin fun str ->
      Buffer.add_string response_body str ;
      String.length str
    end ;
    let rec make_attempt n =
      if n <= 0 then failwith "Exceeded attempt count without success" ;
      match Curl.perform cl ; Curl.CURLE_OK with
      | Curl.CURLE_AGAIN -> make_attempt @@ n - 1
      | Curl.CURLE_OK -> begin
          let code = Curl.get_httpcode cl in
          if code = 200 then begin
            let ch = Stdlib.open_out_bin cache_file in
            Buffer.output_buffer ch response_body ;
            Stdlib.close_out ch ;
            Output.trace ~v:2 begin fun () ->
              Output.Trace.format ~kind
                "@[<v2>Cached: %s@,at: %s@,on: %s@]"
                url cache_file
                (http_strftime Unix.((stat cache_file).st_mtime)) ;
            end ;
            cache_file
          end else if code = 304 then begin
            Output.trace ~v:2 begin fun () ->
              Output.Trace.printf ~kind "Cached version is newer (HTTP 304)"
            end ;
            cache_file
          end else failwithf "Unexpected HTTP %d" code
        end
      | code
      | exception Curl.CurlException (code, _, _) ->
          failwith @@ Curl.strerror code
    in
    make_attempt 50
end

module type CACHE = sig
  val path : string
  val mtime : unit -> float
  val contents : unit -> string
  val lex : with_positions:bool -> Lexing.lexbuf
end

let cache src =
  let src_string = to_string src in
  let mk cfile : (module CACHE) =
    let module C = struct
      let path = cfile
      let mtime () = Unix.(stat cfile).st_mtime
      let contents () = read_file cfile
      let lex ~with_positions =
        let lb = Lexing.from_string ~with_positions @@ contents () in
        Lexing.(lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = src_string }) ;
        lb
    end in
    (module C)
  in
  match src with
  | Local { path } -> mk path
  | Http _ -> mk @@ fetch_with_cache src_string
  | Ipfs { cid ; path } ->
      let cache_dir = Filename.concat Xdg.cache_dir cid in
      let cmd = Printf.sprintf "ipfs get --archive --compress --output %s %s"
          cache_dir cid in
      ignore @@ run_command cmd ;
      let cmd = Printf.sprintf "tar -xf %s.tar.gz" cache_dir in
      ignore @@ run_command cmd ;
      Sys.remove @@ Printf.sprintf "%s.tar.gz" cache_dir ;
      mk @@ Filename.concat cache_dir path
