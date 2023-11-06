(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

let seen : (string, string option) Hashtbl.t = Hashtbl.create 19
let todo : string list ref = ref []
let add path = todo := path :: !todo

let rec process recursive path =
  let stat = Unix.(stat path) in
  match stat.st_kind with
  | S_DIR when recursive ->
      process_directory recursive path
  | S_REG ->
      process_file recursive path
  | _ ->
      Output.trace ~v:2 begin fun (module Trace) ->
        Trace.printf ~kind:"process" "IGNORE: %s" path
      end

and process_directory recursive path =
  let kind = "process_directory" in
  Output.trace ~v:5 begin fun (module Trace) ->
    Trace.printf ~kind "recursive:%b path:%s" recursive path
  end ;
  let fs = Sys.readdir path in
  Array.fast_sort String.compare fs ;
  Array.iter (fun sub -> process recursive (Filename.concat path sub)) fs

and process_file recursive path =
  let kind = "process_file" in
  Output.trace ~v:5 begin fun (module Trace) ->
    Trace.printf ~kind "recursive:%b path:%s" recursive path
  end ;
  if Hashtbl.mem seen path then () else
  let () = Hashtbl.replace seen path None in
  if Filename.check_suffix path ".thm" then begin
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.printf ~kind "TODO: %s" path
    end ;
    let ch = Stdlib.open_in_bin path in
    let contents = read_all ch in
    let lb = Lexing.from_string ~with_positions:true contents in
    let rec spin () =
      let cmd = Parser.any_command_start Lexer.token lb in
      let () = match cmd.el with
        | ATopCommand (Import (thm_file, (left, right), _)) ->
            Output.trace ~v:2 begin fun (module Trace) ->
              Trace.printf ~kind "IMPORT[%d-%d]: %s"
                left.pos_cnum right.pos_cnum
                thm_file
            end ;
        | _ -> ()
      in
      spin ()
    in
    try spin () with
    | Parser.Error
    | Abella_types.Reported_parse_error
    | End_of_file -> ()
  end else
  Output.trace ~v:2 begin fun (module Trace) ->
    Trace.printf ~kind "IGNORE: %s" path
  end

let abella_ipfs_store annotation verbosity recursive paths =
  Output.trace_verbosity := verbosity ;
  if annotation then Output.annotation_mode () ;
  List.iter add paths ;
  let rec spin () =
    match !todo with
    | [] -> 0
    | p :: ps ->
        todo := ps ;
        process recursive p ;
        spin ()
  in
  spin ()

(******************************************************************************)
(* Command line parsing *)

let () =
  let open Cmdliner in
  let annotation =
    let doc = "Annotation mode." in
    Arg.(value @@ flag @@ info ["a" ; "annotate"] ~doc)
  in
  let recursive =
    let doc = "Process directories recursively." in
    Arg.(value @@ flag @@ info ["r"] ~doc)
  in
  let verbosity =
    let doc = "Set verbosity to $(docv)." in
    Arg.(value @@ opt int 0 @@
         info ["verbosity"] ~doc ~docv:"NUM")
  in
  let paths =
    let doc = "An Abella $(b,.thm) file or a directory" in
    Arg.(value @@ pos_all string [] @@ info [] ~docv:"SOURCE" ~doc)
  in
  let cmd =
    let doc = "Upload Abella sources to IPFS" in
    let man = [
      `S Manpage.s_examples ;
      `Blocks [
        `P "To upload a.thm, d/b.thm, and c/*.thm" ;
        `Pre "  \\$ $(tname) a.thm d/b.thm c/*.thm" ;
        `P "To upload all .thm files recursively in d/" ;
        `Pre "  \\$ $(tname) -r d" ;
      ] ;
      `S Manpage.s_see_also ;
      `P "$(b,abella)(1)" ;
      `S Manpage.s_bugs ;
      `P "File bug reports at <$(b,https://github.com/abella-prover/abella/issues)>" ;
    ] in
    let info = Cmd.info "abella_ipfs" ~doc ~man ~exits:[] in
    Cmd.v info @@ Term.(const abella_ipfs_store
                        $ annotation
                        $ verbosity
                        $ recursive
                        $ paths)
  in
  let ecode = Cmd.eval' cmd in
  Output.flush () ;
  Stdlib.exit ecode
