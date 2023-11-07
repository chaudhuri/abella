(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

module Edit = struct
  [@@@warning "-69-34-37-32"]

  type t = { left : int ; right : int ; repl : string }
  let equal e1 e2 =
    e1.left = e2.left && e1.right = e2.right && e1.repl = e2.repl
  let compare e1 e2 = Int.compare e1.left e2.left
end

let rewrite ~edits txt =
  let edits = List.sort Edit.compare edits in
  let len = String.length txt in
  let buf = Buffer.create len in
  let rec spin cur edits =
    if cur >= len then Buffer.contents buf else
    match edits with
    | ed :: edits ->
        Buffer.add_string buf (String.sub txt cur Edit.(ed.left - cur)) ;
        Buffer.add_string buf ed.repl ;
        spin ed.right edits
    | [] ->
        Buffer.add_string buf (String.sub txt cur (len - cur)) ;
        spin len []
  in
  spin 0 edits

let ipfs_add_file file =
  let cmd = Printf.sprintf "ipfs add --cid-version=1 -Q %s" file in
  String.trim @@ run_command cmd

let ipfs_add_string str =
  let (nf, oc) = Filename.open_temp_file "abella" ".ipfs"
      ~mode:Stdlib.[Open_creat ; Open_binary]
      ~perms:0o644
      ~temp_dir:Xdg.cache_dir in
  Stdlib.output_string oc str ;
  Stdlib.close_out oc ;
  let cid = ipfs_add_file nf in
  Sys.remove nf ;
  cid

let ipfs_add_json json = ipfs_add_string @@ Json.(*pretty_*)to_string json

(******************************************************************************)

let seen_thm : (string, string option) Hashtbl.t = Hashtbl.create 19
let seen_lp : (string, string option) Hashtbl.t = Hashtbl.create 19

let todo : string list ref = ref []
let add path = todo := path :: !todo

let _bad_path_rex = "^(https?://|ipfs:).*$" |> Re.Pcre.regexp

let rec process recursive path =
  let stat = Unix.(stat path) in
  match stat.st_kind with
  | S_DIR when recursive ->
      process_directory recursive path
  | S_REG ->
      ignore @@ process_thm recursive path
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

and process_thm recursive path =
  match Hashtbl.find seen_thm path with
  | Some cid -> Some cid
  | exception Not_found ->
      Hashtbl.replace seen_thm path None ;
      let cid = process_thm_ recursive path in
      Hashtbl.replace seen_thm path cid ;
      cid
  | None ->
      failwithf "THM: cycle"

and process_thm_ recursive path =
  let kind = "process_thm" in
  Output.trace ~v:5 begin fun (module Trace) ->
    Trace.printf ~kind "recursive:%b path:%s" recursive path
  end ;
  if Filename.check_suffix path ".thm" then begin
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.printf ~kind "TODO: %s" path
    end ;
    let ch = Stdlib.open_in_bin path in
    let contents = read_all ch in
    let lb = Lexing.from_string ~with_positions:true contents in
    let edits : Edit.t list ref = ref [] in
    let rec spin wrt =
      let cmd = Parser.any_command_start Lexer.token lb in
      let wrt = match cmd.el with
        | ATopCommand (TopCommon (Set ("load_path", QStr lp)))
        | ACommand (Common (Set ("load_path", QStr lp)))
        | ACommon (Set ("load_path", QStr lp)) ->
            Filepath.normalize ~wrt lp
        | ATopCommand (Import (thm_file, (left, right), _)) -> begin
            let left = left.pos_cnum in
            let right = right.pos_cnum in
            let orig = String.sub contents left (right - left) in
            let repl = Filepath.normalize ~wrt thm_file ^ ".thm" in
            match process_thm recursive repl with
            | Some repl ->
                let repl = Printf.sprintf "\"ipfs:%s\" /* %s */" repl orig in
                let edit = Edit.{ left ; right ; repl } in
                edits := edit :: !edits ;
                Output.trace ~v:2 begin fun (module Trace) ->
                  Trace.format ~kind "@[<v2>IMPORT[%d-%d]: %s@,orig: %s@,repl: %s@]"
                    left right thm_file orig repl
                end
            | None -> failwithf "Loading THM: %s" repl
          end ; wrt
        | ATopCommand (Specification (lp_base, (left, right))) -> begin
            let left = left.pos_cnum in
            let right = right.pos_cnum in
            let orig = String.sub contents left (right - left) in
            let repl = Filepath.normalize ~wrt lp_base in
            match process_lp repl with
            | Some repl ->
                let repl = Printf.sprintf "\"ipfs:%s\" /* %s */" repl orig in
                let edit = Edit.{ left ; right ; repl } in
                edits := edit :: !edits ;
                Output.trace ~v:2 begin fun (module Trace) ->
                  Trace.format ~kind "@[<v2>SPECIFICATION[%d-%d]: %s@,orig: %s@,repl: %s@]"
                    left right lp_base orig repl
                end
            | None -> failwithf "Loading LP: %s" repl
          end ; wrt
        | _ -> wrt
      in spin wrt
    in
    let () = try spin path with
      | Parser.Error
      | Abella_types.Reported_parse_error
      | End_of_file -> ()
    in
    let cid = ipfs_add_string @@ rewrite ~edits:!edits contents in
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.format ~kind "@[<v0>THM: %s@,cid: %s@]" path cid ;
    end ;
    Some cid
  end else begin
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.printf ~kind "IGNORE: %s" path
    end ; None
  end

and process_lp lp =
  match Hashtbl.find seen_lp lp with
  | Some cid -> Some cid
  | exception Not_found ->
      Hashtbl.replace seen_lp lp None ;
      let cid = process_lp_ lp in
      Hashtbl.replace seen_lp lp cid ;
      cid
  | None -> failwithf "LP: cycle"

and process_lp_ lp =
  let kind = "process_lp" in
  let lp_base = Filename.basename lp in
  let sigs = Depend.(lp_dependencies (module LPSig) lp) in
  let mods = Depend.(lp_dependencies (module LPMod) lp) in
  let json = `Assoc [ "main", `String lp_base ;
                      "files", `List (
                        List.map begin fun file ->
                          let file_base = Filename.basename file in
                          let contents = read_file file in
                          `Assoc [ "name", `String file_base ;
                                   "contents", `String contents ]
                        end (sigs @ mods)
                      ) ;
                    ] in
  let cid = ipfs_add_json json in
  Output.trace ~v:2 begin fun (module Trace) ->
    Trace.format ~kind "@[<v0>LP: %s@,cid: %s@]" lp_base cid ;
  end ;
  Some cid

let abella_ipfs_store annotation verbosity recursive paths =
  Output.trace_verbosity := verbosity ;
  if annotation then Output.annotation_mode () ;
  List.iter add paths ;
  let rec spin () =
    match !todo with
    | [] -> ()
    | p :: ps ->
        todo := ps ;
        process recursive p ;
        spin ()
  in
  spin () ;
  Hashtbl.iter begin fun fil cid ->
    match cid with
    | Some cid ->
        Output.msg_format "@[<v0>THM: %s@,CID: %s@]" fil cid
    | None ->
        Output.msg_printf "BAD THM: %s" fil
  end seen_thm ;
  Hashtbl.iter begin fun fil cid ->
    match cid with
    | Some cid ->
        Output.msg_format "@[<v0>LP: %s@,CID: %s@]" fil cid
    | None ->
        Output.msg_printf "BAD LP: %s" fil
  end seen_lp ; 0

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
