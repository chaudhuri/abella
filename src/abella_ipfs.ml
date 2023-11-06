(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

[@@@warning "-69-34-37-32"]

module Edit = struct
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

(******************************************************************************)

let seen : (string, string option) Hashtbl.t = Hashtbl.create 19
let todo : string list ref = ref []
let add path = todo := path :: !todo

let bad_path_rex = "^(https?://|ipfs:).*$" |> Re.Pcre.regexp

let rec process recursive path =
  let stat = Unix.(stat path) in
  match stat.st_kind with
  | S_DIR when recursive ->
      process_directory recursive path
  | S_REG ->
      ignore @@ process_file recursive path
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
  match Hashtbl.find seen path with
  | Some cid -> Some cid
  | exception Not_found -> begin
      Hashtbl.replace seen path None ;
      match process_file_ recursive path with
      | None -> None
      | Some cid ->
          Hashtbl.replace seen path (Some cid) ;
          Some cid
    end
  | None ->
      failwithf "Cycle"

and process_file_ recursive path =
  let kind = "process_file" in
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
            match process_file recursive repl with
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
    let new_contents = rewrite ~edits:!edits contents in
    let (nf, oc) = Filename.open_temp_file "abella" "ipfs"
        ~mode:Stdlib.[Open_creat ; Open_binary] in
    Stdlib.output_string oc new_contents ;
    Stdlib.close_out oc ;
    let cmd = Printf.sprintf "ipfs add -Q %s" nf in
    let cid = String.trim @@ run_command cmd in
    Sys.remove nf ;
    Some cid
  end else begin
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.printf ~kind "IGNORE: %s" path
    end ; None
  end

and process_lp lp =
  let kind = "process_lp" in
  let lp_base = Filename.basename lp in
  let sigs = Depend.(lp_dependencies (module LPSig) lp) in
  let mods = Depend.(lp_dependencies (module LPMod) lp) in
  let (jf, jc) = Filename.open_temp_file "abella_lp" ".json"
      ~perms:0o644 ~mode:Stdlib.[Open_creat] in
  Json.to_channel jc @@ begin
    `Assoc [
      "main", `String lp_base ;
      "files", `List (
        List.map begin fun file ->
          let file_base = Filename.basename file in
          let contents = read_file file in
          `Assoc [ "name", `String file_base ;
                   "contents", `String contents ]
        end (sigs @ mods)
      ) ;
    ]
  end ;
  Stdlib.close_out jc ;
  let cmd = Printf.sprintf "ipfs add -Q %s" jf in
  let cid = String.trim @@ run_command cmd in
  Output.trace ~v:2 begin fun (module Trace) ->
    Trace.format ~kind "@[<v0>LP: %s@,TO: %s@,cid: %s@]" lp_base jf cid ;
  end ;
  Sys.remove jf ;
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
        Output.msg_format "@[<v0>FILE: %s@,CID: %s@]" fil cid
    | None ->
        Output.msg_printf "BADFILE: %s" fil
  end seen ; 0

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
