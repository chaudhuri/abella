(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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

open Accumulate
open Extensions
open Abella_types
open Format

module H = Hashtbl

let get_thm_depend filename =
  let lexbuf = lexbuf_from_file (filename ^ ".thm") in
  let specs = ref [] in
  let load_path = ref (Filename.dirname filename) in
  let normalize_filename fn =
    if Filename.is_relative fn then Filename.concat !load_path fn else fn in
  let imports = ref [] in
    begin try
      while true do
        match (Parser.any_command_start Lexer.token lexbuf).el with
          | ATopCommand(Specification(s, _)) ->
              specs := normalize_filename s :: !specs
          | ATopCommand(Import(i, _, _)) ->
              imports := normalize_filename i :: !imports
          | ACommon(Set("load_path", QStr lp)) ->
              load_path := lp
          | _ -> ()
      done
    with
      | End_of_file -> ()
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position lexbuf) ;
          exit 1
    end ;
    (List.rev !specs, List.rev !imports)

let sig_depend_cache = H.create 10
let mod_depend_cache = H.create 10

let rec get_sig_depend filename =
  try
    match H.find sig_depend_cache filename with
      | None ->
          eprintf "Error: Cyclic dependency in %s.sig\n%!" filename ;
          exit 1
      | Some deps -> deps
  with
    | Not_found ->
        H.add sig_depend_cache filename None ;
        let Sig { accum_sig ; _ } = read_lpsig filename in
        let deps =
          (filename ^ ".sig") :: (List.flatten_map get_sig_depend_ accum_sig)
        in
          H.replace sig_depend_cache filename (Some deps) ;
          deps

and get_sig_depend_ wpos = get_sig_depend wpos.el

let rec get_mod_depend filename =
  try
    match H.find mod_depend_cache filename with
      | None ->
          eprintf "Error: Cyclic dependency in %s.mod\n%!" filename ;
          exit 1
      | Some deps -> deps
  with
    | Not_found ->
        H.add mod_depend_cache filename None ;
        let Mod { accum ; _ } = read_lpmod filename in
        let deps =
          (filename ^ ".mod") ::
            (get_sig_depend filename @
               List.flatten_map get_mod_depend_ accum) in
          H.replace mod_depend_cache filename (Some deps) ;
          deps

and get_mod_depend_ wpos = get_mod_depend wpos.el

let print_deps filename =
  let filename = Filename.chop_extension filename in
  let (specs, imports) = get_thm_depend filename in
  let spec_depends =
    List.unique (List.flatten_map get_sig_depend specs @
                   List.flatten_map get_mod_depend specs)
  in
  let depends =
    sprintf "%s.thm %s %s"
      filename
      (String.concat " " (List.map (fun i -> i ^ ".thc") imports))
      (String.concat " " spec_depends)
  in
    printf "%s.thc: %s\n%!" filename depends ;
    printf "%s.out: %s\n%!" filename depends
