(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Dependency generator for Abella *)

let makefile = ref false

let options = Arg.[
    "-M", Set makefile, " Output dependencies in Makefile format"
  ] |> Arg.align

let input_files : string list ref = ref []

let add_input_file file =
  input_files := file :: !input_files

let usage_message =
  Printf.sprintf "Usage: %s [options] <theorem-file> ..."
    (if !Sys.interactive then "abella_dep" else Sys.argv.(0))

let main () =
  Arg.parse options add_input_file usage_message ;
  Printf.printf "Hello, world"

let () =
  if not !Sys.interactive then main ()
