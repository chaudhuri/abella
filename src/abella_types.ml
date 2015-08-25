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

open Metaterm
open Term
open Typing
open Extensions

type uclause = string option * uterm * uterm list
type clause = term

type flavor = Inductive | CoInductive

type udef_clause = umetaterm * umetaterm
type def_clause = {
  head : metaterm ;
  body : metaterm ;
}
type def = {
  flavor   : flavor ;
  typarams : string list ;
  mutual   : ty Itab.t ;
  clauses  : def_clause list ;
}
type defs_table = (string, def) Hashtbl.t

type id = string

exception Reported_parse_error

type set_value =
  | Str of string
  | Int of int
  | QStr of string

type clearable =
  | Keep of id * ty list
  | Remove of id * ty list

type common_command =
  | Back | Reset
  | Set of string * set_value
  | Show of string
  | Quit

type 'term schema = {
  sch_name    : id ;
  sch_arity   : int ;
  sch_ty      : ty ;
  sch_blocks  : 'term block list ;
}

and 'term block = {
  bl_exists : tyctx ;
  bl_nabla  : tyctx ;
  bl_rel    : 'term list list ;
}

type top_command =
  | Theorem of id * string list * umetaterm
  | Define of flavor * tyctx * udef_clause list
  | Schema of uterm schema
  | Import of string
  | Specification of string
  | Query of umetaterm
  | Kind of id list
  | Type of id list * ty
  | Close of id list
  | SSplit of id * id list
  | TopCommon of common_command

type compiled =
  | CTheorem of id * string list * metaterm
  | CDefine of flavor * string list * tyctx * def_clause list
  | CSchema of term schema
  | CImport of string
  | CKind of id list
  | CType of id list * ty
  | CClose of (id * id list) list

type witness =
  | WTrue
  | WHyp of id
  | WLeft of witness
  | WRight of witness
  | WSplit of witness * witness
  | WForall of id list * witness
  | WIntros of id list * witness
  | WExists of (id * term) list * witness
  | WReflexive
  | WUnfold of id * int * witness list
  | WMagic

let witness_to_string =
  let bind_to_string (id, t) =
    id ^ " = " ^ term_to_string t
  in

  let rec aux = function
    | WTrue -> "true"
    | WHyp id -> "apply " ^ id
    | WLeft w -> "left " ^ aux w
    | WRight w -> "right " ^ aux w
    | WSplit(w1,w2) -> "split(" ^ aux w1 ^ ", " ^ aux w2 ^ ")"
    | WForall(ids,w) ->
        "forall[" ^ (String.concat ", " ids) ^ "] " ^ aux w
    | WIntros(ids,w) ->
        "intros[" ^ (String.concat ", " ids) ^ "] " ^ aux w
    | WExists(binds,w) ->
        "exists[" ^ (String.concat ", " (List.map bind_to_string binds)) ^
        "] " ^ aux w
    | WReflexive -> "="
    | WUnfold(id,n,ws) ->
        let ws = List.map aux ws |> String.concat ", " in
        Printf.sprintf "unfold(%s, %d, %s)" id n ws
    | WMagic -> "*"
  in
  aux

type depth_bound = int

type command =
  | Induction of int list * id option
  | CoInduction of id option
  | Apply of clearable * clearable list * (id * uterm) list * id option
  | Backchain of depth_bound option * clearable * (id * uterm) list
  | CutFrom of clearable * clearable * uterm * id option
  | Cut of clearable * clearable * id option
  | SearchCut of clearable * id option
  | Inst of clearable * (id * uterm) list * id option
  | Case of clearable * id option
  | Assert of umetaterm * id option
  | Pick of depth_bound option * (id * ty) list * umetaterm
  | Exists of [`EXISTS | `WITNESS] * uterm
  | Clear of id list
  | Abbrev of id * string
  | Unabbrev of id list
  | Rename of id * id
  | Monotone of clearable * uterm
  | Permute of id list * id option
  | Search of [`nobounds | `depth of depth_bound | `witness of witness]
  | Split
  | SplitStar
  | Left
  | Right
  | Intros of id list
  | Unfold of clause_selector * solution_selector
  | Skip
  | Abort
  | Undo
  | Common of common_command

and clause_selector =
  | Select_any
  | Select_num of int
  | Select_named of string

and solution_selector =
  | Solution_first
  | Solution_all

type any_command =
  | ATopCommand of top_command
  | ACommand of command
  | ACommon of common_command

type sig_decl =
  | SKind of id list
  | SType of id list * ty

type lpsig =
  | Sig of string * string list * sig_decl list

type lpmod =
  | Mod of string * string list * uclause list

let udef_to_string (head, body) =
  if body = UTrue then
    umetaterm_to_string head
  else
    Printf.sprintf "%s := %s" (umetaterm_to_string head)
      (umetaterm_to_formatted_string body)

let udef_clauses_to_string cls =
  String.concat ";\n" (List.map udef_to_string cls)

let flavor_to_string dtype =
  match dtype with
    | Inductive -> "inductive"
    | CoInductive -> "coinductive"

let set_value_to_string v =
  match v with
    | Str s -> s
    | Int d -> string_of_int d
    | QStr s -> Printf.sprintf "%S" s

let id_list_to_string ids =
  String.concat ", " ids

let idtys_to_string idtys =
  String.concat ",\t\n"
    (List.map (fun (id, ty) -> id ^ " : " ^ (ty_to_string ty)) idtys)

let inst_to_string tys =
  match tys with
  | [] -> ""
  | _ -> "[" ^ (List.map ty_to_string tys |> String.concat ",") ^ "]"

let clearable_to_string cl =
  match cl with
  | Keep (h, tys) -> h ^ inst_to_string tys
  | Remove (h, tys) -> "*" ^ h ^ inst_to_string tys

let common_command_to_string cc =
  match cc with
  | Back ->
      Printf.sprintf "#<back>"
  | Reset ->
      Printf.sprintf "#<reset>"
  | Set(k, v) ->
      Printf.sprintf "Set %s %s" k (set_value_to_string v)
  | Show nm ->
      Printf.sprintf "Show %s" nm
  | Quit ->
      Printf.sprintf "Quit"

let block_to_string t2s bl =
  let buf = Buffer.create 19 in
  let add s = Buffer.add_string buf s in
  let space () = add " " in
  if bl.bl_exists <> [] then begin
    add "exists " ;
    List.iter_sep ~sep:space (fun (v, ty) -> add v) bl.bl_exists ;
    add "," ;
    if bl.bl_nabla <> [] then add " " ;
  end ;
  if bl.bl_nabla <> [] then begin
    add "nabla " ;
    List.iter_sep ~sep:space (fun (v, ty) -> add v) bl.bl_nabla ;
    add ","
  end ;
  add " (" ;
  List.iter_sep ~sep:(fun () -> add ", ") begin fun ctx ->
    if ctx = [] then add "nil" else
    List.iter_sep ~sep:(fun () -> add " :: ") begin fun tm ->
      add (t2s tm)
    end ctx
  end bl.bl_rel ;
  add ")" ;
  Buffer.contents buf

let gen_to_string tys =
  match tys with
  | [] -> ""
  | _ -> " [" ^ String.concat "," tys ^ "]"

let top_command_to_string tc =
  match tc with
    | Theorem(name, tys, body) ->
        Printf.sprintf "Theorem %s%s : \n%s" name (gen_to_string tys)
          (umetaterm_to_formatted_string body)
    | Define(flavor, idtys, cls) ->
        Printf.sprintf "%s %s by \n%s"
          (match flavor with Inductive -> "Define" | _ -> "CoDefine")
          (idtys_to_string idtys) (udef_clauses_to_string cls) ;
    | Schema sch ->
        Printf.sprintf "Schema %s := %s" sch.sch_name
          (sch.sch_blocks |>
           List.map (fun bl -> block_to_string uterm_to_string bl) |>
           String.concat "; ")
    | Import filename ->
        Printf.sprintf "Import \"%s\"" filename
    | Specification filename ->
        Printf.sprintf "Specification \"%s\"" filename
    | Query q ->
        Printf.sprintf "Query %s" (umetaterm_to_formatted_string q)
    | Kind ids ->
        Printf.sprintf "Kind %s type" (id_list_to_string ids)
    | Type(ids, ty) ->
        Printf.sprintf "Type %s %s" (id_list_to_string ids) (ty_to_string ty)
    | Close ids ->
        Printf.sprintf "Close %s" (id_list_to_string ids)
    | SSplit(id, ids) ->
        if ids <> [] then
          Printf.sprintf "Split %s as %s" id (id_list_to_string ids)
        else
          Printf.sprintf "Split %s" id
    | TopCommon(cc) ->
        common_command_to_string cc

let withs_to_string ws =
  String.concat ", "
    (List.map (fun (x,t) -> x ^ " = " ^ (uterm_to_string t)) ws)

let hn_to_string = function
  | None -> ""
  | Some hn -> Printf.sprintf "%s : " hn

let clearables_to_string cls =
  List.map clearable_to_string cls |> String.concat " "

let dbound_to_string = function
  | None -> ""
  | Some n -> " " ^ string_of_int n

let command_to_string c =
  match c with
    | Induction(is, hn) ->
        Printf.sprintf "%sinduction on %s" (hn_to_string hn)
          (String.concat " " (List.map string_of_int is))
    | CoInduction None -> "coinduction"
    | CoInduction (Some hn) -> "coinduction " ^ hn
    | Apply(h, [], [], hn) ->
        Printf.sprintf "%sapply %s" (hn_to_string hn)
          (clearable_to_string h)
    | Apply(h, hs, [], hn) ->
        Printf.sprintf "%sapply %s to %s"
          (hn_to_string hn)
          (clearable_to_string h)
          (clearables_to_string hs)
    | Apply(h, [], ws, hn) ->
        Printf.sprintf "%sapply %s with %s"
          (hn_to_string hn)
          (clearable_to_string h)
          (withs_to_string ws)
    | Apply(h, hs, ws, hn) ->
        Printf.sprintf "%sapply %s to %s with %s"
          (hn_to_string hn)
          (clearable_to_string h)
          (clearables_to_string hs)
          (withs_to_string ws)
    | Backchain(dbound, h, []) ->
        Printf.sprintf "backchain%s %s"
          (dbound_to_string dbound)
          (clearable_to_string h)
    | Backchain(dbound, h, ws) ->
        Printf.sprintf "backchain%s %s with %s"
          (dbound_to_string dbound)
          (clearable_to_string h)
          (withs_to_string ws)
    | Cut(h1, h2, hn) ->
        Printf.sprintf "%scut %s with %s"
          (hn_to_string hn)
          (clearable_to_string h1)
          (clearable_to_string h2)
    | CutFrom(h, arg, t, hn) ->
        Printf.sprintf "%scut %s from %s with %s"
          (hn_to_string hn) (uterm_to_string t)
          (clearable_to_string h)
          (clearable_to_string arg)
    | SearchCut(h, hn) ->
        Printf.sprintf "%s cut %s" (hn_to_string hn)
          (clearable_to_string h)
    | Inst(h, ws, hn) ->
        Printf.sprintf "%s inst %s with %s" (hn_to_string hn)
          (clearable_to_string h)
          (withs_to_string ws)
    | Case(Keep (h, _), hn) ->
        Printf.sprintf "%scase %s (keep)" (hn_to_string hn) h
    | Case(Remove (h, _), hn) ->
        Printf.sprintf "%scase %s" (hn_to_string hn) h
    | Assert(t, hn) ->
        Printf.sprintf "%sassert %s"
          (hn_to_string hn)
          (umetaterm_to_formatted_string t)
    | Pick (dbound, bs, t) ->
        Printf.sprintf "pick%s %s, %s"
          (dbound_to_string dbound)
          (idtys_to_string bs)
          (umetaterm_to_formatted_string t)
    | Exists (how, t) ->
        let hows = match how with
          | `EXISTS -> "exists"
          | `WITNESS -> "witness"
        in
        Printf.sprintf "%s %s" hows (uterm_to_string t)
    | Clear hs ->
        Printf.sprintf "clear %s" (String.concat " " hs)
    | Abbrev(h, s) ->
        Printf.sprintf "abbrev %s \"%s\"" h s
    | Unabbrev hs ->
        Printf.sprintf "unabbrev %s" (String.concat " " hs)
    | Rename(hfrom, hto) ->
        Printf.sprintf "rename %s to %s" hfrom hto
    | Monotone(h, t) ->
        Printf.sprintf "monotone %s with %s"
          (clearable_to_string h)
          (uterm_to_string t)
    | Permute(ids, t) ->
        Printf.sprintf "permute (%s)%s"
          (String.concat " " ids)
          (match t with None -> "" | Some h -> " " ^ h)
    | Search(`nobounds) -> "search"
    | Search(`depth d) -> Printf.sprintf "search %d" d
    | Search(`witness w) -> Printf.sprintf "search with %s" (witness_to_string w)
    | Split -> "split"
    | SplitStar -> "split*"
    | Left -> "left"
    | Right -> "right"
    | Unfold (clause_sel, sol_sel) ->
        Printf.sprintf "unfold%s%s"
          (match clause_sel with
           | Select_any -> ""
           | Select_num n -> " " ^ string_of_int n
           | Select_named n -> " " ^ n)
          (match sol_sel with
           | Solution_first -> ""
           | Solution_all -> " (all)")
    | Intros [] -> "intros"
    | Intros ids -> Printf.sprintf "intros %s" (String.concat " " ids)
    | Skip -> "skip"
    | Abort -> "abort"
    | Undo -> "undo"
    | Common(cc) -> common_command_to_string cc
