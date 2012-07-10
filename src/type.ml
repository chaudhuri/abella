(****************************************************************************)
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

open Extensions

type ki = int

type ty = Ty of ty list * aty

and aty =
  | Tyvar of string
  | Tycon of string * ty list

let aty_head = function
  | Tyvar v
  | Tycon (v, _) -> v

let tyarrow tys ty =
  match ty with
    | Ty (tys', bty) -> Ty (tys @ tys', bty)

let tybase bty targs =
  Ty([], Tycon (bty, targs))

let tyvar tv =
  Ty ([], Tyvar tv)

let is_tyvar = function
  | Tyvar _ -> true
  | _ -> false

let fresh =
  let count = ref 0 in
    fun () ->
      incr count ;
      Tyvar (Printf.sprintf "'%d" !count)

let fresh_tyvar () = Ty ([], fresh ())

let ki_to_string ki =
  let buf = Buffer.create 19 in
  for i = 1 to ki do
    Buffer.add_string buf "type -> "
  done ;
  Buffer.add_string buf "type" ;
  Buffer.contents buf

let to_string ty =
  let buf = Buffer.create 19 in
  let rec p_args tys =
    match tys with
    | [] -> ()
    | ty :: tys ->
        p_ty true ty ;
        Buffer.add_string buf " -> " ;
        p_args tys
  and p_ty is_nested (Ty (tys, aty)) =
    let need_parens = is_nested && tys <> [] in
    if need_parens then Buffer.add_char buf '(' ;
    p_args tys ; p_aty aty ;
    if need_parens then Buffer.add_char buf ')'
  and p_aty aty =
    match aty with
    | Tyvar s
    | Tycon (s, []) ->
        Buffer.add_string buf s
    | Tycon (s, tys) ->
        Buffer.add_string buf s ;
        List.iter begin fun ty ->
          Buffer.add_char buf ' ' ;
          p_ty true ty
        end tys
  in
  p_ty false ty ;
  Buffer.contents buf

let freshen ty =
  let rec sweep_ty fmap (Ty (tys, aty)) =
    let (fmap, tys) = sweep_tys fmap tys in
    let (fmap, aty) = sweep_aty fmap aty in
    (fmap, Ty (tys, aty))
  and sweep_tys fmap tys =
    let (fmap, tys) = List.fold_left begin
      fun (fmap, tys) ty ->
        let (fmap, ty) = sweep_ty fmap ty in
        (fmap, ty :: tys)
    end (fmap, []) tys in
    (fmap, List.rev tys)
  and sweep_aty fmap aty =
    match aty with
    | Tyvar v ->
        begin
          try (fmap, IdMap.find v fmap)
          with Not_found ->
            let fv = fresh () in
            let fmap = IdMap.add v fv fmap in
            (fmap, fv)
        end
    | Tycon (k, tys) ->
        let (fmap, tys) = sweep_tys fmap tys in
        (fmap, Tycon (k, tys))
  in
  snd (sweep_ty IdMap.empty ty)

let varify n =
  let rec digs k ds n =
    if n < 26 then (k, (n :: ds))
    else digs (k + 1) (n mod 26 :: ds) (n / 26 - 1)
  in
  let (k, ds) = digs 0 [] n in
  let ds = ref ds in
  let str = String.create (k + 1) in
  for i = 0 to k do
    match !ds with
    | d :: rest ->
        ds := rest ;
        str.[i] <- Char.chr (65 + d)
    | _ -> assert false
  done ;
  str

let renumber ty =
  let mapping = ref IdMap.empty in
  let last = ref 0 in
  let rec sweep_ty (Ty (tys, aty)) =
    let tys = sweep_tys tys in
    let aty = sweep_aty aty in
    Ty (tys, aty)
  and sweep_tys tys = List.map sweep_ty tys
  and sweep_aty aty =
    match aty with
    | Tyvar v ->
        begin match IdMap.find_opt v !mapping with
        | Some aty -> aty
        | None ->
            let next = Tyvar (varify !last) in
            incr last ;
            mapping := IdMap.add v next !mapping ;
            next
        end
    | Tycon (k, tys) ->
        Tycon (k, sweep_tys tys)
  in
  sweep_ty ty

let equal_modulo tya tyb =
  let mapped = ref IdMap.empty in
  let used = ref IdSet.empty in
  let rec sweep_ty (Ty (tysa, atya)) (Ty (tysb, atyb)) =
    sweep_tys tysa tysb && sweep_aty atya atyb
  and sweep_tys tysa tysb =
    match tysa, tysb with
    | [], [] -> true
    | (tya :: tysa), (tyb :: tysb) ->
        sweep_ty tya tyb
        && sweep_tys tysa tysb
    | _ -> false
  and sweep_aty atya atyb =
    match atya, atyb with
    | Tyvar u, _ when IdMap.mem u !mapped ->
        sweep_aty (IdMap.find u !mapped) atyb
    | Tyvar u, Tyvar v when not (IdSet.mem v !used) ->
        mapped := IdMap.add u atyb !mapped ;
        used := IdSet.add v !used ;
        true
    | Tycon (j, tysa), Tycon (k, tysb) when j = k ->
        sweep_tys tysa tysb
    | _ -> false
  in
  sweep_ty tya tyb

type decl =
  | Kind of ki
  | Type of ty

type sign = {
  order : string list ;
  decls : decl IdMap.t ;
}

let oty = tybase "o" []
let olistty = tybase "olist" []
let propty = tybase "prop" []
let listty a = tybase "list" [a]

let get_kind sg tc =
  match IdMap.find_opt tc sg.decls with
  | Some (Kind ki) -> ki
  | _ ->
      failwithf ~exc:"get_kind"
        "Unknown type constructor: %s" tc

let add_types sg tcs ki =
  let exc = "add_types" in
  let sg = List.fold_left begin
    fun sg tc ->
      match IdMap.find_opt tc sg.decls with
      | Some (Kind ki') ->
          if ki <> ki' then
            failwithf ~exc
              "Type constructor %s already declared with different kind %s"
              tc (ki_to_string ki') ;
          sg
      | Some _ ->
          failwithf ~exc
            "Type constructor %s already present in signature" tc
      | _ ->
          { order = tc :: sg.order ;
            decls = IdMap.add tc (Kind ki) sg.decls }
  end sg tcs in
  sg

let get_type sg kon =
  match IdMap.find_opt kon sg.decls with
  | Some (Type ty) -> ty
  | _ ->
      failwithf ~exc:"get_type"
        "Unknown constant: %s" kon

let check_kind sg ty =
  let rec ok ty =
    match ty with
    | Ty (tys, Tyvar gv) ->
        List.iter ok tys
    | Ty (tys, Tycon (tc, tcargs)) ->
        List.iter ok tys ;
        let ki_exp = get_kind sg tc in
        let ki_gpt = List.length tcargs in
        if ki_exp <> ki_gpt then
          failwithf ~exc:"get_kind"
            "Type constructor %s expects %d arg(s), but got %d"
            tc ki_exp ki_gpt ;
        List.iter ok tcargs
  in
  ok ty

let add_consts sg kons ty =
  let exc = "add_consts" in
  check_kind sg ty ;
  let ty = renumber ty in
  let sg = List.fold_left begin
    fun sg kon ->
      match IdMap.find_opt kon sg.decls with
      | Some (Type ty') ->
          if ty <> ty' then
            failwithf ~exc
              "Constant %s already declared with incomparable type %s"
              kon (to_string ty') ;
          sg
      | Some _ ->
          failwithf ~exc
            "Constant %s already present in signature" kon
      | _ ->
          { order = kon :: sg.order ;
            decls = IdMap.add kon (Type ty) sg.decls }
  end sg kons in
  sg

let sign_to_string sg =
  let maxstr = List.fold_left
    (fun m d -> Pervasives.max m (String.length d)) 0 sg.order in
  let buf = Buffer.create 19 in
  List.iter begin fun d ->
    match IdMap.find d sg.decls with
    | Kind ki ->
        Printf.bprintf buf "Kind  %-*s  %s.\n"
          maxstr d (ki_to_string ki)
    | Type ty ->
        Printf.bprintf buf "Type  %-*s  %s.\n"
          maxstr d (to_string ty)
  end (List.rev sg.order) ;
  Buffer.contents buf

let process sg decls =
  List.fold_left begin fun sg decl ->
    match decl with
    | (tcs, Kind ki) ->
        add_types sg tcs ki
    | (kons, Type ty) ->
        add_consts sg kons ty
  end sg decls

let spec_pervasives = 
  process { order = [] ; decls = IdMap.empty }
    [ ["o"],            Kind 0
    ; ["=>"],           Type (tyarrow [oty ; oty] oty)
    ; ["pi" ; "sigma"], Type (tyarrow [tyarrow [tyvar "A"] oty] oty) ]

let import_spec_sign sg =
  process sg
    [ ["prop"],   Kind 0
    ; ["list"],   Kind 1
    ; ["nil"],    Type (listty (tyvar "A"))
    ; ["::"],     Type (tyarrow [tyvar "A" ; listty (tyvar "A")] (listty (tyvar "A")))
    ; ["member"], Type (tyarrow [tyvar "A" ; listty (tyvar "A")] propty) ]
