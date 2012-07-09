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
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty targs =
  Ty([], Tycon (bty, targs))

let tyvar tv =
  Ty ([], Tyvar tv)

let oty = tybase "o" []
let olistty = tybase "olist" []

let is_tyvar = function
  | Tyvar _ -> true
  | _ -> false

let fresh =
  let count = ref 0 in
    fun () ->
      incr count ;
      Tyvar (Printf.sprintf "`%d" !count)

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
  sweep_ty IdMap.empty ty

let eq tya tyb =
  let eqmap = ref IdMap.empty in
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
    | Tyvar u, _ when IdMap.mem u !eqmap ->
        sweep_aty (IdMap.find u !eqmap) atyb
    | Tyvar u, Tyvar _
      when IdMap.for_all (fun _ atyb' -> atyb <> atyb') !eqmap ->
        eqmap := IdMap.add u atyb !eqmap ;
        true
    | Tycon (j, tysa), Tycon (k, tysb) when j = k ->
        sweep_tys tysa tysb
    | _ -> false
  in
  sweep_ty tya tyb

let tya = tyarrow [tyvar "A" ; tyvar "B"] (tybase "foo" [tyvar "C"])
let tyb = tyarrow [tyvar "V" ; tyvar "V"] (tybase "foo" [tyvar "W"])
