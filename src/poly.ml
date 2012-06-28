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

type ty =
  | Tv    of string
  | Tx    of int
  | Kon   of ty list * string
  | Arr   of ty * ty

type sub =
  | Shift of int
  | Cons  of sub * ty

let rec subst_tx ss n =
  match ss, n with
  | Shift m, _ -> Tx (n + m)
  | Cons (_, ty), 0 -> ty
  | Cons (ss, _), _ -> subst_tx ss (n - 1)

and subst ss ty =
  match ty with
  | Tv _ -> ty
  | Tx n -> subst_tx ss n
  | Kon (tys, k) -> Kon (List.map (subst ss) tys, k)
  | Arr (ta, tb) -> Arr (subst ss ta, subst ss tb)

let rec ty_scan (maxx, vars as mv) ty =
  match ty with
  | Tv n ->
      if List.mem n vars then mv
      else (maxx, n :: vars)
  | Tx n -> (Pervasives.max maxx n, vars)
  | Kon (tys, _) ->
      List.fold_left ty_scan mv tys
  | Arr (ta, tb) ->
      ty_scan (ty_scan mv ta) tb

let rec replace_tvs shf vnums ty =
  match ty with
  | Tv n -> List.assoc n vnums
  | Tx x -> Tx (x + shf)
  | Kon (tys, k) -> Kon (List.map (replace_tvs shf vnums) tys, k)
  | Arr (ta, tb) -> Arr (replace_tvs shf vnums ta, replace_tvs shf vnums tb)

let abstract ty =
  let (maxx, vars) = ty_scan (0, []) ty in
  let sub = List.fold_right (fun v ss -> Cons (ss, Tv v)) vars (Shift 0) in
  let (_, vnums) =
    List.fold_left (fun (n, vnums) v -> (n + 1, (v, Tx n) :: vnums))
      (0, []) vars in
  let ty = replace_tvs (List.length vnums) vnums ty in
  (sub, ty)

let test ty =
  let (ss, sty) = abstract ty in
  (ty, subst ss sty)

open Format
open Extensions.ExtFormat

let fmt_arrow ff =
  Format.pp_print_string ff " ->" ;
  Format.pp_print_space ff ()

let varify n =
  let rec digs k ds n =
    if n < 26 then (k, (n :: ds))
    else digs (k + 1) (n mod 26 :: ds) (n / 26 - 1)
  in
  let (k, ds) = digs 0 [] n in
  let ds = ref ds in
  let str = String.create (k + 2) in
  str.[0] <- '\'' ;
  for i = 1 to k + 1 do
    match !ds with
    | d :: rest ->
        ds := rest ;
        str.[i] <- Char.chr (97 + d)
    | _ -> assert false
  done ;
  str

let rec ty_to_fexp ty =
  match ty with
  | Tx n -> Fstr (varify n)
  | Tv v -> Fstr ("\'" ^ v)
  | Kon ([], n) -> Fstr n
  | Kon (tys, kon) ->
      Fatm begin
        fun ff ->
          pp_open_box ff 1 ;
          intercalate
            ~left:(fun ff -> pp_print_string ff "(")
            ~right:(fun ff -> pp_print_string ff ")")
            ~sep:(fun ff -> pp_print_string ff "," ; pp_print_space ff ())
            pp_ty tys ff ;
          pp_print_break ff 1 2 ;
          pp_print_string ff kon ;
      end
  | Arr (ta, tb) ->
      Fapp (1, Finfix (`Right, ty_to_fexp ta, fmt_arrow, ty_to_fexp tb))

and pp_ty ty ff =
  Format.pp_open_box ff 0 ;
  linearize (ty_to_fexp ty) ff ;
  Format.pp_close_box ff ()

let to_buffer buf ty =
  let ff = Format.formatter_of_buffer buf in
  pp_ty ty ff ;
  Format.pp_print_flush ff ()

let ty_to_string ty =
  let buf = Buffer.create 19 in
  to_buffer buf ty ;
  Buffer.contents buf
  
let display ty = Format.printf "%t@." (pp_ty ty)
