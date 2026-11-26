(****************************************************************************)
(* Copyright (C) 2026 Inria (Institut National de Recherche                 *)
(*                           en Informatique et en Automatique)             *)
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

open Abella_lib

module D = Driver

let with_session ?(file_kind=`thm) f =
  let thc_cache_limit = !Source.thc_cache_limit in
  let cleanup () =
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Source.set_thc_cache_limit thc_cache_limit ;
    Accumulate.clear_specification_cache ()
  in
  Fun.protect ~finally:cleanup (fun () ->
    D.Setup.with_saved (fun () ->
      State.reload D.initial_snapshot ;
      State.Undo.set_enabled true ;
      State.Undo.reset () ;
      Accumulate.clear_specification_cache () ;
      Source.clear_virtual () ;
      Source.clear_thc_trust () ;
      D.Setup.compiling := [] ;
      D.Setup.on_import := None ;
      Thmod.reset () ;
      D.Setup.mode := `interactive ;
      D.Setup.file_kind := file_kind ;
      D.Setup.annotate := false ;
      D.Setup.recurse := false ;
      D.Setup.import_mode := `auto ;
      D.Setup.trust_compiled := true ;
      D.Setup.compiled := None ;
      D.Setup.unfinished := [] ;
      D.Setup.input := "test_sealed.thm" ;
      Output.collect_mode () ;
      ignore (Output.drain ()) ;
      f ()))

let error_messages messages =
  List.filter_map begin function
    | `Assoc fields -> begin
        match List.assoc_opt "severity" fields,
              List.assoc_opt "message" fields with
        | Some (`String "error"), Some (`String msg) -> Some msg
        | _ -> None
      end
    | _ -> None
  end messages

let run_script ?(file_kind=`thm) script =
  with_session ~file_kind (fun () ->
    let lb = Lexing.from_string script in
    lb.Lexing.lex_curr_p <- {
      lb.Lexing.lex_curr_p with
      Lexing.pos_fname = !D.Setup.input
    } ;
    D.Setup.lexbuf := lb ;
    let rec loop state =
      match D.process1 state with
      | Ok state' -> loop state'
      | Error err ->
          let msgs = Output.drain () |> error_messages in
          let err_str = Format.asprintf "%a" D.pp_processing_error err in
          Error (String.concat "\n" (err_str :: msgs))
      | exception D.Setup.AbellaExit 0 -> Ok ()
      | exception End_of_file -> Ok ()
      | exception D.Setup.AbellaExit _ ->
          let msgs = Output.drain () |> error_messages in
          Error (String.concat "\n" msgs)
    in
    loop D.Process_top)

let assert_script_ok name script =
  match run_script script with
  | Ok () -> ()
  | Error msg -> Alcotest.failf "%s failed unexpectedly:\n%s" name msg

let contains_substring needle haystack =
  let n = String.length needle and h = String.length haystack in
  let rec spin i =
    i + n <= h && (String.sub haystack i n = needle || spin (i + 1))
  in
  spin 0

let assert_script_fails name ?(file_kind=`thm) ?expect script =
  match run_script ~file_kind script with
  | Ok () -> Alcotest.failf "%s unexpectedly succeeded" name
  | Error msg ->
      match expect with
      | None -> ()
      | Some sub ->
          if not (contains_substring sub msg) then
            Alcotest.failf
              "%s failed with unexpected message (expected %S):\n%s"
              name sub msg

let perm_prelude = {|
Define remove : A -> list A -> list A -> prop by
  remove X (X :: L) L
; remove X (Y :: L) (Y :: K) := remove X L K.

Theorem remove_swap [A] : forall (X : A) Y L L1 L2,
  remove X L L1 -> remove Y L L2 ->
  (X = Y /\ L1 = L2) \/ exists K, remove Y L1 K /\ remove X L2 K.
induction on 1. intros. case H1.
  case H2.
    left. search.
    right. exists K. search.
  case H2.
    right. exists K. search.
    apply IH to H3 H4. case H5.
      left. search.
      right. exists (Y1 :: K2). search.

Define perm : list A -> list A -> prop by
  perm nil nil
; perm (X :: L) K := exists K', remove X K K' /\ perm L K'.

Theorem perm_remove [A] : forall (X : A) L K K',
  perm L K -> remove X K K' ->
  exists L', remove X L L' /\ perm L' K'.
induction on 1. intros. case H1.
  case H2.
  apply remove_swap to H2 H3. case H5.
    exists L1. search.
    apply IH to H4 H7. exists (X1 :: L'). search.

Theorem perm_right_cons [A] : forall (X : A) L K K',
  remove X K K' -> perm K' L -> perm K (X :: L).
induction on 1. intros. case H1.
  search.
  case H2. apply IH to H3 H5. search.

Theorem perm_sym [A] : forall (L K : list A), perm L K -> perm K L.
induction on 1. intros. case H1.
  search.
  apply IH to H3. apply perm_right_cons to H2 H4. search.

Theorem perm_trans [A] : forall (L K M : list A), perm L K -> perm K M -> perm L M.
induction on 1. intros. case H1.
  case H2. search.
  apply perm_sym to H2. apply perm_remove to H5 H3.
    apply perm_sym to H7. apply IH to H4 H8. search.

Seal mset A := list A with perm by perm_sym, perm_trans.
|}

let test_mset_eq_and_mll_perm () =
  assert_script_ok "mset_eq and mll_perm" (perm_prelude ^ {|
Theorem mset_eq [A] : forall (L K : list A), perm L K -> mset L = mset K.
intros. search.

Kind atm type.
Type atom, natom atm -> o.
Type par, tens o -> o -> o.

Define mll : mset o -> prop by
  mll (mset (atom A :: natom A :: nil))
; mll (mset (par A B :: G)) := mll (mset (A :: B :: G))
; mll (mset (tens A B :: G)) :=
    exists G1 G2,
      mll (mset (A :: G1)) /\
      mll (mset (B :: G2)).

Theorem mll_perm : forall G D, mll (mset G) -> perm G D -> mll (mset D).
intros. search.

Theorem mll_id_swapped : forall A, mll (mset (natom A :: atom A :: nil)).
intros. search.
|})

let test_negative_validation () =
  assert_script_fails "non-symmetric relation rejected" ~expect:"symmetry" {|
Define leq : list A -> list A -> prop by
  leq nil L
; leq (X :: L) (X :: K) := leq L K.
Theorem leq_trans [A] : forall (X Y Z : list A), leq X Y -> leq Y Z -> leq X Z.
induction on 1. intros. case H1. search. case H2. apply IH to H3 H4. search.
Theorem bad_sym [A] : forall (X Y : list A), leq X Y -> leq X Y.
intros. search.
Seal bad A := list A with leq by bad_sym, leq_trans.
|};
  assert_script_fails "non-transitive relation rejected" ~expect:"transitivity" {|
Define rel : list A -> list A -> prop by
  rel L L.
Theorem rel_sym [A] : forall (X Y : list A), rel X Y -> rel Y X.
intros. case H1. search.
Theorem bad_trans [A] : forall (X Y Z : list A), rel X Y -> rel Y Z -> rel X Y.
intros. search.
Seal bad A := list A with rel by rel_sym, bad_trans.
|};
  assert_script_fails "unfinished PER lemma rejected" ~expect:"unfinished" (perm_prelude ^ {|
Theorem u_sym [A] : forall (L K : list A), perm L K -> perm K L. skip.
Seal bad A := list A with perm by u_sym, perm_trans.
|});
  assert_script_fails "second constant with sealed target type rejected"
    ~expect:"sealed target type" (perm_prelude ^ {|
Type extra mset A.
|});
  assert_script_fails "Seal with prop in underlying type rejected"
    ~expect:"prop" {|
Define eqp : prop -> prop -> prop by eqp X X.
Theorem eqp_sym : forall X Y, eqp X Y -> eqp Y X. intros. case H1. search.
Theorem eqp_trans : forall X Y Z, eqp X Y -> eqp Y Z -> eqp X Z. intros. case H1. search.
Seal bad := prop with eqp by eqp_sym, eqp_trans.
|};
  assert_script_fails "nabla at sealed type rejected"
    ~expect:"nabla" (perm_prelude ^ {|
Theorem bad_nabla : nabla (x : mset o), x = x.
|});
  assert_script_fails "sealed type in Obj sequent rejected"
    ~expect:"specification logic" (perm_prelude ^ {|
Type mk mset o -> o.
Theorem bad_obj : { mk (mset nil) }.
|});
  assert_script_fails "Seal inside Module rejected"
    ~expect:"module" {|
Module M.
Define r : list A -> list A -> prop by r X X.
Theorem r_sym [A] : forall (X Y : list A), r X Y -> r Y X. intros. case H1. search.
Theorem r_trans [A] : forall (X Y Z : list A), r X Y -> r Y Z -> r X Z. intros. case H1. search.
Seal bad A := list A with r by r_sym, r_trans.
End M.
|};
  assert_script_fails "Seal inside .thmod rejected" ~file_kind:`thmod
    ~expect:".thmod" {|
Module M.
Define r : list A -> list A -> prop by r X X.
Theorem r_sym [A] : forall (X Y : list A), r X Y -> r Y X. intros. case H1. search.
Theorem r_trans [A] : forall (X Y Z : list A), r X Y -> r Y Z -> r X Z. intros. case H1. search.
Seal bad A := list A with r by r_sym, r_trans.
End M.
|}

let test_soundness_regressions () =
  (* 1. Occurs check under sealed constructor: M = u (mk M) is provable, not refutable *)
  assert_script_ok "occurs check under sealed ctor is provable" {|
Kind box type.
Type c box.
Define triv : box -> box -> prop by triv X Y.
Theorem triv_sym : forall X Y, triv X Y -> triv Y X.
intros. search.
Theorem triv_trans : forall X Y Z, triv X Y -> triv Y Z -> triv X Z.
intros. search.
Seal u := box with triv by triv_sym, triv_trans.
Type mk u -> box.

Theorem fixpoint_exists : exists (M : u), M = u (mk M).
exists (u c). search.
|};
  assert_script_fails "occurs check under sealed ctor not refutable" {|
Kind box type.
Type c box.
Define triv : box -> box -> prop by triv X Y.
Theorem triv_sym : forall X Y, triv X Y -> triv Y X.
intros. search.
Theorem triv_trans : forall X Y Z, triv X Y -> triv Y Z -> triv X Z.
intros. search.
Seal u := box with triv by triv_sym, triv_trans.
Type mk u -> box.

Theorem unsound_occurs : (forall M : u, M = u (mk M) -> false).
intros. case H1.
|};
  (* 2. Timestamp escape under sealed constructor *)
  assert_script_fails "timestamp escape under sealed ctor not refutable" {|
Kind expr type.
Type z expr.
Define eqe : expr -> expr -> prop by eqe X Y.
Theorem eqe_sym : forall X Y, eqe X Y -> eqe Y X. intros. search.
Theorem eqe_trans : forall X Y Z, eqe X Y -> eqe Y Z -> eqe X Z. intros. search.
Seal grp := expr with eqe by eqe_sym, eqe_trans.

Theorem not_refutable : exists M : grp, nabla (n : expr), M = grp n -> false.
exists grp z. intros. case H1.
|};
  (* 3. mset [a; b] = mset [b; a] not refuted by case *)
  assert_script_fails "mset [a; b] = mset [b; a] not refuted by case" (perm_prelude ^ {|
Kind elem type.
Type a, b elem.
Theorem not_refutable : mset (a :: b :: nil) = mset (b :: a :: nil) -> false.
intros. case H1.
|});
  (* 4. mset n1 = mset n1 does not prove perm n1 n1 *)
  assert_script_fails "mset n1 = mset n1 does not prove perm n1 n1" (perm_prelude ^ {|
Theorem not_perm_nominal : nabla (n : list o), perm n n.
intros. search.
|})

let test_thc_import () =
  let base_thm = perm_prelude ^ {|
Theorem mset_eq [A] : forall (L K : list A), perm L K -> mset L = mset K.
intros. search.
|} in
  let client_thm = {|
Import "base".
Theorem client_eq [A] : forall (L K : list A), perm L K -> mset L = mset K.
intros. search.
|} in
  with_session (fun () ->
    Source.add_virtual "base.thm" base_thm ;
    let lb = Lexing.from_string client_thm in
    lb.Lexing.lex_curr_p <- {
      lb.Lexing.lex_curr_p with
      Lexing.pos_fname = "client.thm"
    } ;
    D.Setup.input := "client.thm" ;
    D.Setup.lexbuf := lb ;
    let rec loop state =
      match D.process1 state with
      | Ok state' -> loop state'
      | Error err ->
          let msgs = Output.drain () |> error_messages in
          let err_str = Format.asprintf "%a" D.pp_processing_error err in
          Alcotest.failf "thc import failed:\n%s\n%s" err_str
            (String.concat "\n" msgs)
      | exception D.Setup.AbellaExit 0 -> ()
      | exception End_of_file -> ()
    in
    loop D.Process_top)

let test_thc_import_with () =
  let base_thm = {|
Kind tok type.
Type r tok -> tok -> prop.
Axiom r_sym : forall (X Y : tok), r X Y -> r Y X.
Axiom r_trans : forall (X Y Z : tok), r X Y -> r Y Z -> r X Z.
Seal q := tok with r by r_sym, r_trans.
|} in
  let client_thm = {|
Kind tok type.
Define r2 : tok -> tok -> prop by
  r2 X X.
Import "base_with" with r := r2.
Theorem client_refl : forall (X : tok), q X = q X.
intros. search.
|} in
  with_session (fun () ->
    Source.add_virtual "base_with.thm" base_thm ;
    let lb = Lexing.from_string client_thm in
    lb.Lexing.lex_curr_p <- {
      lb.Lexing.lex_curr_p with
      Lexing.pos_fname = "client_with.thm"
    } ;
    D.Setup.input := "client_with.thm" ;
    D.Setup.lexbuf := lb ;
    let rec loop state =
      match D.process1 state with
      | Ok state' -> loop state'
      | Error err ->
          let msgs = Output.drain () |> error_messages in
          let err_str = Format.asprintf "%a" D.pp_processing_error err in
          Alcotest.failf "thc import with failed:\n%s\n%s" err_str
            (String.concat "\n" msgs)
      | exception D.Setup.AbellaExit 0 -> ()
      | exception End_of_file -> ()
    in
    loop D.Process_top ;
    match Sealed.lookup "q" with
    | Some info ->
        Alcotest.(check string) "rel_name renamed" "r2" info.rel_name
    | None -> Alcotest.fail "expected sealed type q to be registered")

let tests =
  ("Sealed", [
     Alcotest.test_case "mset_eq and mll_perm" `Quick test_mset_eq_and_mll_perm ;
     Alcotest.test_case "negative validation" `Quick test_negative_validation ;
     Alcotest.test_case "soundness regressions" `Quick test_soundness_regressions ;
     Alcotest.test_case "thc import" `Quick test_thc_import ;
     Alcotest.test_case "thc import with" `Quick test_thc_import_with ;
   ])
