(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open OUnit
open Abella_lib
open Term
open Term.Notations
open Test_helper

let starts_with prefix s =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix

let only_command script =
  let is_cmd l = starts_with "right-unify" l || starts_with "left-unify" l in
  match List.filter is_cmd (String.split_on_char '\n' script) with
  | [line] -> line
  | lines ->
      assert_failure
        (Printf.sprintf "Expected one command, found %d" (List.length lines))

(* [with_one_unification f] runs the unification [f], renders the trace, and
   returns the single emitted command.  [records] is global, so each case
   resets it before and after. *)
let with_one_unification f =
  Unilog.reset () ;
  f () ;
  let script = Unilog.render_script () in
  Unilog.reset () ;
  only_command script

let test_context_logic_eigen_nominal () =
  let h = const ~ts:1 "h" iiiity in
  let c = const ~ts:2 "c" ity in
  let x = var Logic "X" 3 ity in
  let y = var Eigen "Y" 2 ity in
  let n = nominal_var "n0" ity in
  let line = with_one_unification (fun () ->
    Unify.right_unify (h ^^ [x; y; n]) (h ^^ [c; y; n])) in
  assert_string_equal
    "right-unify ?X : i, _Y : i, #0 : i |- h ?X _Y #0 == h c _Y #0."
    line

let test_empty_context () =
  let f = const ~ts:1 "f" iity in
  let t = [("x", ity)] // (f ^^ [f ^^ [db 1]]) in
  let line = with_one_unification (fun () -> Unify.right_unify t t) in
  assert_string_equal
    "right-unify (x : i) \\ f (f x) == (y : i) \\ f (f y)." line

let test_repeated_var_binds_once () =
  let f = const ~ts:1 "f" iiity in
  let n = nominal_var "n0" ity in
  let line = with_one_unification (fun () ->
    Unify.right_unify (f ^^ [n; n]) (f ^^ [n; n])) in
  assert_string_equal
    "right-unify #0 : i |- f #0 #0 == f #0 #0." line

let test_left_unify () =
  let x = var Eigen "X" 1 iity in
  let n = nominal_var "n0" ity in
  let line = with_one_unification (fun () ->
    Unify.left_unify (x ^^ [n]) (x ^^ [n])) in
  assert_string_equal
    "left-unify _X : i -> i, #0 : i |- _X #0 == _X #0." line

let test_failed_unification_keeps_context () =
  let f = const ~ts:1 "f" iity in
  let g = const ~ts:1 "g" iity in
  let n = nominal_var "n0" ity in
  let line = with_one_unification (fun () ->
    try Unify.right_unify (f ^^ [n]) (g ^^ [n])
    with Unify.UnifyFailure _ -> ()) in
  assert_string_equal
    "right-unify #0 : i |- f #0 != g #0." line

let tests =
  "Unilog" >:::
    [
      "context lists logic, eigen, and nominal" >::
        test_context_logic_eigen_nominal ;
      "empty context omits the turnstile" >::
        test_empty_context ;
      "a repeated variable is bound once" >::
        test_repeated_var_binds_once ;
      "left-unify uses eigen markers" >::
        test_left_unify ;
      "a failed unification keeps its context" >::
        test_failed_unification_keeps_context ;
    ]
