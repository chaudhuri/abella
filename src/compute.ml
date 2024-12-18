(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2024  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions
open Term
open Metaterm
open Abella_types

let format_guard ff guard =
  let format_term ff t = Term.format_term ff t in
  Format.fprintf ff "Suspend %a := @[<hov0>%a@]"
    (format_term) guard.pattern
    (Format.pp_print_list format_term
       ~pp_sep:Format.pp_print_commaspace) guard.condition

let guard_to_string guard =
  let buf = Buffer.create 19 in
  let ff = Format.formatter_of_buffer buf in
  format_guard ff guard ;
  Format.pp_print_flush ff () ;
  Buffer.contents buf

let standardize_predicate (ut : Typing.uterm) =
  let rec get_predicate = function
    | Typing.UCon (_, pred, _) -> pred
    | UApp (_, ut, _) -> get_predicate ut
    | ULam (pos, _, _, _) ->
        failwithf_at ~pos "Invalid lambda-abstraction in suspension head"
  in
  let pred = get_predicate ut in
  let rec get_vars ctx = function
    | Typing.UCon (pos, "_", _) ->
        let id = Term.fresh_name "#" ctx in
        let ty = fresh_tyvar () in
        let ctx = (id, ty) :: ctx in
        (ctx, Typing.UCon (pos, id, ty))
    | UCon (pos, id, _) when is_capital_name id ->
        if List.mem_assoc id ctx then
          failwithf_at ~pos "Repeated variable %s" id ;
        let ty = fresh_tyvar () in
        let ctx = (id, ty) :: ctx in
        (ctx, UCon (pos, id, ty))
    | UCon _ as ut -> (ctx, ut)
    | UApp (pos, ut1, ut2) ->
        let (ctx, ut1) = get_vars ctx ut1 in
        let (ctx, ut2) = get_vars ctx ut2 in
        (ctx, UApp (pos, ut1, ut2))
    | ULam (pos, id, ty, ut) ->
        let (ctx, ut) = get_vars ctx ut in
        (ctx, ULam (pos, id, ty, ut))
  in
  let (ctx, ut) = get_vars [] ut in
  (ctx, pred, ut)

let make_guard ~head ~test =
  let (tyctx, predicate, pattern) = standardize_predicate head in
  let (ty, eqns) = Typing.(infer_type_and_constraints ~sign:!sign tyctx pattern) in
  Unifyty.unify_constraints eqns ;
  let vars = List.map (fun (id, ty) -> (id, Term.fresh ~tag:Eigen 0 ty)) tyctx in
  let pattern = Typing.(uterm_to_term pattern |> replace_term_vars vars) in
  if not @@ Term.(eq_ty ty propty || eq_ty ty oty) then
    failwithf "Expected target type prop or o, got %s" (ty_to_string ty) ;
  let condition = match test with
    | None ->
        List.filter_map (fun (id, vtm) -> if id.[0] = '#' then None else Some vtm) vars
    | Some test ->
        List.unique test
        |> List.map begin fun vid ->
          match List.assoc_opt vid vars with
          | None -> failwithf "Unknown condition variable %s" vid
          | Some term -> term
        end
  in
  { predicate ; pattern ; condition }

(** [evaluate_guard guard t] returns true if the guard stops compute *)
let evaluate_guard guard t =
  let format_term ff t = Term.format_term ff t in
  let kind = "evaluate_guard" in
  [%trace 2 ~kind
      "@[<v0>Testing @[%a@]@,against @[%a@]@]"
      format_term t
      format_guard guard] ;
  let state = Term.get_scoped_bind_state () in
  let result = try
      Unify.left_unify t guard.pattern ;
      (* Output.trace ~v begin fun (module Trace) -> *)
      (*   Trace.format ~kind "Unification resulted in %a" *)
      (*     format_term guard.pattern *)
      (* end ; *)
      (* all test vars neeed to be eigen to stop *)
      List.for_all Term.has_eigen_head guard.condition
    with _ -> false
  in
  Term.set_scoped_bind_state state ;
  [%trace 2 ~kind "result: %b" result] ;
  result

let guards : (id, guard) Hashtbl.t = State.table ()

let add_guard (gd : guard) = Hashtbl.add guards gd.predicate gd

let is_guarded atm =
  let pred, _args =
    match Term.term_head atm with
    | Some pa -> pa
    | None -> [%bug] "Invalid predicate: %s" (term_to_string atm)
  in
  Term.term_to_name pred
  |> Hashtbl.find_all guards
  |> List.exists (fun guard -> evaluate_guard guard atm)

(******************************************************************************)
(* Compute implementation *)

let () =
  let open Typing in
  let e = UCon (ghost_pos, "_", fresh_tyvar ()) in
  let l = UCon (ghost_pos, "L", fresh_tyvar ()) in
  let head = UApp (ghost_pos,
                   UApp (ghost_pos,
                         UCon (ghost_pos, "member", fresh_tyvar ()),
                         e),
                   l) in
  let test = None in
  make_guard ~head ~test |> add_guard

type compute_hyp = {
  clr : clearable ;
  form : metaterm ;
}

type compute_wait = {
  vars : (id * term) list ;
  chyp : compute_hyp ;
}

let ch_to_string (ch : compute_hyp) = clearable_to_string ch.clr

let format_ch ff (ch : compute_hyp) =
  Format.fprintf ff "%s : %a" (clearable_to_string ch.clr) format_metaterm ch.form

let cw_to_string w =
  Printf.sprintf "<%s>%s"
    (List.map fst w.vars |> String.concat ", ")
    (ch_to_string w.chyp)

let pp_print_wait_var ff (v, t) =
  Format.fprintf ff "%s <- %s" v (term_to_string t)

let get_wait clr form =
  let vars = get_metaterm_used form in
  { vars ; chyp = { clr ; form } }

let is_free t =
  match Term.observe t with
  | Var { tag = Eigen ; _ } -> true
  | _ -> false

let is_unchanged wait =
  List.for_all (fun (_, t) -> is_free t) wait.vars

exception Out_of_gas
exception Suspended

let branch_to_string branch =
  branch |>
  List.rev_map (fun x -> string_of_int @@ x + 1) |>
  String.concat "."

let compute ?name ?(gas = 1_000) hs wrt =
  let kind = "compute" in
  let total_gas = gas in
  let gas = ref total_gas in
  let consume_gas n =
    if !gas < n then raise Out_of_gas ;
    gas := !gas - n ;
    [%trace 2 ~kind "Consumed %d gas (%d left)" n !gas] ;
  in
  let fresh_compute_hyp =
    let count = ref @@ -1 in
    fun () -> incr count ; "<#" ^ string_of_int !count ^ ">"
  in
  [%trace 2 ~kind
      "compute wrt %s" (String.concat ", " wrt)] ;
  let subgoals = ref [] in
  let rec compute_all ~(branch : int list) ~chs ~wait ~todo =
    [%trace 2 ~kind
        "BRANCH_ALL [%s] chs:[%s] wait:[%s] todo:[%s]"
        (branch_to_string branch)
        (List.map ch_to_string chs |> String.concat ",")
        (List.map cw_to_string wait |> String.concat ",")
        (List.map ch_to_string todo |> String.concat ",")] ;
    match todo with
    | [] ->
        let sg =
          List.iter begin fun ch ->
            [%trace 2 ~kind "Renaming: %s" (ch_to_string ch)] ;
            let stmt = Prover.get_stmt_clearly ch.clr in
            Prover.add_hyp ?name stmt
          end chs ;
          let state = Term.get_bind_state () in
          let current_seq = Prover.copy_sequent () in
          fun () ->
            Term.set_bind_state state ;
            Prover.set_sequent current_seq
        in
        subgoals := sg :: !subgoals ;
        [%trace 2 ~kind
            "BRANCH_END [%s] with new subgoal"
            (branch_to_string branch)] ;
    | h :: todo ->
        compute_one ~branch ~chs ~wait ~todo h
  and compute_one ~branch ~chs ~wait ~todo (ch : compute_hyp) =
    (* Output.trace ~v begin fun (module Trace) -> *)
    (*   Trace.printf ~kind *)
    (*     "BRANCH_START [%s] chs:[%s] wait:[%s] todo:[%s] %s" *)
    (*     (branch_to_string branch) *)
    (*     (List.map ch_to_string chs |> String.concat ",") *)
    (*     (List.map cw_to_string wait |> String.concat ",") *)
    (*     (List.map ch_to_string todo |> String.concat ",") *)
    (*     (ch_to_string ch) *)
    (* end ; *)
    let suspend () = compute_all ~branch ~chs ~wait:(get_wait ch.clr ch.form :: wait) ~todo in
    let doit () = compute_case ~branch ~chs ~wait ~todo ch in
    match ch.form with
    | Binding (Forall, _, _)
    | Arrow _ ->
        suspend ()
    | Obj ({ mode = Async ; right = atm ; _ }, _)
    | Pred (atm, _)
      when is_guarded atm -> begin
        let saved = Prover.copy_sequent () in
        let rec try_wrts wrt =
          Prover.set_sequent saved ;
          match wrt with
          | [] ->
              suspend ()
          | lem :: wrt -> begin
              let lem_term = Prover.get_lemma lem in
              match Tactics.apply ~sr:!Typing.sr lem_term [Some ch.form] with
              | f, [] ->
                  consume_gas 1 ;
                  Prover.(replace_hyp (stmt_name ch.clr) f) ;
                  let hn = Prover.stmt_name ch.clr in
                  [%trace 2  ~kind
                      "@[<v0>Did: %s : apply %s to *%s.@,  old: %a@,  new: %a@]"
                      hn lem hn
                      format_metaterm ch.form
                      format_metaterm f] ;
                  let todo = {ch with form = f} :: todo in
                  compute_all ~branch ~chs ~wait ~todo
              | _ | exception _ ->
                  try_wrts wrt
            end
        in
        try_wrts wrt
      end
    | Obj ({ mode = Sync f ; _ }, _) -> begin
        match Term.(observe @@ hnorm f) with
        | Var _ -> suspend ()
        | _ -> doit ()
      end
    | _ -> doit ()
  and compute_case ~branch ~chs ~wait ~todo (ch : compute_hyp) =
    consume_gas 1 ;
    let saved = Prover.copy_sequent () in
    [%trace 2 ~kind "compute_case: %a" format_ch ch] ;
    match Prover.case_subgoals ch.clr with
    | exception _ ->
        Prover.set_sequent saved ;
        compute_all ~branch ~chs ~wait:(get_wait ch.clr ch.form :: wait) ~todo
    | cases ->
        let chs = List.filter (fun oldch -> oldch.clr <> ch.clr) chs in
        let saved = Prover.copy_sequent () in
        [%trace 2 ~kind "compute_case: there were %d cases" (List.length cases)] ;
        List.iteri begin fun br (case : Tactics.case) ->
          Prover.set_sequent saved ;
          List.iter Prover.add_if_new_var case.Tactics.new_vars ;
          let hs = List.rev_map (fun h -> Prover.unsafe_add_hyp (fresh_compute_hyp ()) h) case.new_hyps in
          Term.set_bind_state case.bind_state ;
          Prover.update_self_bound_vars () ;
          [%trace 2 ~kind "Case %a" format_ch ch] ;
          List.iter begin fun h ->
            [%trace 2 ~kind "Adding: %s : %a" h.Prover.id format_metaterm h.term] ;
          end hs ;
          let (wait, newly_active) = List.partition is_unchanged wait in
          List.iter begin fun w ->
            [%trace 2 ~kind "Reactivated %s: %a cuz @[<hov0>%a@]"
                (clearable_to_string w.chyp.clr) format_metaterm w.chyp.form
                (Format.pp_print_list ~pp_sep:Format.pp_print_commaspace pp_print_wait_var) w.vars]
          end newly_active ;
          let new_chs = List.rev_map (fun h -> { clr = Remove (h.Prover.id, []) ; form = h.term }) hs in
          let chs = List.rev_append new_chs chs in
          let todo =
            List.rev_map (fun w -> w.chyp) newly_active
            @ new_chs @ todo in
          compute_all ~branch:(br :: branch) ~chs ~wait ~todo
        end cases
  in
  let todo = List.map (fun h -> { clr = h ; form = Prover.get_hyp_or_lemma (Prover.stmt_name h) }) hs in
  match compute_all ~branch:[] ~chs:[] ~wait:[] ~todo with
  | exception Out_of_gas ->
      failwithf "Compute ran out of gas (given %d) -- looping?" total_gas
  | _ ->
      [%trace 2 ~kind "Computation used %d gas" (total_gas - !gas)] ;
      Prover.add_subgoals @@ List.rev !subgoals ;
      Prover.next_subgoal ()

let compute_all ?name ?gas clr =
  let hs = List.map begin fun (h : Prover.hyp) ->
      if clr = `CLEAR then Remove (h.id, []) else Keep (h.id, [])
    end Prover.sequent.hyps in
  compute ?name ?gas hs
