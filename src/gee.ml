(*
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** A faithful implementation of the G sequent calculus *)

(* [Metaterm] and [Extensions] are not opened: both redefine the standard
 * [List] functions to work on terms, which would break the association
 * lists used here for variables and hypotheses. *)
open Term
open Result.Syntax

type form = Metaterm.metaterm

type sequent = {
  vars : (id * term) list ;
  (* eigen vars, with newest var at head
     first component is the var name
     invariant: all the var names are different *)

  hyps : (id * form) list ;
  (* hypotheses, newest at head
     first component is the hyp name
     invariant: hyp names cannot be a var name *)

  goal : form ;
} [@@warning "-69"]

type error =
  | Unknown_hypothesis of id
  | Not_conjunction of form
  | Not_truth of form
  | Not_disjunction of form
  | Not_false of form
  | Not_implication of form
  | Not_forall of form
  | Not_exists of form
  | Not_nabla of form
  | Not_initial of id
  | Duplicate_variable of id
  | Witness_type of ty * term

let pp_error ff = function
  | Unknown_hypothesis id ->
      Format.fprintf ff "No hypothesis named %s in the sequent" id
  | Not_conjunction form ->
      Format.fprintf ff "Expected a conjunction, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_truth form ->
      Format.fprintf ff "Expected true, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_disjunction form ->
      Format.fprintf ff "Expected a disjunction, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_false form ->
      Format.fprintf ff "Expected false, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_implication form ->
      Format.fprintf ff "Expected an implication, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_forall form ->
      Format.fprintf ff "Expected a universal quantification, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_exists form ->
      Format.fprintf ff "Expected an existential quantification, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_nabla form ->
      Format.fprintf ff "Expected a generic quantification, found %s"
        (Metaterm.metaterm_to_string form)
  | Not_initial id ->
      Format.fprintf ff "The hypothesis %s is not initial for the goal" id
  | Duplicate_variable id ->
      Format.fprintf ff "The variable %s is declared more than once" id
  | Witness_type (ty, witness) ->
      Format.fprintf ff "The witness %s is not of type %s"
        (term_to_string witness) (ty_to_string ty)

let error_to_string error =
  Format.asprintf "%a" pp_error error
type 'a result = ('a, error) Result.t

let form_to_sequent goal =
  { vars = [] ; hyps = [] ; goal }

(* [remove_trailing_digits] and [fresh_name] mirror the freshening used by
 * [fresh_wrt], so that both variable and hypothesis names are freshened
 * the same way. *)
let remove_trailing_digits name =
  let is_digit c = c >= '0' && c <= '9' in
  let rec scan i =
    if i >= 0 && is_digit name.[i] then scan (i - 1) else i
  in
  String.sub name 0 (scan (String.length name - 1) + 1)

let fresh_name name used =
  if not (List.mem name used) then name else
  let base = remove_trailing_digits name in
  let rec search i =
    let candidate = base ^ string_of_int i in
    if List.mem candidate used then search (i + 1) else candidate
  in
  search 1

(* An eigen variable must not be nameable as a hypothesis, or the hypothesis
 * would be ill-scoped when its name is elaborated as a term. Hence [add_hyp]
 * keeps its name clear of the variables as well as of the hypotheses. *)
let add_hyp seq hn f =
  let used = List.map fst seq.vars @ List.map fst seq.hyps in
  let id = fresh_name hn used in
  let seq = { seq with hyps = (id, f) :: seq.hyps } in
  Ok (seq, id)

(* Signature variables must have unique names. *)
let check_vars vars =
  let rec check seen = function
    | [] -> Ok ()
    | (vname, _) :: vars' ->
        if List.mem vname seen then Error (Duplicate_variable vname)
        else check (vname :: seen) vars'
  in
  check [] vars

let end_sequent ~vars ~hyps ~goal =
  let* () = check_vars vars in
  let rec add_hyps seq = function
    | [] -> Ok seq
    | (hn, f) :: hyps' ->
        let* seq, _ = add_hyp seq hn f in
        add_hyps seq hyps'
  in
  add_hyps { vars = List.rev vars ; hyps = [] ; goal } (List.rev hyps)

(* Structural rules *)

let contract ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some form -> add_hyp sequent left form

let weaken ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some _ ->
      let hyps = List.filter (fun (id, _) -> id <> left) sequent.hyps in
      Ok { sequent with hyps }

(* Right rules *)

let and_right sequent =
  let* a, b =
    match sequent.goal with
    | Metaterm.And (a, b) -> Ok (a, b)
    | goal -> Error (Not_conjunction goal)
  in
  Ok ({ sequent with goal = a }, { sequent with goal = b })

let top_right sequent =
  match sequent.goal with
  | Metaterm.True -> Ok ()
  | _ -> Error (Not_truth sequent.goal)

let or_right_1 sequent =
  let* a, _ =
    match sequent.goal with
    | Metaterm.Or (a, b) -> Ok (a, b)
    | goal -> Error (Not_disjunction goal)
  in
  Ok { sequent with goal = a }

let or_right_2 sequent =
  let* _, b =
    match sequent.goal with
    | Metaterm.Or (a, b) -> Ok (a, b)
    | goal -> Error (Not_disjunction goal)
  in
  Ok { sequent with goal = b }

let false_left sequent =
  match sequent.goal with
  | Metaterm.False -> Ok ()
  | _ -> Error (Not_false sequent.goal)

let imp_right sequent =
  let* a, b =
    match sequent.goal with
    | Metaterm.Arrow (a, b) -> Ok (a, b)
    | goal -> Error (Not_implication goal)
  in
  (* The antecedent joins the hypotheses at the newest end *)
  let* seq, l1 = add_hyp sequent "_" a in
  Ok ({ seq with goal = b }, l1)

(* [instantiate binder tids body] peels one binder off [tids] and returns
 * the variable it stands for together with the body it instantiates.
 * Nothing ever constructs a binding with an empty variable list. *)
let instantiate binder tids body =
  match tids with
  | [x, ty] -> (x, ty, body)
  | (x, ty) :: tids' -> (x, ty, Metaterm.binding binder tids' body)
  | [] -> [%bug] "Empty quantified variables list"

let exists_right ~witness sequent =
  let* x, ty, body =
    match sequent.goal with
    | Metaterm.Binding (Metaterm.Exists, tids, body) ->
        Ok (instantiate Metaterm.Exists tids body)
    | goal -> Error (Not_exists goal)
  in
  if not (eq_ty (tc [] witness) ty) then
    Error (Witness_type (ty, witness))
  else
    let goal = Metaterm.replace_metaterm_vars [(x, witness)] body in
    Ok { sequent with goal }

(* Pure G has no subordination relation, so a variable introduced under a
 * generic quantifier is raised over every nominal constant in the body it
 * is instantiated in. *)
let raise_over_nominals tag ty body =
  match Metaterm.metaterm_support body with
  | [] -> fresh ~tag 0 ty
  | support ->
      let wty = tyarrow (List.map (tc []) support) ty in
      app (fresh ~tag 0 wty) support

let forall_right sequent =
  let* x, ty, body =
    match sequent.goal with
    | Metaterm.Binding (Metaterm.Forall, tids, body) ->
        Ok (instantiate Metaterm.Forall tids body)
    | goal -> Error (Not_forall goal)
  in
  let v = raise_over_nominals Eigen ty body in
  let alist = [(x, v)] in
  let vars = (term_to_name v, v) :: sequent.vars in
  let seq = { sequent with vars } in
  let goal = Metaterm.replace_metaterm_vars alist body in
  Ok ({ seq with goal }, term_to_name v)

(* The generic quantifier behaves the same on either side of the sequent
 * arrow, so both rules only differ in where the instance is placed *)
let nabla_right sequent =
  let* x, ty, body =
    match sequent.goal with
    | Metaterm.Binding (Metaterm.Nabla, tids, body) ->
        Ok (instantiate Metaterm.Nabla tids body)
    | goal -> Error (Not_nabla goal)
  in
  let v = fresh ~tag:Nominal 0 ty in
  let alist = [(x, v)] in
  let vars = (term_to_name v, v) :: sequent.vars in
  let seq = { sequent with vars } in
  let goal = Metaterm.replace_metaterm_vars alist body in
  Ok ({ seq with goal }, term_to_name v)

(* Left rules *)

let and_left ~left hyps k =
  match List.assoc_opt left hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.And (f, g)) -> k f g
  | Some form -> Error (Not_conjunction form)

let and_left_1 ~left sequent =
  and_left ~left sequent.hyps
    (fun f _ -> add_hyp sequent left f)

let and_left_2 ~left sequent =
  and_left ~left sequent.hyps
    (fun _ g -> add_hyp sequent left g)

let and_left_both ~left sequent =
  and_left ~left sequent.hyps
    (fun f g ->
       let* (sequent, l1) = add_hyp sequent left f in
       let* (sequent, l2) = add_hyp sequent left g in
       Ok (sequent, l1, l2))

let or_left ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.Or (f, g)) ->
      let* (sequent1, l1) = add_hyp sequent left f in
      (* Both branches start from the same sequent *)
      let* (sequent2, l2) = add_hyp sequent left g in
      Ok (sequent1, l1, sequent2, l2)
  | Some form -> Error (Not_disjunction form)

let imp_left ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.Arrow (f, g)) ->
      (* Additive: both premises keep [sequent.hyps], and only the major
       * premise gains the succedent as a hypothesis *)
      let* (major, l1) = add_hyp sequent left g in
      let minor = { sequent with goal = f } in
      Ok (major, l1, minor)
  | Some form -> Error (Not_implication form)

let forall_left ~left ~witness sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.Binding (Metaterm.Forall, tids, body)) ->
      let x, ty, body = instantiate Metaterm.Forall tids body in
      if not (eq_ty (tc [] witness) ty) then
        Error (Witness_type (ty, witness))
      else
        let hyps = (left, Metaterm.replace_metaterm_vars [(x, witness)] body)
                   :: sequent.hyps in
        Ok ({ sequent with hyps }, left)
  | Some form -> Error (Not_forall form)

let exists_left ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.Binding (Metaterm.Exists, tids, body)) ->
      let x, ty, body = instantiate Metaterm.Exists tids body in
      let v = raise_over_nominals Eigen ty body in
      let vars = (term_to_name v, v) :: sequent.vars in
      let* seq, l1 =
        add_hyp { sequent with vars } left
          (Metaterm.replace_metaterm_vars [(x, v)] body)
      in
      Ok (seq, l1)
  | Some form -> Error (Not_exists form)

let nabla_left ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some (Metaterm.Binding (Metaterm.Nabla, tids, body)) ->
      let x, ty, body = instantiate Metaterm.Nabla tids body in
      let v = fresh ~tag:Nominal 0 ty in
      let vars = (term_to_name v, v) :: sequent.vars in
      let* seq, l1 =
        add_hyp { sequent with vars } left
          (Metaterm.replace_metaterm_vars [(x, v)] body)
      in
      Ok (seq, l1)
  | Some form -> Error (Not_nabla form)

(* The sequent is initial at [left] when the hypothesis and the goal are
 * identical up to a permutation of their nominal constants. *)
let initial ~left sequent =
  match List.assoc_opt left sequent.hyps with
  | None -> Error (Unknown_hypothesis left)
  | Some hyp ->
      let equivariant = ref false in
      Metaterm.all_meta_right_permute_unify
        ~sc:(fun () -> equivariant := true) hyp sequent.goal ;
      if !equivariant then Ok () else Error (Not_initial left)
