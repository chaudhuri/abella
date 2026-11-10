(*
 * Copyright (C) 2026  Inria
 * See LICENSE for licensing details.
 *)

(* A nested environment stack for namespace management *)

open Extensions
open Abella_types
open Term

type frame = {
  name : id ;
  tys : int Itab.t ;
  consts : Typing.pty Itab.t ;
  defs : def Itab.t ;
  theorems : (id list * Metaterm.metaterm * fin) Itab.t ;
  guards : guard list Itab.t ;
  templates : template Itab.t ;
}

and template = {
  name : id ;
  params : id list ;
  frame : frame ;
}

type spec = {
  name : id ;
  clauses : (string list * term) Itab.t ;
  (* sr : Subordination.sr ; *) (* ignore for the time being *)
}

type env_kind =
  | Thm of {
      spec : spec option ;
      imports : string list ;
    }
  | Thmod of {
      imports : string list ;
    }

type t = {
  parents : frame list ;
  current : frame ;
  kind : env_kind ;
}

(******************************************************************************)
(* Lookup *)

type lookup_error =
  | Unknown_ty of id
  | Unknown_const of id
  | Unknown_theorem of id
  | Unknown_module of id

let lookup_kind env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_ty x
    | env :: rest ->
        (match Itab.find_opt x env.tys with
         | Some k -> Result.ok k
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

let lookup_const env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_const x
    | env :: rest ->
        (match Itab.find_opt x env.consts with
         | Some pty -> Result.ok (Typing.freshen_ty pty)
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

let lookup_def env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_const x
    | env :: rest ->
        (match Itab.find_opt x env.defs with
         | Some df -> Result.ok df
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

let lookup_theorem env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_theorem x
    | env :: rest ->
        (match Itab.find_opt x env.theorems with
         | Some thm -> Result.ok thm
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

let lookup_guards env x =
  let rec lookup1 = function
    | [] -> []
    | env :: rest ->
        let gs = match Itab.find_opt x env.guards with
          | None -> []
          | Some gs -> gs
        in
        gs @ lookup1 rest
  in
  lookup1 (env.current :: env.parents)

let lookup_template env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_module x
    | env :: rest ->
        (match Itab.find_opt x env.templates with
         | Some k -> Result.ok k
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

(******************************************************************************)
(* Insertion *)

type add_error =
  | Redeclared_ty of id
  | Redeclared_const of id
  | Redeclared_theorem of id
  | Redeclared_module of id

let add_kind env x ki =
  match Itab.find_opt x env.current.tys with
  | Some _ -> Result.error @@ Redeclared_ty x
  | None ->
      let tys = Itab.add x ki env.current.tys in
      let current = { env.current with tys } in
      Result.ok { env with current }

let add_const env con pty =
  match Itab.find_opt con env.current.consts with
  | Some _ -> Result.error @@ Redeclared_const con
  | None ->
      let consts = Itab.add con pty env.current.consts in
      let current = { env.current with consts } in
      Result.ok { env with current }

let add_def env def =
  let open Result.Syntax in
  let rec check_redef ks =
    match ks () with
    | Seq.Nil -> Result.ok Seq.empty
    | Seq.Cons ((dpred, _), ks) -> (
        let* sq = check_redef ks in
        match Itab.find_opt dpred env.current.defs with
        | None -> Result.ok @@ Seq.cons (dpred, def) sq
        | Some _ -> Result.error @@ Redeclared_const dpred
      ) in
  let* defs = check_redef (Itab.to_seq def.mutual) in
  let defs = Itab.add_seq defs env.current.defs in
  let current = { env.current with defs } in
  Result.ok { env with current }

let add_theorem env name tvs form fin =
  match Itab.find_opt name env.current.theorems with
  | Some _ -> Result.error @@ Redeclared_theorem name
  | None ->
      let theorems = Itab.add name (tvs, form, fin) env.current.theorems in
      let current = { env.current with theorems } in
      Result.ok { env with current }

let add_guards env id gs =
  let old_gs =
    match Itab.find_opt id env.current.guards with
    | None -> []
    | Some gs -> gs
  in
  let guards = Itab.add id (gs @ old_gs) env.current.guards in
  let current = { env.current with guards } in
  { env with current }

let add_template env name templ =
  match Itab.find_opt name env.current.templates with
  | Some _ -> Result.error @@ Redeclared_module name
  | None ->
      let templates = Itab.add name templ env.current.templates in
      let current = { env.current with templates } in
      Result.ok { env with current }

(******************************************************************************)
(* Incarnation *)

type incarnation_spec = {
  synonym : id option ;
  args : (id * ty) list ;
  preds : (id * id) list ;
  axioms : (id * id) list ;
}

let[@warning "-27"] incarnate_template env name (spec : incarnation_spec) =
  (* TODO

     1. Fetch the template with `lookup_template`. The rest of the
        steps will (functionally) modify this copy in sequence.
     2. Replace its params with spec.args (assoc list)
     3. For each (k, v) in spec.preds, replace the
        constant k in the template with v if they have compatible
        types. Get the type of k with lookup_const by
        temporarily stacking spec.frame in env, and
        that of v by lookup_const. The target types of
        both k and v must be prop.
     4. For each (k, v) in spec.axioms, check that
        k is an axiom in the template, and v is an axiom
        or a finished theorem in env, and that their
        formulas match up to alpha-varying the schemas.
     5. Prefix all the local names in the template
        with spec.synonym if it exists, or with name if not.
     6. Extend env.current with everything from the template.

    Make a reasonable error type and use Result.t on that error
   *)
  failwith "unimplemented"
