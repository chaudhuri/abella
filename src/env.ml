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
  (* Invariant: each mutually defined block is stored once. Exactly
     one of its keys maps to [`def], holding the shared definition;
     every other key of the block maps to [`fwd] pointing at that
     key in the same table. Rewriters update the single copy while
     lookup follows the pointers. *)
  defs : [`fwd of id | `def of def] Itab.t ;
  theorems : (id list * Metaterm.metaterm * fin) Itab.t ;
  guards : guard list Itab.t ;
  templates : template Itab.t ;
  (* sr covers every type in scope: insertions extend it, and
     incarnation recomputes it from the importer's sr plus the
     template's renamed types. closed records the atys closed in
     this scope (issued here or transferred by incarnation) so
     their closure can be re-applied on incarnation. *)
  sr : Subordination.sr ;
  closed : aty list ;
}

(* A template is what an instantiable module is *)
and template = {
  name : id ;
  params : id list ;
  (* the template's own view of its frame *)
  frame : frame ;
}

type spec = {
  name : id ;
  clauses : (string list * term) Itab.t ;
}

type env_kind =
  | Thm of spec option
  | Thmod

type t = {
  parents : frame list ;
  current : frame ;
  kind : env_kind ;
}

type error =
  | Unknown_ty of id
  | Unknown_const of id
  | Unknown_theorem of id
  | Unknown_module of id
  | Redeclared_ty of id
  | Redeclared_const of id
  | Redeclared_theorem of id
  | Redeclared_module of id
  | Bad_defblock of def
  | Unknown_template of id
  | Arity_mismatch of id list * int
  | Unknown_pred of id
  | Pred_mismatch of id * ty * ty
  | Pred_not_prop of id
  | Unknown_axiom of id
  | Bad_axiom_value of id
  | Axiom_mismatch of id * id
  | Clash of id
  | Close_undeclared of id
  | Close_failed of string

(******************************************************************************)
(* Lookup *)

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
         | Some pty -> Result.ok pty
         | None -> lookup1 rest)
  in
  lookup1 (env.current :: env.parents)

let lookup_const_fresh env x =
  lookup_const env x
  |> Result.map Typing.freshen_ty

let lookup_def env x =
  let rec lookup1 = function
    | [] -> Result.error @@ Unknown_const x
    | env :: rest ->
        let rec spin x =
          match Itab.find_opt x env.defs with
          | Some (`def df) -> Result.ok df
          | Some (`fwd x) -> spin x
          | None -> lookup1 rest
        in
        spin x
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
      let Typing.Poly (_, ty) = pty in
      let sr = Subordination.update env.current.sr ty in
      let current = { env.current with consts ; sr } in
      Result.ok { env with current }

let add_def env def =
  (* NB: like the top-level Define path, this adds no sr edges; def
     types join sr when merged at incarnation. *)
  let open Result.Syntax in
  let rec check_redef ks =
    match ks () with
    | Seq.Nil -> Result.ok ()
    | Seq.Cons ((dpred, _), ks) -> (
        let* () = match Itab.find_opt dpred env.current.defs with
          | None -> Result.ok ()
          | Some _ -> Result.error @@ Redeclared_const dpred
        in
        check_redef ks
      ) in
  let* () = check_redef (Itab.to_seq def.mutual) in
  let* canid = match Itab.choose_opt def.mutual with
    | Some (t, _) -> Result.ok t
    | None -> Result.error @@ Bad_defblock def
  in
  let to_add =
    Itab.to_seq def.mutual
    |> Seq.map (fun (k, _) ->
        (k, if k = canid then `def def else `fwd canid)) in
  let defs = Itab.add_seq to_add env.current.defs in
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

let frame_keys m = List.map fst (List.of_seq (Itab.to_seq m))

let close_frame env atys =
  let open Result.Syntax in
  let* () =
    List.fold_left
      (fun acc aty ->
        let* () = acc in
        match aty with
        | Tycons (nm, _) when List.mem nm (frame_keys env.current.tys) ->
            Result.ok ()
        | Tycons (nm, _) -> Result.error @@ Close_undeclared nm
        | _ -> Result.ok ())
      (Result.ok ()) atys
  in
  let* () =
    match List.intersect (List.map tybase atys) [oty; olistty; propty] with
    | [] -> Result.ok ()
    | bad ->
        Result.error @@ Close_failed
          ("Cannot close "
           ^ String.concat ", "
               (List.map (fun ty -> ty_to_string ty) bad))
  in
  match Subordination.close env.current.sr atys with
  | sr ->
      Result.ok
        { env with
          current =
            { env.current with sr ; closed = atys @ env.current.closed } }
  | exception Failure msg -> Result.error @@ Close_failed msg

(******************************************************************************)
(* Incarnation *)

let subst_of_args params args =
  if List.length args <> List.length params then
    Result.error @@ Arity_mismatch (params, List.length args)
  else
    Result.ok (List.combine params args)

let find_const_schema env x =
  let rec spin = function
    | [] -> None
    | fr :: rest -> (
        match Itab.find_opt x fr.consts with
        | Some _ as found -> found
        | None -> spin rest)
  in
  spin (env.current :: env.parents)

let canonical_tyvar i = Ty ([], Tygenvar ("S" ^ string_of_int i))

let canonicalize (Typing.Poly (pas, ty)) =
  apply_sub_ty (List.mapi (fun i p -> (p, canonical_tyvar i)) pas) ty

let target_is_prop ty =
  match observe_ty ty with
  | Ty (_, aty) -> aty = propaty

let poly_compatible pk pv =
  let Typing.Poly (pas, _) = pk in
  let Typing.Poly (pbs, tyv) = pv in
  let ck = canonicalize pk in
  List.length pas = List.length pbs
  && List.exists
       (fun perm ->
         eq_ty ck
           (apply_sub_ty
              (List.mapi (fun i p -> (p, canonical_tyvar i)) perm)
              tyv))
       (List.permute (List.length pbs) pbs)

let rec subst_const_tm k v t =
  match observe (hnorm t) with
  | Var vr when vr.tag = Constant && vr.name = k ->
      var Constant v vr.ts vr.ty
  | Var _ | DB _ -> t
  | Lam (cx, b) -> lambda cx (subst_const_tm k v b)
  | App (h, args) ->
      app (subst_const_tm k v h) (List.map (subst_const_tm k v) args)
  | Ptr _ | Susp _ -> [%bug] "subst_const_tm: unexpected term form"

let rec subst_const_mt k v mt =
  let open Metaterm in
  match mt with
  | True | False -> mt
  | Eq (a, b) -> Eq (subst_const_tm k v a, subst_const_tm k v b)
  | Obj (o, r) ->
      let context = Context.map (subst_const_tm k v) o.context in
      let right = subst_const_tm k v o.right in
      let mode =
        match o.mode with
        | Async -> Async
        | Sync f -> Sync (subst_const_tm k v f)
      in
      Obj ({ context ; right ; mode }, r)
  | Arrow (a, b) ->
      Arrow (subst_const_mt k v a, subst_const_mt k v b)
  | Binding (q, tids, b) -> Binding (q, tids, subst_const_mt k v b)
  | Or (a, b) -> Or (subst_const_mt k v a, subst_const_mt k v b)
  | And (a, b) -> And (subst_const_mt k v a, subst_const_mt k v b)
  | Pred (p, r) -> Pred (subst_const_tm k v p, r)

let subst_const_guard k v (g : guard) =
  { predicate = (if g.predicate = k then v else g.predicate) ;
    pattern = subst_const_tm k v g.pattern ;
    condition = List.map (subst_const_tm k v) g.condition }

let rec rename_tycons locals repl ty =
  match observe_ty ty with
  | Ty (args, aty) ->
      Ty (List.map (rename_tycons locals repl) args,
          rename_aty locals repl aty)

and rename_aty locals repl = function
  | Tycons (nm, args) ->
      let nm = if List.mem nm locals then repl ^ "." ^ nm else nm in
      Tycons (nm, List.map (rename_tycons locals repl) args)
  | Tygenvar _ as aty -> aty
  | Typtr r as aty -> (
      match !r with
      | TV _ -> aty
      | TT ty -> Typtr (ref (TT (rename_tycons locals repl ty))))

type local_names = {
  ltys : id list ;
  lconsts : id list ;
}

let rec rename_const_tm locals repl t =
  match observe (hnorm t) with
  | Var vr when vr.tag = Constant && List.mem vr.name locals.lconsts ->
      var Constant (repl ^ "." ^ vr.name) vr.ts
        (rename_tycons locals.ltys repl vr.ty)
  | Var _ | DB _ -> t
  | Lam (cx, b) ->
      lambda
        (List.map (fun (x, ty) -> (x, rename_tycons locals.ltys repl ty))
           cx)
        (rename_const_tm locals repl b)
  | App (h, args) ->
      app (rename_const_tm locals repl h)
        (List.map (rename_const_tm locals repl) args)
  | Ptr _ | Susp _ -> [%bug] "rename_const_tm: unexpected term form"

let rec rename_const_mt locals repl mt =
  let open Metaterm in
  match mt with
  | True | False -> mt
  | Eq (a, b) ->
      Eq (rename_const_tm locals repl a, rename_const_tm locals repl b)
  | Obj (o, r) ->
      let context = Context.map (rename_const_tm locals repl) o.context in
      let right = rename_const_tm locals repl o.right in
      let mode =
        match o.mode with
        | Async -> Async
        | Sync f -> Sync (rename_const_tm locals repl f)
      in
      Obj ({ context ; right ; mode }, r)
  | Arrow (a, b) ->
      Arrow (rename_const_mt locals repl a, rename_const_mt locals repl b)
  | Binding (q, tids, b) ->
      Binding
        (q,
         List.map
           (fun (x, ty) -> (x, rename_tycons locals.ltys repl ty))
           tids,
         rename_const_mt locals repl b)
  | Or (a, b) ->
      Or (rename_const_mt locals repl a, rename_const_mt locals repl b)
  | And (a, b) ->
      And (rename_const_mt locals repl a, rename_const_mt locals repl b)
  | Pred (p, r) -> Pred (rename_const_tm locals repl p, r)

let rename_guard locals repl (g : guard) =
  { predicate =
      (if List.mem g.predicate locals.lconsts then
         repl ^ "." ^ g.predicate
       else g.predicate) ;
    pattern = rename_const_tm locals repl g.pattern ;
    condition = List.map (rename_const_tm locals repl) g.condition }

let formula_compatible (tvs1, f1) (tvs2, f2) =
  let open Metaterm in
  List.length tvs1 = List.length tvs2
  && (
    let sub =
      List.map2 (fun v1 v2 -> (v1, Ty ([], Tygenvar v2))) tvs1 tvs2
    in
    let f1 = map_on_tys (apply_sub_ty sub) f1 in
    try Term.unwind_state (fun () -> meta_right_unify f1 f2 ; true) ()
    with Unify.UnifyFailure _ -> false)

let subst_frame tysub (fr : frame) =
  let consts =
    Itab.map
      (fun (Typing.Poly (_, ty)) ->
        let ty = apply_sub_ty tysub ty in
        Typing.Poly (ty_gentyvars ty, ty))
      fr.consts
  in
  let defs =
    Itab.map (function
        | `def df ->
            let mutual = Itab.map (apply_sub_ty tysub) df.mutual in
            let clauses =
              List.map
                (fun (cl : def_clause) ->
                   { head =
                       Metaterm.map_on_tys (apply_sub_ty tysub) cl.head ;
                     body =
                       Metaterm.map_on_tys (apply_sub_ty tysub) cl.body ;
                   })
                df.clauses
            in
            let typarams =
              List.unique
                (List.flatten_map ty_gentyvars
                   (List.map snd (List.of_seq (Itab.to_seq mutual)))
                 @ List.flatten_map
                   (fun cl ->
                      Metaterm.metaterm_collect_gentyvar_names cl.head
                      @ Metaterm.metaterm_collect_gentyvar_names cl.body)
                   clauses)
            in
            `def { df with typarams ; mutual ; clauses }
        | `fwd _ as fwd -> fwd
      ) fr.defs
  in
  let theorems =
    Itab.map
      (fun (_, form, fin) ->
        let form = Metaterm.map_on_tys (apply_sub_ty tysub) form in
        (Metaterm.metaterm_collect_gentyvar_names form, form, fin))
      fr.theorems
  in
  let guards =
    Itab.map
      (List.map (fun g ->
           { g with
             pattern = term_map_on_tys (apply_sub_ty tysub) g.pattern ;
             condition =
               List.map (term_map_on_tys (apply_sub_ty tysub))
                 g.condition ;
           }))
      fr.guards
  in
  { fr with consts ; defs ; theorems ; guards }

let incarnate_pred env (fr : frame) k v =
  match Itab.find_opt k fr.consts with
  | None -> Result.error @@ Unknown_pred k
  | Some pk -> (
      match find_const_schema env v with
      | None -> Result.error @@ Unknown_pred v
      | Some pv ->
          let ck = canonicalize pk in
          if not (target_is_prop ck) then
            Result.error @@ Pred_not_prop k
          else if not (target_is_prop (canonicalize pv)) then
            Result.error @@ Pred_not_prop v
          else if not (poly_compatible pk pv) then
            Result.error @@ Pred_mismatch (k, ck, canonicalize pv)
          else
            let consts = Itab.remove k fr.consts in
            let theorems =
              Itab.map
                (fun (tvs, form, fin) -> (tvs, subst_const_mt k v form, fin))
                fr.theorems
            in
            let defs =
              Itab.map (function
                  | `def (df : def) ->
                      `def { df with
                             clauses =
                               List.map
                                 (fun (cl : def_clause) ->
                                    { head = subst_const_mt k v cl.head ;
                                      body = subst_const_mt k v cl.body ;
                                    })
                                 df.clauses }
                  | `fwd _ as fwd -> fwd
                ) fr.defs
            in
            let guards =
              Itab.fold
                (fun key gs acc ->
                  let key = if key = k then v else key in
                  let gs = List.map (subst_const_guard k v) gs in
                  match Itab.find_opt key acc with
                  | None -> Itab.add key gs acc
                  | Some old -> Itab.add key (gs @ old) acc)
                fr.guards Itab.empty
            in
            Result.ok { fr with consts ; theorems ; defs ; guards })

let check_axiom env (fr : frame) k v =
  match Itab.find_opt k fr.theorems with
  | Some (ktvs, kf, Axiomatic) -> (
      match lookup_theorem env v with
      | Ok (vtvs, vf, (Axiomatic | Finished))
        when formula_compatible (ktvs, kf) (vtvs, vf) ->
          Result.ok ()
      | Ok _ -> Result.error @@ Bad_axiom_value v
      | Error _ -> Result.error @@ Bad_axiom_value v)
  | _ -> Result.error @@ Unknown_axiom k

let prefix_frame (fr : frame) repl =
  let locals = { ltys = frame_keys fr.tys ;
                 lconsts = frame_keys fr.consts @ frame_keys fr.defs } in
  let dot x = repl ^ "." ^ x in
  let tys =
    Itab.fold (fun k v acc -> Itab.add (dot k) v acc) fr.tys Itab.empty
  in
  let consts =
    Itab.fold
      (fun k (Typing.Poly (pas, ty)) acc ->
        Itab.add (dot k)
          (Typing.Poly (pas, rename_tycons locals.ltys repl ty))
          acc)
      fr.consts Itab.empty
  in
  let defs =
    Itab.fold
      (fun k entry acc ->
        match entry with
        | `def (df : def) ->
            let df =
              { df with
                mutual =
                  Itab.fold
                    (fun m ty macc ->
                      Itab.add (dot m) (rename_tycons locals.ltys repl ty)
                        macc)
                    df.mutual Itab.empty ;
                clauses =
                  List.map
                    (fun (cl : def_clause) ->
                      { head = rename_const_mt locals repl cl.head ;
                        body = rename_const_mt locals repl cl.body ;
                      })
                    df.clauses ;
              }
            in
            Itab.add (dot k) (`def df) acc
        | `fwd target ->
            let target =
              if List.mem target locals.lconsts then dot target
              else target
            in
            Itab.add (dot k) (`fwd target) acc)
      fr.defs Itab.empty
  in
  let theorems =
    Itab.fold
      (fun k (tvs, form, fin) acc ->
        Itab.add (dot k) (tvs, rename_const_mt locals repl form, fin) acc)
      fr.theorems Itab.empty
  in
  let guards =
    Itab.fold
      (fun k gs acc ->
        let k =
          if List.mem k locals.lconsts then dot k else k
        in
        let gs = List.map (rename_guard locals repl) gs in
        match Itab.find_opt k acc with
        | None -> Itab.add k gs acc
        | Some old -> Itab.add k (gs @ old) acc)
      fr.guards Itab.empty
  in
  let closed =
    List.filter_map
      (fun aty ->
        match aty with
        | Tycons (nm, _) when List.mem nm locals.ltys ->
            Some (rename_aty locals.ltys repl aty)
        | Tycons _ -> None
        | _ -> Some aty)
      fr.closed
  in
  { fr with tys ; consts ; defs ; theorems ; guards ; closed ;
            templates = Itab.empty }

let merge_into cur m =
  Itab.fold
    (fun k v acc ->
      let open Result.Syntax in
      let* acc = acc in
      if Itab.mem k acc then Result.error @@ Clash k
      else Result.ok @@ Itab.add k v acc)
    m (Result.ok cur)

let sr_add_metaterm sr mt =
  let sr = ref sr in
  ignore
    (Metaterm.map_on_tys
       (fun ty -> sr := Subordination.update !sr ty ; ty)
       mt) ;
  !sr

let extend_current env (fr : frame) =
  let open Result.Syntax in
  let* () =
    List.fold_left
      (fun acc k ->
        let* () = acc in
        if Itab.mem k env.current.defs then Result.error @@ Clash k
        else Result.ok ())
      (Result.ok ()) (frame_keys fr.consts)
  in
  let* () =
    List.fold_left
      (fun acc k ->
        let* () = acc in
        if Itab.mem k env.current.consts || Itab.mem k env.current.defs
        then Result.error @@ Clash k
        else Result.ok ())
      (Result.ok ()) (frame_keys fr.defs)
  in
  let* tys = merge_into env.current.tys fr.tys in
  let* consts = merge_into env.current.consts fr.consts in
  let* defs = merge_into env.current.defs fr.defs in
  let* theorems = merge_into env.current.theorems fr.theorems in
  (* Mirrors subordinate installs: const schemas, def mutual and
     clause types, and theorem statements all extend sr. *)
  let sr =
    let sr =
      Itab.fold
        (fun _ (Typing.Poly (_, ty)) sr -> Subordination.update sr ty)
        fr.consts env.current.sr
    in
    let sr =
      Itab.fold
        (fun _ entry sr ->
          match entry with
          | `def (df : def) ->
              let sr =
                Itab.fold
                  (fun _ ty sr -> Subordination.update sr ty)
                  df.mutual sr
              in
              List.fold_left sr_add_metaterm sr
                (List.flatten_map
                   (fun cl -> [cl.head ; cl.body])
                   df.clauses)
          | `fwd _ -> sr)
        fr.defs sr
    in
    let sr =
      Itab.fold
        (fun _ (_, form, _) sr -> sr_add_metaterm sr form)
        fr.theorems sr
    in
    Subordination.close sr fr.closed
  in
  let closed = fr.closed @ env.current.closed in
  let guards =
    Itab.fold
      (fun k gs acc ->
        let old =
          match Itab.find_opt k acc with
          | None -> []
          | Some old -> old
        in
        Itab.add k (gs @ old) acc)
      fr.guards env.current.guards
  in
  Result.ok
    { env with current = { env.current with tys ; consts ; defs ;
                                              theorems ; guards ; sr ;
                                              closed } }

type incarnation_spec = {
  synonym : id option ;
  args : ty list ;
  preds : (id * id) list ;
  axioms : (id * id) list ;
}

let incarnate_template env name (spec : incarnation_spec) =
  let open Result.Syntax in
  let* templ =
    lookup_template env name
    |> Result.map_error (fun _ -> Unknown_template name)
  in
  let* tysub = subst_of_args templ.params spec.args in
  let frame = subst_frame tysub templ.frame in
  let* frame =
    List.fold_left
      (fun acc (k, v) ->
        let* fr = acc in
        incarnate_pred env fr k v)
      (Result.ok frame) spec.preds
  in
  let* () =
    List.fold_left
      (fun acc (k, v) ->
        let* () = acc in
        check_axiom env frame k v)
      (Result.ok ()) spec.axioms
  in
  let repl =
    match spec.synonym with
    | Some s -> s
    | None -> name
  in
  extend_current env (prefix_frame frame repl)

(******************************************************************************)
(* Error messages *)

let pp_error ppf e =
  let open Format in
  match e with
  | Unknown_ty x -> fprintf ppf "Unknown type constructor: %s" x
  | Unknown_const x -> fprintf ppf "Unknown constant: %s" x
  | Unknown_theorem x -> fprintf ppf "Could not find theorem named %S" x
  | Unknown_module x -> fprintf ppf "Unknown module %s" x
  | Redeclared_ty x -> fprintf ppf "Type %s is already declared" x
  | Redeclared_const x -> fprintf ppf "Constant %s is already declared" x
  | Redeclared_theorem x -> fprintf ppf "Theorem %s is already declared" x
  | Redeclared_module x -> fprintf ppf "Module %s is already declared" x
  | Bad_defblock _ -> fprintf ppf "Definition block has no predicates"
  | Unknown_template x -> fprintf ppf "Unknown module template %s" x
  | Arity_mismatch (params, n) ->
      fprintf ppf "Expected %d type arguments (%s) but got %d"
        (List.length params) (String.concat ", " params) n
  | Unknown_pred x ->
      fprintf ppf "%s is not a declared or defined predicate" x
  | Pred_mismatch (k, expected, found) ->
      fprintf ppf "Incompatible replacement for predicate %s: %s vs %s"
        k (ty_to_string expected) (ty_to_string found)
  | Pred_not_prop x -> fprintf ppf "Predicate %s must target prop" x
  | Unknown_axiom x -> fprintf ppf "Unknown axiom %s" x
  | Bad_axiom_value x ->
      fprintf ppf "%s is not an axiom or finished theorem" x
  | Axiom_mismatch (k, v) ->
      fprintf ppf "Axiom value %s does not have the same statement as key %s"
        v k
  | Clash x -> fprintf ppf "Name %s is already in scope" x
  | Close_undeclared x ->
      fprintf ppf "Cannot close %s: not declared in the current frame" x
  | Close_failed msg -> fprintf ppf "%s" msg

let error_to_string e = Format.asprintf "%a" pp_error e
