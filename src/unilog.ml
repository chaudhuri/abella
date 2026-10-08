open Extensions

module Immut = struct
  type ty = Ty of ty list * aty

  and aty =
    | Tyvar of Term.tyvar
    | Tycons of Term.id * ty list

  type tyctx = (Term.id * ty) list

  type tm =
    | Var of Term.var
    | DB of int
    | Lam of tyctx * tm
    | App of tm * tm list

  let rec of_ty (ty : Term.ty) : ty =
    match Term.observe_ty ty with
    | Term.Ty (args, aty) ->
        let Ty (args', head) = of_aty aty in
        Ty (List.map of_ty args @ args', head)

  and of_aty (aty : Term.aty) : ty =
    match aty with
    | Term.Tygenvar v -> Ty ([], Tyvar v)
    | Term.Tycons (c, args) -> Ty ([], Tycons (c, List.map of_ty args))
    | Term.Typtr {contents = Term.TV v} -> Ty ([], Tyvar v)
    | Term.Typtr {contents = Term.TT t} -> of_ty t

  let of_tyctx (ctx : Term.tyctx) : tyctx =
    List.map (fun (id, ty) -> (id, of_ty ty)) ctx

  let rec of_tm (tm : Term.term) : tm =
    match Term.observe (Term.hnorm tm) with
    | Term.Var v -> Var v
    | Term.DB i -> DB i
    | Term.Lam (ctx, body) -> Lam (of_tyctx ctx, of_tm body)
    | Term.App (head, args) -> App (of_tm head, List.map of_tm args)
    | Term.Susp _ -> assert false
    | Term.Ptr _ -> assert false

  let tag_to_string = function
    | Term.Eigen -> "eigen"
    | Term.Constant -> "constant"
    | Term.Logic -> "logic"
    | Term.Nominal -> "nominal"

  let rec ty_to_yojson (Ty (args, aty)) : Json.t =
    `Assoc [
      "args", `List (List.map ty_to_yojson args) ;
      "head", aty_to_yojson aty ;
    ]

  and aty_to_yojson (aty : aty) : Json.t =
    match aty with
    | Tyvar v -> `Assoc [ "tyvar", `String v ]
    | Tycons (c, args) ->
        `Assoc [
          "tycons", `String c ;
          "args", `List (List.map ty_to_yojson args) ;
        ]

  let tyctx_to_yojson (ctx : tyctx) : Json.t =
    `List (List.map (fun (name, ty) ->
        `Assoc [ "name", `String name ; "ty", ty_to_yojson ty ]) ctx)

  let rec tm_to_yojson (tm : tm) : Json.t =
    match tm with
    | Var v ->
        `Assoc [ "var", `String v.name ; "tag", `String (tag_to_string v.tag) ]
    | DB i -> `Assoc [ "db", `Int i ]
    | Lam (ctx, body) ->
        `Assoc [
          "lam", `Assoc [
            "ctx", tyctx_to_yojson ctx ;
            "body", tm_to_yojson body ;
          ] ;
        ]
    | App (head, args) ->
        `Assoc [
          "app", `Assoc [
            "head", tm_to_yojson head ;
            "args", `List (List.map tm_to_yojson args) ;
          ] ;
        ]
end

type named_term = { name : string ; term : Immut.tm }

type outcome =
  | Success of named_term list
  | Failure of string

type record = {
  kind    : string ;
  left    : Immut.tm ;
  right   : Immut.tm ;
  used    : named_term list ;
  outcome : outcome ;
}

let records : record list ref = ref []
let outfile : string option ref = ref None

let set_output filename = outfile := Some filename

let add r = records := r :: !records

let json_of_named_term ~key t =
  `Assoc [ key, `String t.name ; "term", Immut.tm_to_yojson t.term ]

let json_of_record r =
  let base = [
    "kind", `String r.kind ;
    "problem", `Assoc [
      "left", Immut.tm_to_yojson r.left ;
      "right", Immut.tm_to_yojson r.right ;
    ] ;
    "used", `List (List.map (json_of_named_term ~key:"name") r.used) ;
  ] in
  let outcome = match r.outcome with
    | Success sol ->
        [ "result", `String "success" ;
          "solution", `List (List.map (json_of_named_term ~key:"var") sol) ]
    | Failure msg ->
        [ "result", `String "failure" ;
          "failure", `String msg ;
          "solution", `List [] ]
  in
  `Assoc (base @ outcome)

let write () =
  match !outfile with
  | None -> ()
  | Some f ->
      let oc = open_out_bin f in
      Json.to_channel oc (`List (List.rev_map json_of_record !records)) ;
      close_out oc

let () = if Term.log_unifications then at_exit write
