open Extensions

module Cbor = CBOR.Simple

module Immut = struct
  exception CborError of string

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

  let rec to_ty (Ty (args, aty)) : Term.ty =
    Term.Ty (List.map to_ty args, to_aty aty)

  and to_aty (aty : aty) : Term.aty =
    match aty with
    | Tyvar v -> Term.Tygenvar v
    | Tycons (c, args) -> Term.Tycons (c, List.map to_ty args)

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

  let rec ty_to_cbor (Ty (args, aty)) : Cbor.t =
    `Map [
      `Text "args", `Array (List.map ty_to_cbor args) ;
      `Text "head", aty_to_cbor aty ;
    ]

  and aty_to_cbor (aty : aty) : Cbor.t =
    match aty with
    | Tyvar v -> `Map [ `Text "tyvar", `Text v ]
    | Tycons (c, args) ->
        `Map [
          `Text "tycons", `Text c ;
          `Text "args", `Array (List.map ty_to_cbor args) ;
        ]

  let tyctx_to_cbor (ctx : tyctx) : Cbor.t =
    `Array (List.map (fun (name, ty) ->
        `Map [ `Text "name", `Text name ; `Text "ty", ty_to_cbor ty ]) ctx)

  let rec tm_to_cbor (tm : tm) : Cbor.t =
    match tm with
    | Var v ->
        `Map [
          `Text "var", `Text v.name ;
          `Text "tag", `Text (tag_to_string v.tag) ;
          `Text "ts", `Int v.ts ;
          `Text "ty", ty_to_cbor (of_ty v.ty) ;
        ]
    | DB i -> `Map [ `Text "db", `Int i ]
    | Lam (ctx, body) ->
        `Map [
          `Text "lam", `Map [
            `Text "ctx", tyctx_to_cbor ctx ;
            `Text "body", tm_to_cbor body ;
          ] ;
        ]
    | App (head, args) ->
        `Map [
          `Text "app", `Map [
            `Text "head", tm_to_cbor head ;
            `Text "args", `Array (List.map tm_to_cbor args) ;
          ] ;
        ]

  let cbor_error fmt =
    Printf.ksprintf (fun msg -> raise (CborError msg)) fmt

  let get_field key = function
    | `Map fields -> begin
        match List.assoc_opt (`Text key) fields with
        | Some cbor -> cbor
        | None -> cbor_error "missing field %S" key
      end
    | _ -> cbor_error "expected a map to read field %S from" key

  let string_of_cbor = function
    | `Text s -> s
    | _ -> cbor_error "expected a string"

  let int_of_cbor = function
    | `Int i -> i
    | _ -> cbor_error "expected an integer"

  let list_of_cbor f = function
    | `Array cs -> List.map f cs
    | _ -> cbor_error "expected an array"

  let tag_of_string = function
    | "eigen" -> Term.Eigen
    | "constant" -> Term.Constant
    | "logic" -> Term.Logic
    | "nominal" -> Term.Nominal
    | s -> cbor_error "unknown variable tag %S" s

  let rec ty_of_cbor (cbor : Cbor.t) : ty =
    Ty (list_of_cbor ty_of_cbor (get_field "args" cbor),
        aty_of_cbor (get_field "head" cbor))

  and aty_of_cbor (cbor : Cbor.t) : aty =
    match cbor with
    | `Map fields when List.mem_assoc (`Text "tyvar") fields ->
        Tyvar (string_of_cbor (List.assoc (`Text "tyvar") fields))
    | `Map _ ->
        Tycons (string_of_cbor (get_field "tycons" cbor),
                list_of_cbor ty_of_cbor (get_field "args" cbor))
    | _ -> cbor_error "expected a map for a type"

  let tyctx_of_cbor (cbor : Cbor.t) : tyctx =
    list_of_cbor (fun entry ->
        (string_of_cbor (get_field "name" entry), ty_of_cbor (get_field "ty" entry)))
      cbor

  let rec tm_of_cbor (cbor : Cbor.t) : tm =
    match cbor with
    | `Map fields when List.mem_assoc (`Text "var") fields ->
        let name = string_of_cbor (List.assoc (`Text "var") fields) in
        let tag = tag_of_string (string_of_cbor (List.assoc (`Text "tag") fields)) in
        let ts = int_of_cbor (get_field "ts" cbor) in
        let ty = to_ty (ty_of_cbor (get_field "ty" cbor)) in
        Var (Term.term_to_var (Term.var tag name ts ty))
    | `Map fields when List.mem_assoc (`Text "db") fields ->
        DB (int_of_cbor (List.assoc (`Text "db") fields))
    | `Map fields when List.mem_assoc (`Text "lam") fields ->
        let lam = List.assoc (`Text "lam") fields in
        Lam (tyctx_of_cbor (get_field "ctx" lam),
             tm_of_cbor (get_field "body" lam))
    | `Map fields when List.mem_assoc (`Text "app") fields ->
        let app = List.assoc (`Text "app") fields in
        App (tm_of_cbor (get_field "head" app),
             list_of_cbor tm_of_cbor (get_field "args" app))
    | `Map _ -> cbor_error "unknown term constructor"
    | _ -> cbor_error "expected a map for a term"
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

let cbor_of_named_term ~key t =
  `Map [ `Text key, `Text t.name ; `Text "term", Immut.tm_to_cbor t.term ]

let cbor_of_record r =
  let base = [
    `Text "kind", `Text r.kind ;
    `Text "problem", `Map [
      `Text "left", Immut.tm_to_cbor r.left ;
      `Text "right", Immut.tm_to_cbor r.right ;
    ] ;
    `Text "used", `Array (List.map (cbor_of_named_term ~key:"name") r.used) ;
  ] in
  let outcome = match r.outcome with
    | Success sol ->
        [ `Text "result", `Text "success" ;
          `Text "solution", `Array (List.map (cbor_of_named_term ~key:"var") sol) ]
    | Failure msg ->
        [ `Text "result", `Text "failure" ;
          `Text "failure", `Text msg ;
          `Text "solution", `Array [] ]
  in
  `Map (base @ outcome)

let write () =
  match !outfile with
  | None -> ()
  | Some f ->
      let oc = open_out_bin f in
      let cbor = `Array (List.rev_map cbor_of_record !records) in
      output_string oc (Cbor.encode cbor) ;
      close_out oc

let () = if Term.log_unifications then at_exit write
