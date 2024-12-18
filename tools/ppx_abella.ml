let do_tracing = true
let format = "Output.msg_format"
let verbosity = "Output.trace_verbosity"

open Ppxlib

let string_of_location ~loc =
  let pos = loc.loc_start in
  Stdlib.Printf.sprintf "%s:%d.%d"
    pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let rm_labelled lab alist =
  let rec extract seen l =
    match l with
    | [] -> (None, List.rev seen)
    | (Labelled x, a) :: l when x = lab -> (Some a, List.rev_append seen l)
    | u :: l -> extract (u :: seen) l
  in
  extract [] alist

let trace_expander =
  let name = "trace" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(single_expr_payload (pexp_apply (eint __) (many __))) in
  let open Ast_builder.Default in
  let expand ~ctxt verb args =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    let (kind, args) = rm_labelled "kind" args in
    match List.map snd args with
    | fmt :: args ->
        let (kind_space, kind_arg) = match kind with
          | None -> "", estring ~loc ""
          | Some expr -> " ", expr
        in
        let ( ^^ ) f1 f2 = eapply ~loc (evar ~loc "Stdlib.^^") [f1 ; f2] in
        let fmt =
          estring ~loc ("@[<hv4>>>>" ^ kind_space ^ "%s [at %s]@ ")
          ^^ fmt ^^
          estring ~loc "@]" in
        let pos_arg = estring ~loc (string_of_location ~loc) in
        pexp_ifthenelse ~loc
          (eapply ~loc (evar ~loc "Stdlib.&&")
             [ ebool ~loc do_tracing ;
               (eapply ~loc (evar ~loc "Stdlib.<=")
                  [ eint ~loc verb ; eapply ~loc (evar ~loc "Stdlib.!") [evar ~loc verbosity] ]) ])
          (eapply ~loc (evar ~loc format) (fmt :: kind_arg :: pos_arg :: args))
          None
    | _ ->
        pexp_extension ~loc
          (Location.error_extensionf ~loc "Missing format string")
  in
  Extension.V3.declare name context extractor expand |>
  Context_free.Rule.extension

let bug_expander =
  let name = "bug" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(pstr nil) in
  let expand ~ctxt =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    let open Ast_builder.Default in
    let erf = evar ~loc "Stdlib.Format.err_formatter" in
    let continuation =
      let reportme =
        eapply ~loc (evar ~loc "Stdlib.Format.fprintf")
          [ erf ;
            estring ~loc "@.Please report this at \
                         \ https://github.com/abella-prover/abella/issues@." ] in
      let fail =
        eapply ~loc (evar ~loc "Stdlib.failwith")
          [ estring ~loc "Bug" ] in
      pexp_fun ~loc Nolabel None (ppat_any ~loc)
        (esequence ~loc [ reportme ; fail ])
    in
    esequence ~loc
      [ eapply ~loc (evar ~loc "Stdlib.Format.fprintf")
          [ erf ;
            estring ~loc ("ABELLA BUG at " ^ string_of_location ~loc ^ "@.") ] ;
        eapply ~loc (evar ~loc "Stdlib.Format.kfprintf")
          [ continuation ; erf  ] ]
  in
  Extension.V3.declare name context extractor expand |>
  Context_free.Rule.extension

let () =
  Driver.V2.register_transformation "ppx_abella"
    ~rules:[
      trace_expander ;
      (* tracef_expander ; *)
      bug_expander ;
    ]
