let do_tracing = true

open Ppxlib

let string_of_location ~loc =
  let pos = loc.loc_start in
  Stdlib.Printf.sprintf "%s:%d.%d"
    pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let trace_expander =
  let name = "trace" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(pstr nil) in
  let open Ast_builder.Default in
  let printer ~loc =
    if do_tracing then evar ~loc "Output.msg_format" else
      eapply ~loc (evar ~loc "Stdlib.Format.ifprintf")
        [ evar ~loc "Stdlib.Format.err_formatter" ] in
  let expand ~ctxt =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    eapply ~loc (printer ~loc)
      [ estring ~loc @@
        "@[<hov2>TRACE[" ^ string_of_location ~loc ^ "]@ %t@]" ]
  in
  Extension.V3.declare name context extractor expand |>
  Context_free.Rule.extension

let tracef_expander =
  let name = "tracef" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(pstr nil) in
  let open Ast_builder.Default in
  let printer ~loc =
    if do_tracing then evar ~loc "Output.msg_format" else
      eapply ~loc (evar ~loc "Stdlib.Format.ifprintf")
        [ evar ~loc "Stdlib.Format.err_formatter" ] in
  let expand ~ctxt =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    pexp_fun ~loc Nolabel None
      (ppat_var ~loc { loc ; txt = "fmt" }) @@
    eapply ~loc (printer ~loc)
      [ eapply ~loc (evar ~loc "Stdlib.^^")
          [ eapply ~loc (evar ~loc "Stdlib.^^")
              [ estring ~loc @@
                "@[<hov2>TRACE[" ^ string_of_location ~loc ^ "]@ " ;
                evar ~loc "fmt" ] ;
            estring ~loc "@]" ] ]
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
      tracef_expander ;
      bug_expander ;
    ]
