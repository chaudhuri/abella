open Extensions
open Term
open Spec

type hhwseq = {
  context : Context.t ;
  term    : term ;
}

let b_context = bucket "context"
let b_term    = bucket "term"

module Basic : Spec.Basic with type seq = hhwseq =
struct
  type seq = hhwseq    

  let make bucks =
    let ctx = ref [] in
    let conc = ref None in
    List.iter begin
      fun (b, ts) ->
        if b = b_context then
          if !ctx = [] then ctx := ts
          else failwith "Hhw.make: repeated bucket \"context\""
        else if b = b_term then
          if !conc = None then begin
            match ts with
            | [t] -> conc := Some t
            | _ -> failwith "Hhw.make: invalid contents of bucket \"term\""
          end
          else failwith "Hhw.make: repeated bucket \"term\""
        else failwith ("Hhw.make: unknown bucket \"" ^ (b :> string) ^ "\"")
    end bucks ;
    match !conc with
    | None -> failwith "Hhw.make: missing conclusion"
    | Some t -> { context = Context.of_list !ctx ; term = t }
    
  let to_string seq =
    let buf = Buffer.create 19 in
    Buffer.add_char buf '{' ;
    if not (Context.is_empty seq.context) then begin
      Buffer.add_string buf (Context.to_string seq.context) ;
      Buffer.add_string buf " |- "
    end ;
    Buffer.add_string buf (term_to_string seq.term) ;
    Buffer.add_char buf '}' ;
    Buffer.contents buf

  let map_terms fn seq =
    let context = Context.map (fn b_context) seq.context in
    let term = fn b_term seq.term in
    { context = context ; term = term }

  let iter_terms fn seq =
    Context.iter (fn b_context) seq.context ;
    fn b_term seq.term

  let cut cseq hseq =
    if Context.mem cseq.term hseq.context then
      let context = hseq.context
        |> Context.remove cseq.term
        |> Context.union cseq.context
        |> Context.normalize
      in
      if Context.wellformed context then
        { hseq with context = context }
      else failwith "hhw: cannot merge contexts"
  else failwith "hhw: needless use of cut"

  let support seq =
    let vs = find_var_refs Nominal (seq.term :: Context.to_list seq.context) in
    List.map (fun v -> (term_to_var v).name) vs
      
  let inst seq ws =
    let (seq, _) = List.fold_left begin
      fun (seq, supp) (n, repl) ->
        if List.mem n supp then
          let seq = map_terms (fun _ t -> Term.replace_vars ~tag:Nominal [(n, repl)] t) seq in
          let supp = List.filter (fun m -> n <> m) supp in
          (seq, supp)
        else failwith ("did not find " ^ n)
    end (seq, support seq) ws in
    seq

  let async_phase ~cont seq =
    let rec spin tys seq =
      match observe (hnorm seq.term) with
      | App (arr, [ant ; term]) when is_head_name "=>" arr ->
          spin tys { context = Context.add ant seq.context ; term = term }
      | App (pi, [term]) when is_head_name "pi" pi ->
          begin match observe term with
          | Lam (ty :: tys, term) ->
              spin (ty :: tys) { seq with term = Term.lambda tys term }
          | _ ->
              failwith ("hhw: async_phase: invalid_term: " ^ Term.term_to_string term)
          end
      | _ -> cont { tys = tys ; seq = seq }
    in
    spin [] seq

  let sync_phase  = fun ~cont _ -> failwith "sync_phase"

end

include Spec.Complete (Basic)
