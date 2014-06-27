open Term
open Typing

exception TranslationError of string 

 let generate_name =
  let counter = ref 0 in
  fun () -> (incr counter; "V" ^ (string_of_int (!counter))) 

let is_type t = app (const "istype" (tyarrow [lftypety] oty)) [t]

let has_type term ty pos =
  app (const "hastype" (tyarrow [lfobjty; lftypety] oty)) [term; ty]

let rec trans_type t =
  match t with
  | UCon(p, x, ty) -> lfobjty
  | UType(p) -> lftypety
  | UImp(p, t1, t2) -> tyarrow [trans_type t1] (trans_type t2)
  | UApp(p, t1, t2) -> trans_type t1
  | _ -> raise (TranslationError "invalid type")

let rec trans_term t =
  match t with
  | UCon(p, x, ty) -> const x ty
  | UApp(p, t1, t2) -> app (trans_term t1) [(trans_term t2)]
  | UAbs(p, x, a, b) -> abstract x (trans_type a) (trans_term b)
  | _ -> raise (TranslationError "invalid term")

let rec translate t = 
  let translate_abstraction_type x a t1 t2 pos =
    let r = UJudge(pos, t1, t2) in
    let r' = translate r in
    let l = UJudge(pos, UCon(pos, x, (trans_type a)), a) in
    let l' = translate l in
    (* "forall x, l' => r'" *)
  in 
  match t with
    | UJudge(p, UAbs(q, x, a, b), UPi(q', x', a', b')) ->
       if x=x' && a= a' then (* MKS: shouldn't this be alpha equiv rather than eq? *)
         translate_abstraction_type x a b b' p
       else
         raise (TranslationError "invalid quantification")
    | UJudge(p, tm, UPi(q, x, a, b)) ->
       let tm' = UApp(p, tm, UCon(p, x, (trans_type a))) in
       translate_abstraction_type x a tm' b p
    | UJudge(p, tm, UImp(q, t1, t2)) ->
       let x = (generate_name ()) in
       let tm' = UApp(p, tm, UCon(p, x, (trans_type t1))) in
       translate_abstraction_type x t1 tm' t2 p
    | UJudge(p, tm, UType(q)) -> is_type (trans_term tm)
    | UJudge(p, t1, t2) -> has_type (trans_term t1) (trans_term t2) p
    | _ -> raise (TranslationError "Only LF judgements may be translated")
