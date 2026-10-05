open Extensions

type named_term = { name : string ; term : string }

type outcome =
  | Success of named_term list
  | Failure of string

type record = {
  kind    : string ;
  left    : string ;
  right   : string ;
  used    : named_term list ;
  outcome : outcome ;
}

let records : record list ref = ref []
let outfile : string option ref = ref None

let set_output filename = outfile := Some filename

let add r = records := r :: !records

let json_of_named_term ~key t =
  `Assoc [ key, `String t.name ; "term", `String t.term ]

let json_of_record r =
  let base = [
    "kind", `String r.kind ;
    "problem", `Assoc [ "left", `String r.left ; "right", `String r.right ] ;
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
