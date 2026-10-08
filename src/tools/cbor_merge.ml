(* Merge a stream of top-level CBOR arrays (as produced by Unilog) into a
   single CBOR array. Reads concatenated CBOR values from stdin and writes
   one merged array to stdout. Used by test/unify_experiments.sh. *)

let read_all ic =
  let chunk = Bytes.create 65536 in
  let buf = Buffer.create 65536 in
  let rec loop () =
    let n = input ic chunk 0 (Bytes.length chunk) in
    if n > 0 then begin
      Buffer.add_subbytes buf chunk 0 n ;
      loop ()
    end
  in
  loop () ;
  Buffer.contents buf

let rec collect arrays data =
  if data = "" then List.rev arrays
  else
    let item, rest = CBOR.Simple.decode_partial data in
    match item with
    | `Array records -> collect (List.rev_append records arrays) rest
    | _ -> failwith "cbor_merge: expected a top-level CBOR array"

let () =
  let records = collect [] (read_all stdin) in
  output_string stdout (CBOR.Simple.encode (`Array records))
