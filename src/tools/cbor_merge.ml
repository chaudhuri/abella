(* Merge a stream of top-level CBOR arrays (as produced by Unilog) into a
   single CBOR array. Reads concatenated CBOR values from stdin and writes
   one merged array to stdout.

   Elements are copied verbatim rather than decoded, so the merge never
   materializes the (potentially huge) trace structures in memory. *)

let fail fmt = Printf.ksprintf failwith fmt

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

let byte s i =
  if i < 0 || i >= String.length s then fail "truncated CBOR" else Char.code s.[i]

(* [length s pos add] decodes the argument encoded in the byte at [pos] and
   returns it together with the position just past the encoding. Indefinite
   lengths are reported as -1. *)
let length s pos add =
  match add with
  | a when a < 24 -> (a, pos + 1)
  | 24 -> (byte s (pos + 1), pos + 2)
  | 25 -> ((byte s (pos + 1) lsl 8) lor byte s (pos + 2), pos + 3)
  | 26 ->
      ((byte s (pos + 1) lsl 24) lor (byte s (pos + 2) lsl 16)
       lor (byte s (pos + 3) lsl 8) lor byte s (pos + 4), pos + 5)
  | 27 ->
      let v = ref 0 in
      for k = 0 to 7 do v := (!v lsl 8) lor byte s (pos + 1 + k) done ;
      (!v, pos + 9)
  | 31 -> (-1, pos + 1)
  | a -> fail "invalid CBOR length encoding %d" a

let rec skip_item s pos =
  let b = byte s pos in
  let major = b lsr 5 and add = b land 0x1f in
  match major with
  | 0 | 1 -> snd (length s pos add)
  | 2 | 3 -> begin
      let (len, p) = length s pos add in
      if len >= 0 then p + len else skip_chunks s p
    end
  | 4 -> begin
      let (len, p) = length s pos add in
      if len >= 0 then skip_items s p len else skip_break s p
    end
  | 5 -> begin
      let (len, p) = length s pos add in
      if len >= 0 then skip_items s p (2 * len) else skip_break s p
    end
  | 6 -> skip_item s (snd (length s pos add))
  | 7 -> begin
      match add with
      | a when a < 24 || a = 31 -> pos + 1
      | 24 -> pos + 2
      | 25 -> pos + 3
      | 26 -> pos + 5
      | 27 -> pos + 9
      | a -> fail "invalid CBOR simple value %d" a
    end
  | _ -> assert false

and skip_items s pos k =
  if k = 0 then pos else skip_items s (skip_item s pos) (k - 1)

and skip_break s pos =
  if byte s pos = 0xff then pos + 1 else skip_break s (skip_item s pos)

and skip_chunks s pos =
  let b = byte s pos in
  if b = 0xff then pos + 1
  else begin
    if b lsr 5 <> 2 && b lsr 5 <> 3 then fail "invalid CBOR string chunk" ;
    let (len, p) = length s pos (b land 0x1f) in
    skip_chunks s (p + len)
  end

(* [array_bounds s pos] returns the element count, the position of the first
   element, and the position just past a definite-length top-level array. *)
let array_bounds s pos =
  let b = byte s pos in
  if b lsr 5 <> 4 then fail "expected a top-level CBOR array" ;
  let add = b land 0x1f in
  if add = 31 then fail "indefinite top-level CBOR array is not supported" ;
  let count, content = length s pos add in
  (count, content, skip_items s content count)

let emit_array_header oc n =
  if n < 24 then
    output_byte oc (0x80 lor n)
  else if n < 256 then begin
    output_byte oc 0x98 ;
    output_byte oc n
  end
  else if n < 65536 then begin
    output_byte oc 0x99 ;
    output_byte oc (n lsr 8) ;
    output_byte oc (n land 0xff)
  end
  else if n <= 0xffffffff then begin
    output_byte oc 0x9a ;
    output_byte oc (n lsr 24) ;
    output_byte oc ((n lsr 16) land 0xff) ;
    output_byte oc ((n lsr 8) land 0xff) ;
    output_byte oc (n land 0xff)
  end
  else begin
    output_byte oc 0x9b ;
    for k = 7 downto 0 do
      output_byte oc ((n lsr (8 * k)) land 0xff)
    done
  end

let () =
  let data = read_all stdin in
  let len = String.length data in
  let total = ref 0 in
  let pos = ref 0 in
  while !pos < len do
    let count, _content, next = array_bounds data !pos in
    total := !total + count ;
    pos := next
  done ;
  emit_array_header stdout !total ;
  let pos = ref 0 in
  while !pos < len do
    let _count, content, next = array_bounds data !pos in
    output_substring stdout data content (next - content) ;
    pos := next
  done
