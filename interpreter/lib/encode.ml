open Z

(* Interleave two integers bitwise. 
 * Example: x = 0b101 and y = 0b110
 * results in 0b111001. *)
let rec interleave_int (x : t) (y : t) : t =
  if x = zero && y = zero
  then zero
  else
    let x1 = x land one
    and y1 = (y land one) lsl 1
    and x2 = x asr 1
    and y2 = y asr 1 in
    x1 + y1 + ((interleave_int x2 y2) lsl 2)

let encode_int (x : t) (y : t) =
  let sign_bits = of_string @@ begin
    match (sign y, sign x) with
      | (-1, -1) -> "0b11"
      | (-1, _)  -> "0b10"
      | (_, -1)  -> "0b01"
      | _        -> "0b00"
  end in
  let interleaved = interleave_int (abs x) (abs y) in
  sign_bits + (interleaved lsl 2)

let rec split_int (i : t) : t * t =
  if i = zero
  then zero, zero
  else
    let x1 = i land one
    and y1 = (i asr 1) land one
    and (x2, y2) = split_int (i asr 2) in
    (x1 + (x2 lsl 1), y1 + (y2 lsl 1))

let decode_int (i : t) : t * t =
  let x1 = i land one
  and y1 = (i asr 1) land one in
  let f = begin
    fun (x, y) ->
    if x1 = one then
      if y1 = one
      then (neg x, neg y)
      else (neg x, y)
    else
      if y1 = one
      then (x, neg y)
      else (x, y)
    end in
  f @@ split_int (i asr 2)
