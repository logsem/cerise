open Ast
open Z

exception DecodeException

(* Encodings of permissions satisfy
 * lattice structure by:
 * - join : bitwise or
 * - meet : bitwise and
 * - x flowsto y : y join x = y *)
let encode_perm (p : perm) : t =
  of_string @@
  match p with
  | O -> "0b000"
  | E -> "0b001"
  | RO -> "0b100"
  | RX -> "0b101"
  | RW -> "0b110"
  | RWX -> "0b111"

let decode_perm (i : t) : perm =
  let b0 = testbit i 0
  and b1 = testbit i 1
  and b2 = testbit i 2 in
  match (b0,b1,b2) with
  | (false, false, false) -> O
  | (false, false, true)  -> E
  | (true, false, false)  -> RO
  | (true, false, true)   -> RX
  | (true, true, false)   -> RW
  | (true, true, true)    -> RWX
  | _ -> raise DecodeException

let encode_reg (r : regname) : t =
  match r with
  | PC -> zero
  | Reg i -> succ @@ of_int i

let decode_reg (i : t) : regname =
  if i = zero
  then PC
  else Reg (to_int @@ pred i)

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

(* Encode two integers by interleaving their 
 * absolute values bitwise, followed
 * by two bits representing signs.
 *)
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
  let is_x_neg = testbit i 0
  and is_y_neg = testbit i 1 in
  let f = begin
    fun (x, y) ->
      match (is_x_neg, is_y_neg) with
      | (true, true) -> (neg x, neg y)
      | (true, false) -> (neg x, y)
      | (false, true) -> (x, neg y)
      | (false, false) -> (x, y)
  end in
  f @@ split_int (i asr 2)

let encode_statement (s : statement): t =
  let (!$) opcode = of_string opcode in
  let (^!) opcode args = opcode + (args lsl 8) in
  match s with
  | Jmp r -> !$"0x00" ^! (encode_reg r)
  | Jnz (r1, r2) -> !$"0x01" ^! encode_int (encode_reg r1) (encode_reg r2)
  | Move (r, c) -> begin
      let curried_enc = encode_int (encode_reg r) in
      match c with
      | Register r' -> !$"0x02" ^! curried_enc (encode_reg r')
      | Const i -> !$"0x03" ^! curried_enc (of_int i)
      | Perm p -> !$"0x04" ^! curried_enc (encode_perm p)
    end
  | _ -> zero
