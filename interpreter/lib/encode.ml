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
  match (b2,b1,b0) with
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

let (!$) opcode = of_string opcode

let encode_statement (s : statement): t =
  let (^!) opcode args = opcode + (args lsl 8) in
  let const_convert opcode c = begin
    match c with
    | Register r -> (opcode, encode_reg r)
    | Const i -> (succ opcode, of_int i)
    | Perm p -> (succ @@ succ opcode, encode_perm p)
  end in
  let two_const_convert opcode c1 c2 = begin
    let three = of_int 3
    and six = of_int 6 in
    let (opc1, c1_enc) = begin
      match c1 with
      | Register r -> (opcode, encode_reg r)
      | Const i -> (opcode + three, of_int i)
      | Perm p -> (opcode + six, encode_perm p)
    end in
    let (opc2, c2_enc) = const_convert opc1 c2 in
    (opc2, encode_int c1_enc c2_enc)
  end in
  match s with
  | Jmp r -> !$"0x00" ^! (encode_reg r)
  | Jnz (r1, r2) -> !$"0x01" ^! encode_int (encode_reg r1) (encode_reg r2)
  | Move (r, c) -> begin (* 0x02, 0x03, 0x04 *)
      let (opc, c_enc) = const_convert (!$"0x02") c in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Load (r1, r2) -> !$"0x05" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | Store (r, c) -> begin (* 0x06, 0x07, 0x08 *)
      let (opc, c_enc) = const_convert (!$"0x06") c in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Add (r, c1, c2) -> begin (* 0x09 to 0x11 *)
      let (opc, c_enc) = two_const_convert (!$"0x09") c1 c2 in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Sub (r, c1, c2) -> begin (* 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a *)
      let (opc, c_enc) = two_const_convert (!$"0x12") c1 c2 in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Lt (r, c1, c2) -> begin (* 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23 *)
      let (opc, c_enc) = two_const_convert (!$"0x1b") c1 c2 in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Lea (r, c) -> begin (* 0x24, 0x25, 0x26 *)
      let (opc, c_enc) = const_convert (!$"0x24") c in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | Restrict (r, c) -> begin (* 0x27, 0x28, 0x29 *)
      let (opc, c_enc) = const_convert (!$"0x27") c in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | SubSeg (r, c1, c2) -> begin (* 0x2a to 0x32 *)
      let (opc, c_enc) = two_const_convert (!$"0x2a") c1 c2 in
      opc ^! (encode_int (encode_reg r) c_enc)
    end
  | IsPtr (r1, r2) -> !$"0x33" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | GetP (r1, r2) -> !$"0x34" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | GetB (r1, r2) -> !$"0x35" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | GetE (r1, r2) -> !$"0x36" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | GetA (r1, r2) -> !$"0x37" ^! (encode_int (encode_reg r1) (encode_reg r2))
  | Fail -> !$"0x38"
  | Halt -> !$"0x39"

let decode_statement (i : t) : statement =
  let opc = extract i 0 8 
  and payload = i asr 8 in
  (* Jmp *)
  if opc = !$"0x00"
  then Jmp (decode_reg payload)
  else
  (* Jnz *)
  if opc = !$"0x01"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    Jnz (r1, r2)
  end else
  (* Move *)
  if opc = !$"0x02" (* register register *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r1 = decode_reg r_enc
    and r2 = Register (decode_reg c_enc) in
    Move (r1, r2)
  end else
  if opc = !$"0x03" (* register const *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and c = Const (to_int c_enc) in
    Move (r, c)
  end else
  if opc = !$"0x04" (* register perm *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and p = Perm (decode_perm c_enc) in
    Move (r, p)
  end else
  (* Load *)
  if opc = !$"0x05"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    Load (r1, r2)
  end else
  (* Store *)
  if opc = !$"0x06" (* register register *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r1 = decode_reg r_enc
    and r2 = Register (decode_reg c_enc) in
    Store (r1, r2)
  end else
  if opc = !$"0x07" (* register const *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and c = Const (to_int c_enc) in
    Store (r, c)
  end else
  if opc = !$"0x08" (* register perm *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and p = Perm (decode_perm c_enc) in
    Store (r, p)
  end else
  (* Add *)
  if !$"0x08" < opc && opc < !$"0x0c"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Register (decode_reg c1_enc)
    and c2 = begin
      if opc = !$"0x09" then Register (decode_reg c2_enc) else
      if opc = !$"0x0a" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Add (r, c1, c2)
  end else
  if !$"0x0b" < opc && opc < !$"0x0f"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Const (to_int c1_enc)
    and c2 = begin
      if opc = !$"0x0c" then Register (decode_reg c2_enc) else
      if opc = !$"0x0d" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Add (r, c1, c2)
  end else
  if !$"0x0e" < opc && opc < !$"0x12"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Perm (decode_perm c1_enc)
    and c2 = begin
      if opc = !$"0x0f" then Register (decode_reg c2_enc) else
      if opc = !$"0x10" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Add (r, c1, c2)
  end else
  (* Sub *)
  if !$"0x11" < opc && opc < !$"0x15"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Register (decode_reg c1_enc)
    and c2 = begin
      if opc = !$"0x12" then Register (decode_reg c2_enc) else
      if opc = !$"0x13" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Sub (r, c1, c2)
  end else
  if !$"0x14" < opc && opc < !$"0x18"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Const (to_int c1_enc)
    and c2 = begin
      if opc = !$"0x15" then Register (decode_reg c2_enc) else
      if opc = !$"0x16" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Sub (r, c1, c2)
  end else
  if !$"0x17" < opc && opc < !$"0x1b"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Perm (decode_perm c1_enc)
    and c2 = begin
      if opc = !$"0x18" then Register (decode_reg c2_enc) else
      if opc = !$"0x19" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Sub (r, c1, c2)
  end else
  (* Lt *)
  if !$"0x1a" < opc && opc < !$"0x1e"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Register (decode_reg c1_enc)
    and c2 = begin
      if opc = !$"0x1b" then Register (decode_reg c2_enc) else
      if opc = !$"0x1c" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Lt (r, c1, c2)
  end else
  if !$"0x1c" < opc && opc < !$"0x21"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Const (to_int c1_enc)
    and c2 = begin
      if opc = !$"0x1e" then Register (decode_reg c2_enc) else
      if opc = !$"0x1f" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Lt (r, c1, c2)
  end else
  if !$"0x20" < opc && opc < !$"0x24"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Perm (decode_perm c1_enc)
    and c2 = begin
      if opc = !$"0x21" then Register (decode_reg c2_enc) else
      if opc = !$"0x22" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    Lt (r, c1, c2)
  end else
  (* Lea *)
  if opc = !$"0x24" (* register register *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r1 = decode_reg r_enc
    and r2 = Register (decode_reg c_enc) in
    Lea (r1, r2)
  end else
  if opc = !$"0x25" (* register const *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and c = Const (to_int c_enc) in
    Lea (r, c)
  end else
  if opc = !$"0x26" (* register perm *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and p = Perm (decode_perm c_enc) in
    Lea (r, p)
  end else
  (* Restrict *)
  if opc = !$"0x27" (* register register *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r1 = decode_reg r_enc
    and r2 = Register (decode_reg c_enc) in
    Restrict (r1, r2)
  end else
  if opc = !$"0x28" (* register const *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and c = Const (to_int c_enc) in
    Restrict (r, c)
  end else
  if opc = !$"0x29" (* register perm *)
  then begin
    let (r_enc, c_enc) = decode_int payload in
    let r = decode_reg r_enc
    and p = Perm (decode_perm c_enc) in
    Restrict (r, p)
  end else
  (* SubSeg *)
  if !$"0x29" < opc && opc < !$"0x2d"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Register (decode_reg c1_enc)
    and c2 = begin
      if opc = !$"0x2a" then Register (decode_reg c2_enc) else
      if opc = !$"0x2b" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    SubSeg (r, c1, c2)
  end else
  if !$"0x2c" < opc && opc < !$"0x30"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Const (to_int c1_enc)
    and c2 = begin
      if opc = !$"0x2d" then Register (decode_reg c2_enc) else
      if opc = !$"0x2e" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    SubSeg (r, c1, c2)
  end else
  if !$"0x2f" < opc && opc < !$"0x33"
  then begin
    let (r_enc, payload') = decode_int payload in
    let (c1_enc, c2_enc) = decode_int payload' in
    let r = decode_reg r_enc
    and c1 = Perm (decode_perm c1_enc)
    and c2 = begin
      if opc = !$"0x30" then Register (decode_reg c2_enc) else
      if opc = !$"0x31" then Const (to_int c2_enc) else
      Perm (decode_perm c2_enc)
    end in
    SubSeg (r, c1, c2)
  end else
  (* IsPtr *)
  if opc = !$"0x33"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    IsPtr (r1, r2)
  end else
  (* GetP *)
  if opc = !$"0x34"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    GetP (r1, r2)
  end else
  (* GetB *)
  if opc = !$"0x35"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    GetB (r1, r2)
  end else
  (* GetE *)
  if opc = !$"0x36"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    GetE (r1, r2)
  end else
  (* GetA *)
  if opc = !$"0x37"
  then begin
    let (r1_enc, r2_enc) = decode_int payload in
    let r1 = decode_reg r1_enc
    and r2 = decode_reg r2_enc in
    GetA (r1, r2)
  end else
  (* Fail *)
  if opc = !$"0x38"
  then Fail
  else
  (* Halt *)
  if opc = !$"0x39"
  then Halt
  else raise DecodeException
