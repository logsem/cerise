
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> Big_int_Z.big_int **)

let rec length = function
| [] -> Big_int_Z.zero_big_int
| _ :: l' -> Big_int_Z.succ_big_int (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type signed_int =
| Pos of uint
| Neg of uint

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : signed_int -> signed_int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 -> (match nzhead d0 with
             | Nil -> Pos (D0 Nil)
             | x -> Neg x)

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type signed_int0 =
| Pos0 of uint0
| Neg0 of uint0

(** val nzhead0 : uint0 -> uint0 **)

let rec nzhead0 d = match d with
| D10 d0 -> nzhead0 d0
| _ -> d

(** val unorm0 : uint0 -> uint0 **)

let unorm0 d =
  match nzhead0 d with
  | Nil0 -> D10 Nil0
  | x -> x

(** val norm0 : signed_int0 -> signed_int0 **)

let norm0 = function
| Pos0 d0 -> Pos0 (unorm0 d0)
| Neg0 d0 -> (match nzhead0 d0 with
              | Nil0 -> Pos0 (D10 Nil0)
              | x -> Neg0 x)

(** val revapp0 : uint0 -> uint0 -> uint0 **)

let rec revapp0 d d' =
  match d with
  | Nil0 -> d'
  | D10 d0 -> revapp0 d0 (D10 d')
  | D11 d0 -> revapp0 d0 (D11 d')
  | D12 d0 -> revapp0 d0 (D12 d')
  | D13 d0 -> revapp0 d0 (D13 d')
  | D14 d0 -> revapp0 d0 (D14 d')
  | D15 d0 -> revapp0 d0 (D15 d')
  | D16 d0 -> revapp0 d0 (D16 d')
  | D17 d0 -> revapp0 d0 (D17 d')
  | D18 d0 -> revapp0 d0 (D18 d')
  | D19 d0 -> revapp0 d0 (D19 d')
  | Da d0 -> revapp0 d0 (Da d')
  | Db d0 -> revapp0 d0 (Db d')
  | Dc d0 -> revapp0 d0 (Dc d')
  | Dd d0 -> revapp0 d0 (Dd d')
  | De d0 -> revapp0 d0 (De d')
  | Df d0 -> revapp0 d0 (Df d')

(** val rev0 : uint0 -> uint0 **)

let rev0 d =
  revapp0 d Nil0

module Coq_Little =
 struct
  (** val succ : uint0 -> uint0 **)

  let rec succ = function
  | Nil0 -> D11 Nil0
  | D10 d0 -> D11 d0
  | D11 d0 -> D12 d0
  | D12 d0 -> D13 d0
  | D13 d0 -> D14 d0
  | D14 d0 -> D15 d0
  | D15 d0 -> D16 d0
  | D16 d0 -> D17 d0
  | D17 d0 -> D18 d0
  | D18 d0 -> D19 d0
  | D19 d0 -> Da d0
  | Da d0 -> Db d0
  | Db d0 -> Dc d0
  | Dc d0 -> Dd d0
  | Dd d0 -> De d0
  | De d0 -> Df d0
  | Df d0 -> D10 (succ d0)
 end

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

type signed_int1 =
| IntDecimal of signed_int
| IntHexadecimal of signed_int0

module Coq__1 = struct
 (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)
 let rec add = Big_int_Z.add_big_int
end
include Coq__1

(** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec sub = (fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Nat =
 struct
  type t = Big_int_Z.big_int

  (** val zero : Big_int_Z.big_int **)

  let zero =
    Big_int_Z.zero_big_int

  (** val one : Big_int_Z.big_int **)

  let one =
    Big_int_Z.succ_big_int Big_int_Z.zero_big_int

  (** val two : Big_int_Z.big_int **)

  let two =
    Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ x =
    Big_int_Z.succ_big_int x

  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> m)
      (fun p -> Big_int_Z.succ_big_int (add p m))
      n0

  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double n0 =
    add n0 n0

  (** val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> add m (mul p m))
      n0

  (** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec sub n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb = Big_int_Z.eq_big_int

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec leb = Big_int_Z.le_big_int

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb n0 m =
    leb (Big_int_Z.succ_big_int n0) m

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec max n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> n0)
        (fun m' -> Big_int_Z.succ_big_int (max n' m'))
        m)
      n0

  (** val min : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec min n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> Big_int_Z.zero_big_int)
        (fun m' -> Big_int_Z.succ_big_int (min n' m'))
        m)
      n0

  (** val even : Big_int_Z.big_int -> bool **)

  let rec even n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> true)
      (fun n1 ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> false)
        (fun n' -> even n')
        n1)
      n0

  (** val odd : Big_int_Z.big_int -> bool **)

  let odd n0 =
    negb (even n0)

  (** val pow : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pow n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
      (fun m0 -> mul n0 (pow n0 m0))
      m

  (** val tail_add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec tail_add n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> m)
      (fun n1 -> tail_add n1 (Big_int_Z.succ_big_int m))
      n0

  (** val tail_addmul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec tail_addmul r0 n0 m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> r0)
      (fun n1 -> tail_addmul (tail_add m r0) n1 m)
      n0

  (** val tail_mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let tail_mul n0 m =
    tail_addmul Big_int_Z.zero_big_int n0 m

  (** val of_uint_acc : uint -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 d0 ->
      of_uint_acc d0
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc)
    | D1 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc))
    | D2 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc)))
    | D3 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc))))
    | D4 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc)))))
    | D5 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc))))))
    | D6 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc)))))))
    | D7 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc))))))))
    | D8 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc)))))))))
    | D9 d0 ->
      of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))) acc))))))))))

  (** val of_uint : uint -> Big_int_Z.big_int **)

  let of_uint d =
    of_uint_acc d Big_int_Z.zero_big_int

  (** val of_hex_uint_acc : uint0 -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil0 -> acc
    | D10 d0 ->
      of_hex_uint_acc d0
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)
    | D11 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))
    | D12 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))
    | D13 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))
    | D14 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))
    | D15 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))
    | D16 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))))
    | D17 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))))
    | D18 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))
    | D19 d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))
    | Da d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))
    | Db d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))
    | Dc d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))))
    | Dd d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))))
    | De d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))))))
    | Df d0 ->
      of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
          (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))))))

  (** val of_hex_uint : uint0 -> Big_int_Z.big_int **)

  let of_hex_uint d =
    of_hex_uint_acc d Big_int_Z.zero_big_int

  (** val of_num_uint : uint1 -> Big_int_Z.big_int **)

  let of_num_uint = function
  | UIntDecimal d0 -> of_uint d0
  | UIntHexadecimal d0 -> of_hex_uint d0

  (** val to_little_uint : Big_int_Z.big_int -> uint -> uint **)

  let rec to_little_uint n0 acc =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> acc)
      (fun n1 -> to_little_uint n1 (Little.succ acc))
      n0

  (** val to_uint : Big_int_Z.big_int -> uint **)

  let to_uint n0 =
    rev (to_little_uint n0 (D0 Nil))

  (** val to_little_hex_uint : Big_int_Z.big_int -> uint0 -> uint0 **)

  let rec to_little_hex_uint n0 acc =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> acc)
      (fun n1 -> to_little_hex_uint n1 (Coq_Little.succ acc))
      n0

  (** val to_hex_uint : Big_int_Z.big_int -> uint0 **)

  let to_hex_uint n0 =
    rev0 (to_little_hex_uint n0 (D10 Nil0))

  (** val to_num_uint : Big_int_Z.big_int -> uint1 **)

  let to_num_uint n0 =
    UIntDecimal (to_uint n0)

  (** val to_num_hex_uint : Big_int_Z.big_int -> uint1 **)

  let to_num_hex_uint n0 =
    UIntHexadecimal (to_hex_uint n0)

  (** val of_int : signed_int -> Big_int_Z.big_int option **)

  let of_int d =
    match norm d with
    | Pos u -> Some (of_uint u)
    | Neg _ -> None

  (** val of_hex_int : signed_int0 -> Big_int_Z.big_int option **)

  let of_hex_int d =
    match norm0 d with
    | Pos0 u -> Some (of_hex_uint u)
    | Neg0 _ -> None

  (** val of_num_int : signed_int1 -> Big_int_Z.big_int option **)

  let of_num_int = function
  | IntDecimal d0 -> of_int d0
  | IntHexadecimal d0 -> of_hex_int d0

  (** val to_int : Big_int_Z.big_int -> signed_int **)

  let to_int n0 =
    Pos (to_uint n0)

  (** val to_hex_int : Big_int_Z.big_int -> signed_int0 **)

  let to_hex_int n0 =
    Pos0 (to_hex_uint n0)

  (** val to_num_int : Big_int_Z.big_int -> signed_int1 **)

  let to_num_int n0 =
    IntDecimal (to_int n0)

  (** val divmod :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int * Big_int_Z.big_int **)

  let rec divmod x y q u =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> divmod x' y (Big_int_Z.succ_big_int q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div x y =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' Big_int_Z.zero_big_int y'))
      y

  (** val modulo : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let modulo x y =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' Big_int_Z.zero_big_int y')))
      y

  (** val gcd : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec gcd a b =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (Big_int_Z.succ_big_int a')) (Big_int_Z.succ_big_int a'))
      a

  (** val square : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let square n0 =
    mul n0 n0

  (** val sqrt_iter :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int **)

  let rec sqrt_iter k p q r0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ ->
        sqrt_iter k' (Big_int_Z.succ_big_int p) (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int q))
          (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int q)))
        (fun r' -> sqrt_iter k' p q r')
        r0)
      k

  (** val sqrt : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sqrt n0 =
    sqrt_iter n0 Big_int_Z.zero_big_int Big_int_Z.zero_big_int Big_int_Z.zero_big_int

  (** val log2_iter :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int **)

  let rec log2_iter k p q r0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> log2_iter k' (Big_int_Z.succ_big_int p) (Big_int_Z.succ_big_int q) q)
        (fun r' -> log2_iter k' p (Big_int_Z.succ_big_int q) r')
        r0)
      k

  (** val log2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let log2 n0 =
    log2_iter (pred n0) Big_int_Z.zero_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
      Big_int_Z.zero_big_int

  (** val iter : Big_int_Z.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> x)
      (fun n1 -> f (iter n1 f x))
      n0

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec div2 = (fun n -> Big_int_Z.div_big_int n (Big_int_Z.big_int_of_int 2))

  (** val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec testbit a n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> odd a)
      (fun n1 -> testbit (div2 a) n1)
      n0

  (** val shiftl : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec shiftl a n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> a)
      (fun n1 -> double (shiftl a n1))
      n0

  (** val shiftr : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec shiftr a n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> a)
      (fun n1 -> div2 (shiftr a n1))
      n0

  (** val bitwise :
      (bool -> bool -> bool) -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
      Big_int_Z.big_int **)

  let rec bitwise op n0 a b =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n' ->
      add
        (if op (odd a) (odd b)
         then Big_int_Z.succ_big_int Big_int_Z.zero_big_int
         else Big_int_Z.zero_big_int)
        (mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))
          (bitwise op n' (div2 a) (div2 b))))
      n0

  (** val coq_land : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_land a b =
    bitwise (&&) a a b

  (** val coq_lor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lor a b =
    bitwise (||) (max a b) a b

  (** val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let ldiff a b =
    bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

  (** val coq_lxor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion : 'a1 -> (Big_int_Z.big_int -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 **)

  let rec recursion x f0 n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> x)
      (fun n1 -> f0 n1 (recursion x f0 n1))
      n0

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eq_dec = Big_int_Z.eq_big_int

  (** val leb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int -> Big_int_Z.big_int -> __ -> 'a1
        -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int -> Big_int_Z.big_int -> __ -> 'a1
        -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int -> Big_int_Z.big_int -> __ -> 'a1
        -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int -> Big_int_Z.big_int -> __ -> 'a1
        -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sqrt_up a =
    match compare Big_int_Z.zero_big_int a with
    | Lt -> Big_int_Z.succ_big_int (sqrt (pred a))
    | _ -> Big_int_Z.zero_big_int

  (** val log2_up : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let log2_up a =
    match compare (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) a with
    | Lt -> Big_int_Z.succ_big_int (log2 (pred a))
    | _ -> Big_int_Z.zero_big_int

  module Private_NZDiv =
   struct
   end

  (** val lcm : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> Big_int_Z.big_int **)

  let b2n = function
  | true -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int
  | false -> Big_int_Z.zero_big_int

  (** val setbit : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let setbit a n0 =
    coq_lor a (shiftl (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) n0)

  (** val clearbit : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let clearbit a n0 =
    ldiff a (shiftl (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) n0)

  (** val ones : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let ones n0 =
    pred (shiftl (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) n0)

  (** val lnot : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let lnot a n0 =
    coq_lxor a (ones n0)

  (** val coq_Even_Odd_dec : Big_int_Z.big_int -> bool **)

  let rec coq_Even_Odd_dec n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> true)
      (fun n1 -> if coq_Even_Odd_dec n1 then false else true)
      n0

  type coq_EvenT = Big_int_Z.big_int

  type coq_OddT = Big_int_Z.big_int

  (** val coq_EvenT_0 : coq_EvenT **)

  let coq_EvenT_0 =
    Big_int_Z.zero_big_int

  (** val coq_EvenT_2 : Big_int_Z.big_int -> coq_EvenT -> coq_EvenT **)

  let coq_EvenT_2 _ h0 =
    Big_int_Z.succ_big_int h0

  (** val coq_OddT_1 : coq_OddT **)

  let coq_OddT_1 =
    Big_int_Z.zero_big_int

  (** val coq_OddT_2 : Big_int_Z.big_int -> coq_OddT -> coq_OddT **)

  let coq_OddT_2 _ h0 =
    Big_int_Z.succ_big_int h0

  (** val coq_EvenT_S_OddT : Big_int_Z.big_int -> coq_EvenT -> coq_OddT **)

  let coq_EvenT_S_OddT _ h =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> assert false (* absurd case *))
      (fun n0 -> n0)
      h

  (** val coq_OddT_S_EvenT : Big_int_Z.big_int -> coq_OddT -> coq_EvenT **)

  let coq_OddT_S_EvenT _ h =
    h

  (** val even_EvenT : Big_int_Z.big_int -> coq_EvenT **)

  let rec even_EvenT n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> coq_EvenT_0)
      (fun n1 ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> assert false (* absurd case *))
        (fun n2 -> let he = even_EvenT n2 in coq_EvenT_2 n2 he)
        n1)
      n0

  (** val odd_OddT : Big_int_Z.big_int -> coq_OddT **)

  let rec odd_OddT n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> assert false (* absurd case *))
      (fun n1 ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> coq_OddT_1)
        (fun n2 -> let he = odd_OddT n2 in coq_OddT_2 n2 he)
        n1)
      n0

  (** val coq_Even_EvenT : Big_int_Z.big_int -> coq_EvenT **)

  let coq_Even_EvenT =
    even_EvenT

  (** val coq_Odd_OddT : Big_int_Z.big_int -> coq_OddT **)

  let coq_Odd_OddT =
    odd_OddT

  (** val coq_EvenT_OddT_dec : Big_int_Z.big_int -> (coq_EvenT, coq_OddT) sum **)

  let coq_EvenT_OddT_dec n0 =
    if even n0 then Inl (even_EvenT n0) else Inr (odd_OddT n0)

  (** val coq_OddT_EvenT_rect :
      (Big_int_Z.big_int -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (Big_int_Z.big_int -> coq_OddT -> 'a1
      -> 'a2) -> Big_int_Z.big_int -> coq_OddT -> 'a1 **)

  let rec coq_OddT_EvenT_rect hQP hQ0 hPQ n0 h =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> assert false (* absurd case *))
        (fun _ -> assert false (* absurd case *))
        h)
      (fun n1 ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> hQP Big_int_Z.zero_big_int coq_EvenT_0 hQ0)
        (fun n2 ->
        let hES = coq_OddT_S_EvenT (Big_int_Z.succ_big_int n2) h in
        let hO = coq_EvenT_S_OddT n2 hES in
        hQP (Big_int_Z.succ_big_int n2) hES (hPQ n2 hO (coq_OddT_EvenT_rect hQP hQ0 hPQ n2 hO)))
        n1)
      n0

  (** val coq_EvenT_OddT_rect :
      (Big_int_Z.big_int -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (Big_int_Z.big_int -> coq_OddT -> 'a1
      -> 'a2) -> Big_int_Z.big_int -> coq_EvenT -> 'a2 **)

  let coq_EvenT_OddT_rect hQP hQ0 hPQ n0 hES =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> hQ0)
      (fun n1 ->
      let hO = coq_EvenT_S_OddT n1 hES in hPQ n1 hO (coq_OddT_EvenT_rect hQP hQ0 hPQ n1 hO))
      n0
 end

module Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ = Big_int_Z.succ_big_int

  (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add = Big_int_Z.add_big_int

  (** val add_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun _ -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun q -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (succ q))
        (fun _ -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred = (fun n -> Big_int_Z.max_big_int Big_int_Z.unit_big_int
  (Big_int_Z.pred_big_int n))

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_nat x =
    iter_op Coq__1.add x (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

  (** val of_succ_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun x -> succ (of_succ_nat x))
      n0

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module N =
 struct
  (** val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let to_nat a =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_nat n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n' -> (Pos.of_succ_nat n'))
      n0

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec n0 m =
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun p ->
      (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec p p0)
        m)
      n0
 end

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x :: _ -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 -> if eq_dec0 y a then list_eq_dec eq_dec0 l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val skipn : Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

module Z =
 struct
  (** val zero : Big_int_Z.big_int **)

  let zero =
    Big_int_Z.zero_big_int

  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 p))
      x

  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      (fun p -> Big_int_Z.minus_big_int (Pos.pred_double p))
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      (fun p -> (Pos.pred_double p))
      (fun p -> Big_int_Z.minus_big_int
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val pos_sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 q))
        (fun q -> Big_int_Z.minus_big_int (Pos.pred_double q))
        (fun _ -> Big_int_Z.zero_big_int)
        y)
      x

  (** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp = Big_int_Z.minus_big_int

  (** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = Big_int_Z.sub_big_int

  (** val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let of_nat n0 =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun n1 -> (Pos.of_succ_nat n1))
      n0
 end

module Coq_Nat = Nat

type decision = bool

(** val decide : decision -> bool **)

let decide decision0 =
  decision0

type ('a, 'b) relDecision = 'a -> 'b -> decision

(** val decide_rel : ('a1, 'a2) relDecision -> 'a1 -> 'a2 -> decision **)

let decide_rel relDecision0 =
  relDecision0

type 'a empty = 'a

(** val empty0 : 'a1 empty -> 'a1 **)

let empty0 empty1 =
  empty1

type 'm mRet = __ -> __ -> 'm

(** val mret : 'a1 mRet -> 'a2 -> 'a1 **)

let mret mRet0 x =
  Obj.magic mRet0 __ x

type 'm mBind = __ -> __ -> (__ -> 'm) -> 'm -> 'm

(** val mbind : 'a1 mBind -> ('a2 -> 'a1) -> 'a1 -> 'a1 **)

let mbind mBind0 x x0 =
  Obj.magic mBind0 __ __ x x0

type 'm fMap = __ -> __ -> (__ -> __) -> 'm -> 'm

(** val fmap : 'a1 fMap -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let fmap fMap0 x x0 =
  Obj.magic fMap0 __ __ x x0

type ('k, 'a, 'm) lookup = 'k -> 'm -> 'a option

(** val lookup0 : ('a1, 'a2, 'a3) lookup -> 'a1 -> 'a3 -> 'a2 option **)

let lookup0 lookup1 =
  lookup1

type ('k, 'a, 'm) insert = 'k -> 'a -> 'm -> 'm

(** val insert0 : ('a1, 'a2, 'a3) insert -> 'a1 -> 'a2 -> 'a3 -> 'a3 **)

let insert0 insert1 =
  insert1

type ('k, 'a, 'm) partialAlter = ('a option -> 'a option) -> 'k -> 'm -> 'm

(** val partial_alter :
    ('a1, 'a2, 'a3) partialAlter -> ('a2 option -> 'a2 option) -> 'a1 -> 'a3 -> 'a3 **)

let partial_alter partialAlter0 =
  partialAlter0

(** val option_ret : __ -> __ option **)

let option_ret x =
  Some x

(** val option_bind : (__ -> __ option) -> __ option -> __ option **)

let option_bind f = function
| Some x -> f x
| None -> None

(** val option_fmap : (__ -> __) -> __ option -> __ option **)

let option_fmap =
  option_map

module Coq0_Nat =
 struct
  (** val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) relDecision **)

  let eq_dec =
    Nat.eq_dec
 end

module Coq_Pos =
 struct
  (** val eq_dec : (Big_int_Z.big_int, Big_int_Z.big_int) relDecision **)

  let eq_dec =
    Pos.eq_dec

  (** val app : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec app p1 p2 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p3 -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (app p1 p3))
      (fun p3 -> Big_int_Z.mult_int_big_int 2 (app p1 p3))
      (fun _ -> p1)
      p2

  (** val reverse_go : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec reverse_go p1 p2 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p3 ->
      reverse_go ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p1) p3)
      (fun p3 -> reverse_go (Big_int_Z.mult_int_big_int 2 p1) p3)
      (fun _ -> p1)
      p2

  (** val reverse : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let reverse =
    reverse_go Big_int_Z.unit_big_int

  (** val dup : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec dup p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p' -> (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) (dup p')))
      (fun p' -> Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2 (dup p')))
      (fun _ -> Big_int_Z.unit_big_int)
      p
 end

(** val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec foldl f a = function
| [] -> a
| x :: l0 -> foldl f (f a x) l0

(** val list_fmap : (__ -> __) -> __ list -> __ list **)

let rec list_fmap f = function
| [] -> []
| x :: l0 -> (f x) :: (list_fmap f l0)

(** val mapM : 'a1 mBind -> 'a1 mRet -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let rec mapM h h0 f = function
| [] -> mret h0 []
| x :: l0 -> mbind h (fun y -> mbind h (fun k -> mret h0 (y :: k)) (mapM h h0 f l0)) (f x)

(** val elem_of_list_dec : ('a1, 'a1) relDecision -> ('a1, 'a1 list) relDecision **)

let rec elem_of_list_dec dec x = function
| [] -> false
| y :: l0 -> if decide (decide_rel dec x y) then true else elem_of_list_dec dec x l0

(** val list_difference : ('a1, 'a1) relDecision -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec list_difference dec l k =
  match l with
  | [] -> []
  | x :: l0 ->
    if decide_rel (elem_of_list_dec dec) x k
    then list_difference dec l0 k
    else x :: (list_difference dec l0 k)

(** val positives_flatten_go : Big_int_Z.big_int list -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec positives_flatten_go xs acc =
  match xs with
  | [] -> acc
  | x :: xs0 ->
    positives_flatten_go xs0
      (Coq_Pos.app (Big_int_Z.mult_int_big_int 2
        ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) acc))
        (Coq_Pos.reverse (Coq_Pos.dup x)))

(** val positives_flatten : Big_int_Z.big_int list -> Big_int_Z.big_int **)

let positives_flatten xs =
  positives_flatten_go xs Big_int_Z.unit_big_int

(** val positives_unflatten_go :
    Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int -> Big_int_Z.big_int list option **)

let rec positives_unflatten_go p acc_xs acc_elm =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun p0 ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p' ->
      positives_unflatten_go p' acc_xs
        ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) acc_elm))
      (fun _ -> None)
      (fun _ -> None)
      p0)
    (fun p0 ->
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p' -> positives_unflatten_go p' (acc_elm :: acc_xs) Big_int_Z.unit_big_int)
      (fun p' -> positives_unflatten_go p' acc_xs (Big_int_Z.mult_int_big_int 2 acc_elm))
      (fun _ -> None)
      p0)
    (fun _ -> Some acc_xs)
    p

(** val positives_unflatten : Big_int_Z.big_int -> Big_int_Z.big_int list option **)

let positives_unflatten p =
  positives_unflatten_go p [] Big_int_Z.unit_big_int

(** val list_eq_dec0 : ('a1, 'a1) relDecision -> ('a1 list, 'a1 list) relDecision **)

let list_eq_dec0 =
  list_eq_dec

type 'a countable = { encode : ('a -> Big_int_Z.big_int); decode : (Big_int_Z.big_int -> 'a option) }

(** val list_countable : ('a1, 'a1) relDecision -> 'a1 countable -> 'a1 list countable **)

let list_countable _ h =
  { encode = (fun xs ->
    positives_flatten (fmap (Obj.magic (fun _ _ -> list_fmap)) h.encode (Obj.magic xs))); decode =
    (fun p ->
    mbind (Obj.magic (fun _ _ -> option_bind)) (fun positives ->
      mapM (Obj.magic (fun _ _ -> option_bind)) (Obj.magic (fun _ -> option_ret)) (Obj.magic h).decode
        positives) (Obj.magic positives_unflatten p)) }

(** val n_countable : Big_int_Z.big_int countable **)

let n_countable =
  { encode = (fun x ->
    (fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p -> Pos.succ p)
      x); decode = (fun p ->
    if decide (decide_rel Coq_Pos.eq_dec p Big_int_Z.unit_big_int)
    then Some Big_int_Z.zero_big_int
    else Some (Pos.pred p)) }

(** val nat_countable : Big_int_Z.big_int countable **)

let nat_countable =
  { encode = (fun x -> n_countable.encode (N.of_nat x)); decode = (fun p ->
    fmap (Obj.magic (fun _ _ -> option_fmap)) N.to_nat ((Obj.magic n_countable).decode p)) }

(** val map_insert : ('a1, 'a2, 'a3) partialAlter -> ('a1, 'a2, 'a3) insert **)

let map_insert h i x =
  partial_alter h (fun _ -> Some x) i

type 'a pmap_raw =
| PLeaf
| PNode of 'a option * 'a pmap_raw * 'a pmap_raw

(** val pNode' : 'a1 option -> 'a1 pmap_raw -> 'a1 pmap_raw -> 'a1 pmap_raw **)

let pNode' o l r0 =
  match l with
  | PLeaf ->
    (match o with
     | Some _ -> PNode (o, l, r0)
     | None -> (match r0 with
                | PLeaf -> PLeaf
                | PNode (_, _, _) -> PNode (o, l, r0)))
  | PNode (_, _, _) -> PNode (o, l, r0)

(** val pempty_raw : 'a1 pmap_raw empty **)

let pempty_raw =
  PLeaf

(** val plookup_raw : (Big_int_Z.big_int, 'a1, 'a1 pmap_raw) lookup **)

let rec plookup_raw i = function
| PLeaf -> None
| PNode (o, l, r0) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> lookup0 plookup_raw i0 r0)
     (fun i0 -> lookup0 plookup_raw i0 l)
     (fun _ -> o)
     i)

(** val psingleton_raw : Big_int_Z.big_int -> 'a1 -> 'a1 pmap_raw **)

let rec psingleton_raw i x =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun i0 -> PNode (None, PLeaf, (psingleton_raw i0 x)))
    (fun i0 -> PNode (None, (psingleton_raw i0 x), PLeaf))
    (fun _ -> PNode ((Some x), PLeaf, PLeaf))
    i

(** val ppartial_alter_raw :
    ('a1 option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 pmap_raw -> 'a1 pmap_raw **)

let rec ppartial_alter_raw f i = function
| PLeaf -> (match f None with
            | Some x -> psingleton_raw i x
            | None -> PLeaf)
| PNode (o, l, r0) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> pNode' o l (ppartial_alter_raw f i0 r0))
     (fun i0 -> pNode' o (ppartial_alter_raw f i0 l) r0)
     (fun _ -> pNode' (f o) l r0)
     i)

type 'a pmap = 'a pmap_raw
  (* singleton inductive, whose constructor was PMap *)

(** val pmap_car : 'a1 pmap -> 'a1 pmap_raw **)

let pmap_car p =
  p

(** val pempty : 'a1 pmap empty **)

let pempty =
  empty0 pempty_raw

(** val plookup : (Big_int_Z.big_int, 'a1, 'a1 pmap) lookup **)

let plookup i m =
  lookup0 plookup_raw i (pmap_car m)

(** val ppartial_alter : (Big_int_Z.big_int, 'a1, 'a1 pmap) partialAlter **)

let ppartial_alter f i m =
  partial_alter ppartial_alter_raw f i m

type ('k, 'a) gmap = 'a pmap
  (* singleton inductive, whose constructor was GMap *)

(** val gmap_lookup : ('a1, 'a1) relDecision -> 'a1 countable -> ('a1, 'a2, ('a1, 'a2) gmap) lookup **)

let gmap_lookup _ h i pat =
  lookup0 plookup (h.encode i) pat

(** val gmap_empty : ('a1, 'a1) relDecision -> 'a1 countable -> ('a1, 'a2) gmap empty **)

let gmap_empty _ _ =
  empty0 pempty

(** val gmap_partial_alter :
    ('a1, 'a1) relDecision -> 'a1 countable -> ('a1, 'a2, ('a1, 'a2) gmap) partialAlter **)

let gmap_partial_alter _ h f i pat =
  partial_alter ppartial_alter f (h.encode i) pat

type immediate = Big_int_Z.big_int

type handle = { base : Big_int_Z.big_int; offset : Big_int_Z.big_int; bound : Big_int_Z.big_int;
                valid : bool; id : Big_int_Z.big_int }

type value =
| Val_int of Big_int_Z.big_int
| Val_handle of handle

type value_type =
| T_int
| T_handle

type binop =
| BOI_add
| BOI_sub

type result_type = value_type list

type function_type =
| Tf of result_type * result_type

type basic_instruction =
| I_unreachable
| I_nop
| I_drop
| I_block of function_type * basic_instruction list
| I_loop of function_type * basic_instruction list
| I_if of function_type * basic_instruction list * basic_instruction list
| I_br of immediate
| I_br_if of immediate
| I_return
| I_call of immediate
| I_get_local of immediate
| I_set_local of immediate
| I_tee_local of immediate
| I_get_global of immediate
| I_set_global of immediate
| I_load of value_type
| I_store of value_type
| I_segload of value_type
| I_segstore of value_type
| I_slice
| I_segalloc
| I_handleadd
| I_segfree
| I_const of value
| I_binop of value_type * binop

type regName =
| PC
| STK
| R of Big_int_Z.big_int

(** val all_registers : regName list **)

let all_registers =
  (R Big_int_Z.zero_big_int) :: ((R (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))))))))))))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))))))))))))))))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))) :: ((R (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))))))))))))))))))))) :: ((R
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))) :: (PC :: []))))))))))))))))))))))))))))))))

(** val reg_eq_dec : (regName, regName) relDecision **)

let reg_eq_dec r1 r2 =
  match r1 with
  | PC -> (match r2 with
           | PC -> true
           | _ -> false)
  | STK -> (match r2 with
            | STK -> true
            | _ -> false)
  | R n0 -> (match r2 with
             | R n1 -> Nat.eq_dec n0 n1
             | _ -> false)

(** val r : Big_int_Z.big_int -> (Big_int_Z.big_int, regName) sum **)

let r n0 =
  Inr (R n0)

type perm =
| O
| RO
| RW
| RWL
| RX
| E
| RWX
| RWLX
| URW
| URWL
| URWX
| URWLX

type locality =
| Global
| Local
| Directed

type instr =
| Jmp of regName
| Jnz of regName * regName
| Mov of regName * (Big_int_Z.big_int, regName) sum
| Load of regName * regName
| Store of regName * (Big_int_Z.big_int, regName) sum
| Lt0 of regName * (Big_int_Z.big_int, regName) sum * (Big_int_Z.big_int, regName) sum
| Add of regName * (Big_int_Z.big_int, regName) sum * (Big_int_Z.big_int, regName) sum
| Sub of regName * (Big_int_Z.big_int, regName) sum * (Big_int_Z.big_int, regName) sum
| Lea of regName * (Big_int_Z.big_int, regName) sum
| Restrict of regName * (Big_int_Z.big_int, regName) sum
| Subseg of regName * (Big_int_Z.big_int, regName) sum * (Big_int_Z.big_int, regName) sum
| IsPtr of regName * regName
| GetL of regName * regName
| GetP of regName * regName
| GetB of regName * regName
| GetE of regName * regName
| GetA of regName * regName
| Fail
| Halt
| Nop
| LoadU of regName * regName * (Big_int_Z.big_int, regName) sum
| StoreU of regName * (Big_int_Z.big_int, regName) sum * (Big_int_Z.big_int, regName) sum
| PromoteU of regName

type machineParameters = { decodeInstr : (Big_int_Z.big_int -> instr);
                           encodeInstr : (instr -> Big_int_Z.big_int);
                           encodePerm : (perm -> Big_int_Z.big_int);
                           encodeLoc : (locality -> Big_int_Z.big_int);
                           decodePermPair : (Big_int_Z.big_int -> perm * locality);
                           encodePermPair : ((perm * locality) -> Big_int_Z.big_int) }

(** val r_stk : regName **)

let r_stk =
  STK

(** val rclear_instrs : regName list -> instr list **)

let rclear_instrs r0 =
  map (fun r_i -> Mov (r_i, (Inl Big_int_Z.zero_big_int))) r0

(** val push_instrs : (Big_int_Z.big_int, regName) sum list -> instr list **)

let push_instrs _UU03c1_s =
  map (fun _UU03c1_ -> StoreU (r_stk, (Inl Big_int_Z.zero_big_int), _UU03c1_)) _UU03c1_s

(** val pop_instrs : machineParameters -> regName -> Big_int_Z.big_int list **)

let pop_instrs h r0 =
  (h.encodeInstr (LoadU (r0, r_stk, (Inl (Big_int_Z.minus_big_int Big_int_Z.unit_big_int))))) :: (
    (h.encodeInstr (Lea (r_stk, (Inl (Big_int_Z.minus_big_int Big_int_Z.unit_big_int))))) :: [])

(** val push_env_instrs : instr list **)

let push_env_instrs =
  push_instrs (map (fun r0 -> Inr r0) (list_difference reg_eq_dec all_registers (PC :: (r_stk :: []))))

(** val pop_env_instrs : machineParameters -> Big_int_Z.big_int list **)

let pop_env_instrs h =
  foldl (fun b r0 -> app (pop_instrs h r0) b) []
    (list_difference reg_eq_dec all_registers (PC :: (r_stk :: [])))

(** val call_instrs_prologue : machineParameters -> regName list -> instr list **)

let call_instrs_prologue h rargs =
  app (push_instrs ((Inl Big_int_Z.zero_big_int) :: []))
    (app push_env_instrs
      (app (push_instrs ((Inr r_stk) :: []))
        (app
          (push_instrs
            (app ((Inl
              (h.encodeInstr (Mov ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))), (Inr PC))))) :: ((Inl
              (h.encodeInstr (Lea ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))), (Inl (Big_int_Z.minus_big_int
                Big_int_Z.unit_big_int)))))) :: ((Inl
              (h.encodeInstr (Load (r_stk, (R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
                Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))) :: [])))
              (app (map (fun x -> Inl x) (pop_env_instrs h)) ((Inl
                (h.encodeInstr (LoadU (PC, r_stk, (Inl (Big_int_Z.minus_big_int
                  Big_int_Z.unit_big_int)))))) :: []))))
          (app ((Mov ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))), (Inr
            PC))) :: ((Lea ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))), (Inl
            (Z.add ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
              ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
              (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int))))) (Z.of_nat (length rargs)))))) :: []))
            ((StoreU (r_stk, (Inl (Big_int_Z.minus_big_int
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
            ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
            Big_int_Z.unit_big_int)))))))), (Inr (R (Big_int_Z.succ_big_int
            Big_int_Z.zero_big_int))))) :: [])))))

(** val call_instrs : machineParameters -> regName -> regName list -> instr list **)

let call_instrs h r0 rargs =
  app (call_instrs_prologue h rargs)
    (app ((Mov ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      Big_int_Z.zero_big_int))))))))))))))))))))))))))))))), (Inr r_stk))) :: ((PromoteU (R
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))) :: ((Lea ((R (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))))))))))))))))))))), (Inl
      (Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2 (Big_int_Z.mult_int_big_int 2
      (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)))))))))) :: ((Restrict ((R
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      Big_int_Z.zero_big_int))))))))))))))))))))))))))))))), (Inl
      (h.encodePermPair (E, Directed))))) :: []))))
      (app ((GetA ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))),
        r_stk)) :: ((GetE ((R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))))))))))))))))), r_stk)) :: ((Subseg (r_stk, (Inr (R
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))), (Inr (R
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))) :: [])))
        (app
          (push_instrs ((Inr (R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
            (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))) :: []))
          (app (push_instrs (map (fun x -> Inr x) rargs))
            (app
              (rclear_instrs (list_difference reg_eq_dec all_registers (PC :: (r0 :: (r_stk :: [])))))
              ((Jmp r0) :: []))))))

type labeled_instr =
| Label of Big_int_Z.big_int list
| BInstr of instr
| Br_Jmp of Big_int_Z.big_int list * Big_int_Z.big_int
| Br_Jnz of Big_int_Z.big_int list * Big_int_Z.big_int

(** val instrs : instr list -> labeled_instr list **)

let instrs li =
  map (fun i -> BInstr i) li

(** val r_stk0 : regName **)

let r_stk0 =
  STK

(** val r_mem : regName **)

let r_mem =
  R Big_int_Z.zero_big_int

(** val r_fun : regName **)

let r_fun =
  R (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val r_glob : regName **)

let r_glob =
  R (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))

(** val compile_value : value -> (Big_int_Z.big_int, regName) sum **)

let compile_value = function
| Val_int n0 -> Inl (Z.of_nat n0)
| Val_handle _ -> Inl (Z.of_nat Big_int_Z.zero_big_int)

type compilation_state = { reg : Big_int_Z.big_int; lbl : Big_int_Z.big_int list;
                           depth : Big_int_Z.big_int }

(** val new_state :
    Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int -> compilation_state **)

let new_state reg0 lbl0 depth0 =
  { reg = reg0; lbl = lbl0; depth = depth0 }

(** val add_reg : compilation_state -> Big_int_Z.big_int -> compilation_state **)

let add_reg s n0 =
  new_state (add s.reg n0) s.lbl s.depth

(** val sub_reg : compilation_state -> Big_int_Z.big_int -> compilation_state **)

let sub_reg s n0 =
  new_state (sub s.reg n0) s.lbl s.depth

(** val new_lbl : compilation_state -> compilation_state **)

let new_lbl s =
  let label = s.lbl in
  let new_label =
    if Coq_Nat.eqb s.depth (length label)
    then (add (hd Big_int_Z.zero_big_int label) (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) :: 
           (tl label)
    else (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) :: label
  in
  new_state s.reg new_label s.depth

(** val sync_lbl : compilation_state -> compilation_state **)

let sync_lbl s =
  let new_label = skipn (sub (length s.lbl) s.depth) s.lbl in new_state s.reg new_label s.depth

(** val next_depth : compilation_state -> compilation_state **)

let next_depth s =
  new_state s.reg s.lbl (add s.depth (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))

type cfg = labeled_instr list * compilation_state

(** val compile_basic_instr : machineParameters -> basic_instruction -> compilation_state -> cfg **)

let rec compile_basic_instr h i s =
  let nreg = s.reg in
  (match i with
   | I_nop -> ((instrs (Nop :: [])), s)
   | I_drop -> ([], (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_block (_, body) ->
     let (compiled_body, sC) =
       foldl (fun acc i0 ->
         let (instrs_acc, s_acc) = acc in
         let (instrs_comp, s_comp) = compile_basic_instr h i0 s_acc in
         ((app instrs_acc instrs_comp), s_comp)) ([], (new_lbl (next_depth s))) body
     in
     ((app compiled_body ((Label (new_lbl (next_depth s)).lbl) :: [])),
     (new_state s.reg (sync_lbl sC).lbl s.depth))
   | I_loop (_, body) ->
     let (compiled_body, sC) =
       foldl (fun acc i0 ->
         let (instrs_acc, s_acc) = acc in
         let (instrs_comp, s_comp) = compile_basic_instr h i0 s_acc in
         ((app instrs_acc instrs_comp), s_comp)) ([], (new_lbl (next_depth s))) body
     in
     (((Label (new_lbl (next_depth s)).lbl) :: compiled_body),
     (new_state s.reg (sync_lbl sC).lbl s.depth))
   | I_br n0 -> (((Br_Jmp ((skipn n0 (sync_lbl s).lbl), nreg)) :: []), s)
   | I_br_if n0 ->
     (((Br_Jnz ((skipn n0 (sync_lbl s).lbl), nreg)) :: []),
       (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_return ->
     let tmp2 = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let jaddr = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((GetB ((R nreg), r_stk0)) :: ((GetA ((R tmp2), r_stk0)) :: ((Sub ((R nreg), (r nreg),
        (r tmp2))) :: ((LoadU ((R jaddr), r_stk0, (r tmp2))) :: ((Jmp (R jaddr)) :: [])))))), s)
   | I_call i0 ->
     ((app (instrs ((Lea (r_fun, (Inl (Z.of_nat i0)))) :: ((Load ((R nreg), r_fun)) :: [])))
        (instrs (call_instrs h (R nreg) []))), s)
   | I_get_local i0 ->
     let off = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((GetB ((R nreg), r_stk0)) :: ((Add ((R nreg), (r nreg), (Inl (Z.of_nat i0)))) :: ((GetA
        ((R off), r_stk0)) :: ((Sub ((R off), (r nreg), (r off))) :: ((LoadU ((R nreg), r_stk0,
        (r off))) :: [])))))), (add_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_set_local i0 ->
     let v = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let off = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((GetB ((R nreg), r_stk0)) :: ((Add ((R nreg), (r nreg), (Inl (Z.of_nat i0)))) :: ((GetA
        ((R off), r_stk0)) :: ((Sub ((R off), (r nreg), (r off))) :: ((StoreU (r_stk0, (r off),
        (r v))) :: [])))))), (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_tee_local i0 ->
     let v = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let off = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((GetB ((R nreg), r_stk0)) :: ((Add ((R nreg), (r nreg), (Inl (Z.of_nat i0)))) :: ((GetA
        ((R off), r_stk0)) :: ((Sub ((R off), (r nreg), (r off))) :: ((StoreU (r_stk0, (r off),
        (r v))) :: ((Mov ((R nreg), (r v))) :: []))))))), s)
   | I_get_global i0 ->
     ((instrs ((Lea (r_glob, (Inl (Z.of_nat i0)))) :: ((Load ((R nreg), r_glob)) :: ((Lea (r_glob,
        (Inl (Z.opp (Z.of_nat i0))))) :: [])))),
       (add_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_set_global i0 ->
     let v = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((Lea (r_glob, (Inl (Z.of_nat i0)))) :: ((Store (r_glob, (r v))) :: ((Lea (r_glob, (Inl
        (Z.opp (Z.of_nat i0))))) :: [])))),
     (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_load _ ->
     let a = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let res = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((Lea (r_mem, (r a))) :: ((Load ((R nreg), r_mem)) :: ((Sub ((R a), (Inl Z.zero),
        (r a))) :: ((Lea (r_mem, (r a))) :: ((Mov ((R res), (r nreg))) :: [])))))), s)
   | I_store _ ->
     let v = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let a = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     ((instrs ((Lea (r_mem, (r a))) :: ((Store (r_mem, (r v))) :: ((Sub ((R a), (Inl Z.zero),
        (r a))) :: ((Lea (r_mem, (r a))) :: []))))),
     (sub_reg s (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))
   | I_segload _ ->
     let h0 = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let res = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((Load ((R res), (R h0))) :: [])), s)
   | I_segstore _ ->
     let h0 = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     let v = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((Store ((R h0), (r v))) :: [])),
     (sub_reg s (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))
   | I_slice ->
     let h0 =
       sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
         Big_int_Z.zero_big_int)))
     in
     let o1 = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     let o2 = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let tmp2 = add nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let res =
       sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
         Big_int_Z.zero_big_int)))
     in
     ((instrs ((GetB ((R nreg), (R h0))) :: ((Add ((R o1), (r o1), (r nreg))) :: ((GetE ((R tmp2), (R
        h0))) :: ((Sub ((R o2), (r tmp2), (r o2))) :: ((Subseg ((R h0), (r o1), (r o2))) :: ((Mov ((R
        res), (r h0))) :: []))))))),
     (sub_reg s (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))
   | I_handleadd ->
     let h0 = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     let off = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     ((instrs ((Lea ((R h0), (r off))) :: [])),
     (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_const v ->
     ((instrs ((Mov ((R nreg), (compile_value v))) :: [])),
       (add_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | I_binop (_, b) ->
     let v1 = sub nreg (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
     let v2 = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     let res = sub nreg (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)) in
     ((instrs
        (match b with
         | BOI_add -> (Add ((R res), (r v1), (r v2))) :: []
         | BOI_sub -> (Sub ((R res), (r v2), (r v1))) :: [])),
     (sub_reg s (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
   | _ -> ((instrs (Fail :: [])), s))

(** val labeled_compile :
    machineParameters -> basic_instruction list -> Big_int_Z.big_int -> Big_int_Z.big_int list ->
    Big_int_Z.big_int -> labeled_instr list **)

let rec labeled_compile h il nreg nlbl ndepth =
  match il with
  | [] -> []
  | i :: il' ->
    let (instrs_comp, s_comp) = compile_basic_instr h i (new_state nreg nlbl ndepth) in
    app instrs_comp (labeled_compile h il' s_comp.reg s_comp.lbl s_comp.depth)

(** val addresses_labels : labeled_instr list -> (Big_int_Z.big_int list, Big_int_Z.big_int) gmap **)

let addresses_labels il =
  let rec addresses_labels' il0 addr =
    match il0 with
    | [] -> gmap_empty (list_eq_dec0 Coq0_Nat.eq_dec) (list_countable Coq0_Nat.eq_dec nat_countable)
    | l :: il' ->
      (match l with
       | Label lbl0 ->
         insert0
           (map_insert
             (gmap_partial_alter (list_eq_dec0 Coq0_Nat.eq_dec)
               (list_countable Coq0_Nat.eq_dec nat_countable))) lbl0 addr (addresses_labels' il' addr)
       | BInstr _ -> addresses_labels' il' (add addr (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))
       | _ ->
         addresses_labels' il'
           (add addr (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
             Big_int_Z.zero_big_int)))))
  in addresses_labels' il Big_int_Z.zero_big_int

(** val branch_labels : labeled_instr list -> instr list **)

let branch_labels il =
  let label_map = addresses_labels il in
  let rec branch_labels' il0 addr =
    match il0 with
    | [] -> []
    | l :: il' ->
      (match l with
       | Label _ -> branch_labels' il' addr
       | BInstr i ->
         i :: (branch_labels' il' (add addr (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))
       | Br_Jmp (lbl0, reg_tmp) ->
         let off =
           match lookup0
                   (gmap_lookup (list_eq_dec0 Coq0_Nat.eq_dec)
                     (list_countable Coq0_Nat.eq_dec nat_countable)) lbl0 label_map with
           | Some o -> Z.sub (Z.of_nat o) (Z.of_nat addr)
           | None -> Z.zero
         in
         app ((Mov ((R reg_tmp), (Inr PC))) :: ((Lea ((R reg_tmp), (Inl off))) :: ((Jmp (R
           reg_tmp)) :: [])))
           (branch_labels' il'
             (add addr (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
               Big_int_Z.zero_big_int)))))
       | Br_Jnz (lbl0, reg_tmp) ->
         let reg_cond = sub reg_tmp (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
         let off =
           match lookup0
                   (gmap_lookup (list_eq_dec0 Coq0_Nat.eq_dec)
                     (list_countable Coq0_Nat.eq_dec nat_countable)) lbl0 label_map with
           | Some o -> Z.sub (Z.of_nat o) (Z.of_nat addr)
           | None -> Z.zero
         in
         app ((Mov ((R reg_tmp), (Inr PC))) :: ((Lea ((R reg_tmp), (Inl off))) :: ((Jnz ((R reg_tmp),
           (R reg_cond))) :: [])))
           (branch_labels' il'
             (add addr (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
               Big_int_Z.zero_big_int))))))
  in branch_labels' il Big_int_Z.zero_big_int

(** val compile : machineParameters -> basic_instruction list -> instr list **)

let compile h il =
  let min_reg = Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))
  in
  let min_lbl = [] in
  let min_depth = Big_int_Z.zero_big_int in
  branch_labels (labeled_compile h il min_reg min_lbl min_depth)

(** val bank_example_call : basic_instruction list **)

let bank_example_call =
  let account_ptr = Big_int_Z.zero_big_int in
  let account_id = Big_int_Z.succ_big_int Big_int_Z.zero_big_int in
  let account_balance = Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int) in
  (I_get_local account_ptr) :: ((I_const (Val_int Big_int_Z.zero_big_int)) :: ((I_const (Val_int
  (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
  Big_int_Z.zero_big_int)))))) :: (I_slice :: ((I_set_local account_id) :: ((I_get_local
  account_ptr) :: ((I_const (Val_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
  (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))) :: ((I_const (Val_int
  Big_int_Z.zero_big_int)) :: (I_slice :: ((I_set_local account_balance) :: ((I_get_local
  account_balance) :: ((I_const (Val_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
  (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
  Big_int_Z.zero_big_int)))))) :: (I_handleadd :: ((I_set_local account_balance) :: ((I_get_local
  account_balance) :: ((I_const (Val_int Big_int_Z.zero_big_int)) :: ((I_segstore
  T_int) :: ((I_get_local account_id) :: ((I_call Big_int_Z.zero_big_int) :: ((I_get_local
  account_balance) :: ((I_segload T_int) :: []))))))))))))))))))))
