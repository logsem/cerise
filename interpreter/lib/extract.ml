
type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val length : 'a1 list -> Z.t **)

let rec length = function
| [] -> Z.zero
| _ :: l' -> Z.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Coq__1 = struct
 (** val add : Z.t -> Z.t -> Z.t **)
 let add (n : Z.t) (m : Z.t) : Z.t = Z.add n m
end
include Coq__1

(** val sub : Z.t -> Z.t -> Z.t **)

let sub = fun n m -> Z.max Z.zero (Z.sub n m)

type z = Z.t

module Nat =
 struct
  (** val eq_dec : Z.t -> Z.t -> bool **)

  let eq_dec = Z.equal
 end


(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)


type decision = bool

(** val decide : decision -> bool **)

let decide decision0 =
  decision0

type ('a, 'b) relDecision = 'a -> 'b -> decision

(** val decide_rel : ('a1, 'a2) relDecision -> 'a1 -> 'a2 -> decision **)

let decide_rel relDecision0 =
  relDecision0

(** val foldl : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec foldl f a = function
| [] -> a
| x :: l0 -> foldl f (f a x) l0

(** val elem_of_list_dec :
    ('a1, 'a1) relDecision -> ('a1, 'a1 list) relDecision **)

let rec elem_of_list_dec dec x = function
| [] -> false
| y :: l0 ->
  if decide (decide_rel dec x y) then true else elem_of_list_dec dec x l0

(** val list_difference :
    ('a1, 'a1) relDecision -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec list_difference dec l k =
  match l with
  | [] -> []
  | x :: l0 ->
    if decide_rel (elem_of_list_dec dec) x k
    then list_difference dec l0 k
    else x :: (list_difference dec l0 k)

type immediate = Z.t

type handle = { base : Z.t; offset : Z.t; bound : Z.t; valid : bool; id : Z.t }

type value =
| Val_int of Z.t
| Val_handle of handle

type value_type =
| T_int
| T_handle

type binop =
| BOI_add
| BOI_sub

type basic_instruction =
| I_nop
| I_drop
| I_const of value
| I_binop of value_type * binop
| I_get_local of immediate
| I_set_local of immediate
| I_load of value_type
| I_store of value_type
| I_br of immediate
| I_call of immediate
| I_return
| I_segload of value_type
| I_segstore of value_type
| I_slice
| I_segalloc
| I_handleadd
| I_segfree

type regName =
| PC
| R of Z.t

(** val all_registers : regName list **)

let all_registers =
  (R Z.zero) :: ((R (Z.succ Z.zero)) :: ((R (Z.succ (Z.succ Z.zero))) :: ((R
    (Z.succ (Z.succ (Z.succ Z.zero)))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ Z.zero)))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ Z.zero))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ Z.zero)))))))))) :: ((R
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ Z.zero))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ Z.zero)))))))))))) :: ((R
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ Z.zero))))))))))))) :: ((R (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ Z.zero)))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ Z.zero))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ Z.zero)))))))))))))))) :: ((R (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ Z.zero))))))))))))))))) :: ((R
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ Z.zero))))))))))))))))))) :: ((R (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ Z.zero)))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ Z.zero))))))))))))))))))))))))) :: ((R (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ Z.zero))))))))))))))))))))))))))) :: ((R
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))))))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero)))))))))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    Z.zero))))))))))))))))))))))))))))))) :: ((R (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ
    (Z.succ
    Z.zero)))))))))))))))))))))))))))))))) :: (PC :: []))))))))))))))))))))))))))))))))

(** val reg_eq_dec : (regName, regName) relDecision **)

let reg_eq_dec r1 r2 =
  match r1 with
  | PC -> (match r2 with
           | PC -> true
           | R _ -> false)
  | R n -> (match r2 with
            | PC -> false
            | R n0 -> Nat.eq_dec n n0)

(** val r : Z.t -> (z, regName) sum **)

let r n =
  Inr (R n)

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
| Mov of regName * (z, regName) sum
| Load of regName * regName
| Store of regName * (z, regName) sum
| Lt of regName * (z, regName) sum * (z, regName) sum
| Add of regName * (z, regName) sum * (z, regName) sum
| Sub of regName * (z, regName) sum * (z, regName) sum
| Lea of regName * (z, regName) sum
| Restrict of regName * (z, regName) sum
| Subseg of regName * (z, regName) sum * (z, regName) sum
| IsPtr of regName * regName
| GetL of regName * regName
| GetP of regName * regName
| GetB of regName * regName
| GetE of regName * regName
| GetA of regName * regName
| Fail
| Halt
| Nop
| LoadU of regName * regName * (z, regName) sum
| StoreU of regName * (z, regName) sum * (z, regName) sum
| PromoteU of regName

type machineParameters = { decodeInstr : (z -> instr);
                           encodeInstr : (instr -> z);
                           encodePerm : (perm -> z);
                           encodeLoc : (locality -> z);
                           decodePermPair : (z -> perm * locality);
                           encodePermPair : ((perm * locality) -> z) }

(** val bank_example : basic_instruction list **)

let bank_example =
  let account_ptr = Z.zero in
  let account_id = Z.succ Z.zero in
  let account_balance = Z.succ (Z.succ Z.zero) in
  (I_get_local account_ptr) :: ((I_const (Val_int Z.zero)) :: ((I_const
  (Val_int (Z.succ (Z.succ (Z.succ (Z.succ
  Z.zero)))))) :: (I_slice :: ((I_set_local account_id) :: ((I_get_local
  account_ptr) :: ((I_const (Val_int (Z.succ (Z.succ (Z.succ (Z.succ
  Z.zero)))))) :: ((I_const (Val_int Z.zero)) :: (I_slice :: ((I_set_local
  account_balance) :: ((I_get_local account_balance) :: ((I_const (Val_int
  (Z.succ (Z.succ (Z.succ (Z.succ
  Z.zero)))))) :: (I_handleadd :: ((I_set_local
  account_balance) :: ((I_get_local account_balance) :: ((I_const (Val_int
  Z.zero)) :: ((I_segstore T_int) :: ((I_get_local account_id) :: ((I_call
  Z.zero) :: ((I_get_local account_balance) :: ((I_segload
  T_int) :: []))))))))))))))))))))
