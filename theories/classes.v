From Coq Require Import ZArith.
From stdpp Require Import base option.
From cap_machine Require Import machine_base machine_parameters addr_reg.

(* Helper classes. These are used to support proofsearch for automation (of in
   particular the [solve_cap_pure] tactic). They are not intended to be used
   directly in program specifications or manual proof scripts. *)

(* Reduction helpers *)

Class SimplTC {A} (x x': A) :=
  MkSimplTc: x = x'.

Class CbvTC {A} (x x': A) :=
  MkCbvTc: x = x'.

(* Address arithmetic *)

Class AddrOffsetLt z z' := MkAddrOffsetLt: (z < z')%Z.
Hint Mode AddrOffsetLt + + : typeclass_instances.
Class AddrOffsetLe z z' := MkAddrOffsetLe: (z <= z')%Z.
Hint Mode AddrOffsetLe + + : typeclass_instances.

Class AsWeakAddrIncr (a: Addr) (b: Addr) (z: Z) :=
  MkAsWeakAddrIncr: a = (b ^+ z)%a.
Hint Mode AsWeakAddrIncr ! - - : typeclass_instances.

Class IncrAddr (a: Addr) (z: Z) (a': Addr) :=
  MkIncrAddr: (a + z)%a = Some a'.
Hint Mode IncrAddr + + - : typeclass_instances.

Class AddrLe (a a': Addr) := MkAddrLe: (a <= a')%a.
Hint Mode AddrLe + + : typeclass_instances.
Class AddrLt (a a': Addr) := MkAddrLt: (a < a')%a.
Hint Mode AddrLt + + : typeclass_instances.

Class AddrEq (a b: Addr) (res: bool) :=
  MkAddrEq: res = true → a = b.
Hint Mode AddrEq + + - : typeclass_instances.

(* Other *)

Class DecodeInstr `{MachineParameters} (w: Word) (i: instr) :=
  MkDecodeInstr: decodeInstrW w = i.
Hint Mode DecodeInstr - + - : typeclass_instances.
