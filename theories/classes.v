From Coq Require Import ZArith.
From stdpp Require Import base option.
From cap_machine Require Import machine_base machine_parameters addr_reg.

(* Helpers *)

Class SimplTC {A} (x x': A) :=
  MkSimplTc: x = x'.

Class CbvTC {A} (x x': A) :=
  MkCbvTc: x = x'.

(* Address regions *)
(* XXX Should these be moved to the cap_pure hintsdb? *)

Class ContiguousRegion (a: Addr) (z: Z): Prop :=
  MkContiguousRegion: is_Some (a + z)%a.
Hint Mode ContiguousRegion + - : typeclass_instances.

Class SubBounds (b e: Addr) (b' e': Addr) :=
  MkSubBounds: (b <= b')%a ∧ (b' <= e')%a ∧ (e' <= e)%a.
Hint Mode SubBounds + + - - : typeclass_instances.

Class InBounds (b e: Addr) (a: Addr) :=
  MkInBounds: (b <= a)%a ∧ (a < e)%a.
Hint Mode InBounds + + + : typeclass_instances.

(* Address manipulation *)

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

Class ExecPCPerm p :=
  MkExecPcPerm: p = RX ∨ p = RWX.
Hint Mode ExecPCPerm + : typeclass_instances.

Existing Class PermFlows.

Class DecodeInstr `{MachineParameters} (w: Word) (i: instr) :=
  MkDecodeInstr: decodeInstrW w = i.
Hint Mode DecodeInstr + + - : typeclass_instances.
