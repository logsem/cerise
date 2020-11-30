From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes.

(* Helper tactics *)

Hint Extern 0 (@SimplTC _ _ _) => (cbn; reflexivity) : typeclass_instances.
Hint Extern 0 (@CbvTC _ ?lhs _) => (
  let lhs' := eval vm_compute in lhs in
  change lhs with lhs';
  reflexivity
) : typeclass_instances.

(* Address manipulation *)

Instance AddrOffsetLe_refl z : AddrOffsetLe z z.
Proof. apply Z.le_refl. Qed.

Lemma AddrOffsetLe_compute z z': (z <=? z' = true)%Z -> AddrOffsetLe z z'.
Proof. intro. apply Z.leb_le; auto. Qed.
Hint Extern 1 (AddrOffsetLe _ _) => (apply AddrOffsetLe_compute; reflexivity) : typeclass_instances.

Lemma AddrOffsetLt_compute z z': (z <? z' = true)%Z -> AddrOffsetLt z z'.
Proof. intro. apply Z.ltb_lt; auto. Qed.
Hint Extern 1 (AddrOffsetLt _ _) => (apply AddrOffsetLt_compute; reflexivity) : typeclass_instances.

Instance AddrOffsetLe_of_lt z z': AddrOffsetLt z z' → AddrOffsetLe z z'.
Proof. unfold AddrOffsetLt, AddrOffsetLe. lia. Qed.

Instance AsWeakAddrIncr_incr b z:
  AsWeakAddrIncr (b ^+ z)%a b z.
Proof. reflexivity. Qed.

Instance AsWeakAddrIncr_no_incr b :
  AsWeakAddrIncr b b 0 | 50.
Proof. unfold AsWeakAddrIncr. solve_addr. Qed.

Instance AddrLe_refl a : AddrLe a a.
Proof. unfold AddrLe. solve_addr. Qed.

Instance AddrLe_of_lt a a' : AddrLt a a' → AddrLe a a'.
Proof. unfold AddrLt, AddrLe. solve_addr. Qed.

Instance AddrLe_offsets (a a' a'': Addr) (z z': Z) :
  AsWeakAddrIncr a' a z →
  AsWeakAddrIncr a'' a z' →
  AddrOffsetLe 0 z →
  AddrOffsetLe z z' →
  AddrLe a' a''.
Proof. unfold AddrOffsetLe, AddrLe, AsWeakAddrIncr. solve_addr. Qed.

Instance AddrLt_offsets (a a' a'': Addr) (z z': Z) :
  AsWeakAddrIncr a' a z →
  AsWeakAddrIncr a'' a z' →
  AddrOffsetLe 0 z →
  ContiguousRegion a z' →
  AddrOffsetLt z z' →
  AddrLt a' a''.
Proof.
  unfold AsWeakAddrIncr, AddrOffsetLe, AddrOffsetLt, AddrLt.
  intros ? ? ? [? ?] ?. solve_addr.
Qed.

Instance AddrEqSame a : AddrEq a a true.
Proof. constructor. Qed.

Instance AddrEq_offset_cbv b z z' :
  CbvTC z z' →
  AddrEq (b ^+ z)%a (b ^+ z')%a true.
Proof. intros ->. constructor. Qed.

Instance AddrEq_default_neq a a' : AddrEq a a' false | 100.
Proof. inversion 1. Qed.

(* other *)

Instance DecodeInstr_encode `{MachineParameters} (i: instr) :
  DecodeInstr (encodeInstrW i) i.
Proof. apply decode_encode_instrW_inv. Qed.




(* Tests *)

Goal forall (a: Addr),
  AddrEq (a ^+ 1)%a (a ^+ (Z.of_nat 1))%a true.
Proof. typeclasses eauto. Qed.

Goal forall (a: Addr), exists a' z,
  AsWeakAddrIncr (a ^+ 1)%a a' z ∧ a' = a ∧ z = 1%Z.
Proof. intros. do 2 eexists. repeat apply conj. typeclasses eauto. all: reflexivity. Qed.

