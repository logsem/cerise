From Coq Require Import ZArith.
From stdpp Require Import base.
From cap_machine Require Export machine_base.

Class MachineParameters := {
  decodeInstr : Z → instr;
  encodeInstr : instr → Z;

  decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;
  encode_decode_instr_not_fail :
    forall (z: Z), decodeInstr z ≠ Fail →
                   encodeInstr (decodeInstr z) = z;

  encodePerm : Perm → Z;
  encodePerm_inj : Inj eq eq encodePerm;

  encodeLoc : Locality → Z;
  encodeLoc_inj : Inj eq eq encodeLoc;

  decodePermPair : Z → Perm * Locality;
  encodePermPair : Perm * Locality → Z;

  decode_encode_permPair_inv :
    forall pl, decodePermPair (encodePermPair pl) = pl;
}.

(* Lift the encoding / decoding between Z and instructions on Words: simplify
   fail on capabilities. *)

Definition decodeInstrW `{MachineParameters} : Word → instr :=
  fun w =>
    match w with
    | inl z => decodeInstr z
    | inr _ => Fail
    end.

Definition encodeInstrW `{MachineParameters} : instr → Word :=
  fun i => inl (encodeInstr i).

Lemma decode_encode_instrW_inv `{MachineParameters} (i: instr):
  decodeInstrW (encodeInstrW i) = i.
Proof. apply decode_encode_instr_inv. Qed.

Lemma encode_decode_instrW_not_fail `{MachineParameters} (w: Word):
  decodeInstrW w ≠ Fail → encodeInstrW (decodeInstrW w) = w.
Proof.
  destruct w; cbn.
  - intros. unfold encodeInstrW. f_equal. apply encode_decode_instr_not_fail. auto.
  - intros. congruence.
Qed.
