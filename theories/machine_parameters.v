From Coq Require Import ZArith.
From stdpp Require Import base.
From cap_machine Require Export machine_base.

Class MachineParameters := {
  decodeInstr : Z → instr;
  encodeInstr : instr → Z;

  decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;

  encodePerm : Perm → Z;
  encodePerm_inj : Inj eq eq encodePerm;
  decodePerm : Z → Perm;

  decode_encode_perm_inv :
    forall pl, decodePerm (encodePerm pl) = pl;

  encodeSealPerms : Seal_Perms → Z;
  encodeSealPerms_inj : Inj eq eq encodeSealPerms;
  decodeSealPerms : Z → Seal_Perms;

  decode_encode_seal_perms_inv :
    forall pl, decodeSealPerms (encodeSealPerms pl) = pl;
}.

(* Lift the encoding / decoding between Z and instructions on Words: simplify
   fail on capabilities. *)

Definition decodeInstrW `{MachineParameters} : Word → instr :=
  fun w =>
    match get_z w with
    | Some z => decodeInstr z
    | _ => Fail
    end.

Definition encodeInstrW `{MachineParameters} : instr → Word :=
  fun i => WInt (encodeInstr i).

Lemma decode_encode_instrW_inv `{MachineParameters} (i: instr):
  decodeInstrW (encodeInstrW i) = i.
Proof. apply decode_encode_instr_inv. Qed.

Definition encodeInstrsW `{MachineParameters} : list instr → list Word :=
  map encodeInstrW.
