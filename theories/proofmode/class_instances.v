From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes.
From machine_utils Require Export class_instances.

Instance DecodeInstr_encode `{MachineParameters} (i: instr) :
  DecodeInstr (encodeInstrW i) i.
Proof. apply decode_encode_instrW_inv. Qed.

