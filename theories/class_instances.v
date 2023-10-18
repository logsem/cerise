From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes logical_mapsto.
From machine_utils Require Export class_instances.

Instance DecodeInstr_encode `{MachineParameters} (i: instr) :
  DecodeInstr (encodeInstrW i) i.
Proof. apply decode_encode_instrW_inv. Qed.

Instance DecodeInstrL_encode `{MachineParameters} (i: instr) :
  DecodeInstrL (encodeInstrWL i) i.
Proof. apply decode_encode_instrLW_inv. Qed.
