From Coq Require Import ZArith.
From stdpp Require Import base option.
From cap_machine Require Import machine_base machine_parameters addr_reg.
From machine_utils Require Export classes.

(* Helper classes, complementing the ones from machine_utils *)
(* They are used to support automation, and are not intended to be used
   directly in program specifications or manual proof scripts. *)

Class DecodeInstr `{MachineParameters} (w: Word) (i: instr) :=
  MkDecodeInstr: decodeInstrW w = i.
#[global] Hint Mode DecodeInstr - + - : typeclass_instances.
