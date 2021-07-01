From cap_machine Require Import solve_addr machine_base classes.

(* Extend [solve_addr] to handle more pure arithmetic goals from
   [machine_base.v] and [classes.v] *)

Ltac without_evars c :=
  (has_evar c; fail 1) || idtac.

Global Ltac zify_addr_op_nonbranching_step_hook ::=
  lazymatch goal with
  | H : ContiguousRegion _ _ |- _ => destruct H
  | H : SubBounds _ _ _ _ |- _ => unfold SubBounds in H
  | |- SubBounds ?b ?e ?b' ?e' =>
    without_evars b; without_evars e; without_evars b'; without_evars e';
    unfold SubBounds
  | H : InBounds _ _ _ |- _ => unfold InBounds in H
  | |- InBounds ?b ?e ?a =>
    without_evars b; without_evars e; without_evars a;
    unfold InBounds
  | H : IncrAddr _ _ _ |- _ => unfold IncrAddr in H
  | |- IncrAddr ?a ?z ?a' =>
    without_evars a; without_evars z; without_evars a';
    unfold IncrAddr
  | H : withinBounds _ _ _ = true |- _ =>
    apply withinBounds_le_addr in H
  | |- withinBounds ?b ?e ?a = true =>
    without_evars b; without_evars e; without_evars a;
    apply le_addr_withinBounds'
  | H : isCorrectPC (_, _, _, _) |- _ =>
    apply isCorrectPC_le_addr in H
  | H : isWithin _ _ _ _ = true |- _ => apply isWithin_implies in H
  | |- isWithin ?b ?e ?b' ?e' = true =>
    without_evars b; without_evars e; without_evars b'; without_evars e';
    apply isWithin_of_le
  end.


(* tests *)
From Coq Require Import ZArith.

Goal forall d d' d'',
  (d + 1)%a = Some d'' ->
  (d + 2)%a = Some d' ->
  withinBounds d d' d'' = true.
Proof. intros. solve_addr. Qed.
