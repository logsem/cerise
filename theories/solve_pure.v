From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes class_instances.
From cap_machine.rules Require Import rules_Get rules_AddSubLt.

From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

Create HintDb cap_pure discriminated. (* /!\ *)

Lemma isCorrectPC_prove p b e a :
  ExecPCPerm p →
  InBounds b e a →
  isCorrectPC (inr (p, b, e, a)).
Proof.
  unfold ExecPCPerm, InBounds. intros. constructor; eauto.
Qed.
Hint Resolve isCorrectPC_prove : cap_pure.
Hint Mode isCorrectPC + : cap_pure.

Lemma IncrAddr_prove a z a' :
  IncrAddr a z a' →
  (a + z)%a = Some a'.
Proof.
  intros ->. reflexivity.
Qed.
Hint Resolve IncrAddr_prove : cap_pure.

Lemma DecodeInstr_prove `{MachineParameters} w i :
  DecodeInstr w i →
  decodeInstrW w = i.
Proof.
  intros ->. reflexivity.
Qed.
Hint Resolve DecodeInstr_prove : cap_pure.

Lemma ExecPCPerm_not_E p :
  ExecPCPerm p →
  p ≠ E.
Proof.
  intros [H|H] ->; inversion H.
Qed.
Hint Resolve ExecPCPerm_not_E : cap_pure.

Lemma ExecPCPerm_readAllowed p :
  ExecPCPerm p →
  readAllowed p = true.
Proof.
  intros [-> | ->]; reflexivity.
Qed.
Hint Resolve ExecPCPerm_readAllowed : cap_pure.
Hint Extern 1 (readAllowed _ = true) => reflexivity : cap_pure.

Lemma withinBounds_InBounds p b e a :
  InBounds b e a →
  withinBounds (p, b, e, a) = true.
Proof.
  intros [? ?]. unfold withinBounds.
  apply andb_true_intro.
  split; [apply Z.leb_le;solve_addr | apply Z.ltb_lt;auto].
Qed.
Hint Resolve withinBounds_InBounds : cap_pure.

(* is_Get *)
Hint Resolve is_Get_GetP : cap_pure.
Hint Resolve is_Get_GetB : cap_pure.
Hint Resolve is_Get_GetE : cap_pure.
Hint Resolve is_Get_GetA : cap_pure.
Hint Mode is_Get ! - - : cap_pure.

(* is_AddSubLt *)
Hint Resolve is_AddSubLt_Add : cap_pure.
Hint Resolve is_AddSubLt_Sub : cap_pure.
Hint Resolve is_AddSubLt_Lt : cap_pure.
Hint Mode is_AddSubLt ! - - - : cap_pure.

(* Local context management *)

Class InCtx (P: Prop) := MkInCtx: P.

Instance ContiguousRegion_InCtx a z :
  InCtx (ContiguousRegion a z) → ContiguousRegion a z.
Proof. auto. Qed.

Instance IncrAddr_InCtx a z a' :
  InCtx ((a + z)%a = Some a') → IncrAddr a z a'.
Proof. auto. Qed.

Instance ExecPCPerm_InCtx p :
  InCtx (ExecPCPerm p) → ExecPCPerm p.
Proof. auto. Qed.

Lemma SubBounds_InCtx b e b' e' :
  InCtx (SubBounds b e b' e') → SubBounds b e b' e'.
Proof. auto. Qed.

Instance withinBounds_InCtx p b e a :
  InCtx (withinBounds (p, b, e, a) = true) →
  InBounds b e a.
Proof.
  unfold InCtx, InBounds. cbn.
  intros [?%Z.leb_le ?%Z.ltb_lt]%andb_true_iff. solve_addr.
Qed.

Hint Extern 1 (SubBounds _ _ ?b' ?e') =>
  (is_evar b'; is_evar e'; apply SubBounds_InCtx) : typeclass_instances.

Ltac contains_evars c :=
  match c with
  | context [ ?x ] => is_evar x
  end.

Ltac2 does_not_contain_evars c :=
  match
    Control.case
      (fun _ => ltac1:(c |- contains_evars c) (Ltac1.of_constr c))
  with
  | Err _ => ()
  | Val _ => Control.zero (Tactic_failure(None))
  end.
Ltac does_not_contain_evars c :=
  let f := ltac2:(c |- does_not_contain_evars (Option.get (Ltac1.to_constr c))) in
  f c.

Goal exists (x:nat), x = S x ∧ 1 = x.
  eexists. split.
  match goal with |- ?y = _ => contains_evars y end.
  match goal with |- _ = ?y => contains_evars y end.
  all: cycle 1.
  match goal with |- ?y = _ => does_not_contain_evars y end.
Abort.

Hint Extern 1 (SubBounds _ _ ?b' ?e') =>
  (does_not_contain_evars b'; does_not_contain_evars e';
   apply SubBounds_InCtx) : typeclass_instances.

(* *)

Ltac freeze_hyps :=
  repeat (match goal with
  | h : ?P |- _ =>
    lazymatch type of P with
    | Prop => idtac
    | _ => fail
    end;
    lazymatch P with
    | InCtx _ => fail
    | _ => idtac
    end;
    change P with (InCtx P) in h
  end).

Ltac unfreeze_hyps :=
  repeat (match goal with
  | h : InCtx ?P |- _ =>
    change (InCtx P) with P in h
  end).

Ltac2 solve_cap_pure () :=
  first [ assumption
    | discriminate
    | ltac1:(freeze_hyps);
      typeclasses_eauto with cap_pure typeclass_instances;
      ltac1:(unfreeze_hyps) ].

Ltac solve_cap_pure :=
  ltac2:(solve_cap_pure ()).


(* Tests *)

Goal forall (r_t1 PC: RegName) `{MachineParameters}, exists r1 r2,
  decodeInstrW (encodeInstrW (Mov r_t1 PC)) = Mov r1 r2 ∧
  r1 = r_t1 ∧ r2 = inr PC.
Proof. do 2 eexists. repeat apply conj. solve_cap_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (inr (p, b, e, a)).
Proof. intros. solve_cap_pure. Qed.

Goal forall (r_t1 r_t2: RegName), exists r1 r2,
  is_Get (GetB r_t2 r_t1) r1 r2 ∧
  r1 = r_t2 ∧ r2 = r_t1.
Proof. do 2 eexists. repeat apply conj. solve_cap_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (inr (p, b, e, (a ^+ 1)%a)).
Proof. intros. solve_cap_pure. Qed.

Goal forall (r_t1 r_t2 r_t3: RegName), exists r1 r2 r3,
  is_AddSubLt (Sub r_t2 r_t2 r_t3) r1 (inr r2) (inr r3) ∧
  r1 = r_t2 ∧ r2 = r_t2 ∧ r3 = r_t3.
Proof. do 3 eexists. repeat apply conj. solve_cap_pure. all: reflexivity. Qed.

Goal forall a, exists a',
  ContiguousRegion a 2 →
  ((a ^+ 1)%a + 1)%a = Some a' ∧ a' = (a ^+ 2)%a.
Proof. intros. eexists. split. solve_cap_pure. reflexivity. Qed.

Goal forall (a b c: Addr),
  (a + b)%a = Some c →
  exists (a b c: Addr),
  (a + b)%a = Some c.
Proof. intros. do 3 eexists. Fail solve_cap_pure. Abort.

Goal forall (a b: Addr), exists c,
  ContiguousRegion a 5 →
  (a + (b - a))%a = Some c.
Proof. intros. eexists. Fail solve_cap_pure. Abort.

Goal E ≠ RO. solve_cap_pure. Qed.
Goal forall (P: Prop), P → P. intros. solve_cap_pure. Qed.
