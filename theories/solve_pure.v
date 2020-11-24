From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes class_instances.
From cap_machine.rules Require Import rules_Get rules_AddSubLt.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Create HintDb cap_pure discriminated. (* /!\ *)
Hint Mode eq + + - : cap_pure. (* XXX hackish *) (* TODO: freeze local context *)

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

Ltac2 solve_cap_pure () :=
  (* XXX remove this hack by using freezing on the local ctx *)
  (* Avoid running proof search on goals of the form [(?a + ?z)%a = Some ?a'],
     which can pick up random hypotheses from the context, instantiating the
     evars. This cannot easily be controled using a Hint Mode (which only
     applies to the head constant. *)
  let is_evar (c: constr) :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Evar(_)(_) => true
    | _ => false
    end
  in
  lazy_match! goal with
  | [ |- (?a + ?y)%a = Some _ ] =>
    match Bool.or (is_evar a) (is_evar y) with
    | true => Control.zero (Tactic_failure(None))
    | false => ()
    end
  | [ |- _ ] => ()
  end;
  (* otherwise: *)
  typeclasses_eauto with cap_pure typeclass_instances.

Ltac solve_cap_pure :=
  ltac2:(solve_cap_pure ()).


(* Tests *)

(* TODO: move *)
  Definition regn : RegName → (Z+RegName)%type := inr.
  Definition cst : Z → (Z+RegName)%type := inl.

  Coercion regn : RegName >-> sum.
  Coercion cst : Z >-> sum.

Goal forall (r_t1 PC: RegName) `{MachineParameters}, exists r1 r2,
  decodeInstrW (encodeInstrW (Mov r_t1 PC)) = Mov r1 r2 ∧
  r1 = r_t1 ∧ r2 = inr PC.
Proof. do 2 eexists. repeat apply conj. solve_cap_pure. all: reflexivity. Qed.

Goal forall p b e a n,
  AddrOffsetLt 0 n →
  ExecPCPerm p →
  SubBounds b e a (a ^+ n)%a →
  ContiguousRegion a n →
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
