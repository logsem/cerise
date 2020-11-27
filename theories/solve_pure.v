From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg classes class_instances solve_addr.
From cap_machine Require Export solve_addr_extra.
From cap_machine.rules Require Import rules_Get rules_AddSubLt.

From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(* The [solve_pure] tactic is able to solve goals involving:

   - ContiguousRegion
   - SubBounds
   - InBounds
   - ExecPCPerm
   - PermFlows  (TODO: extend)
   - decodeInstrW w = ?
   - (a + z)%a = Some ?
   - readAllowed p (TODO: extend)
   - withinBounds (p, b, e, a) = true
   - is_Get
   - is_AddSubLt

   It also leverages the classes and instances defined in [classes.v] and
   [class_instances.v], but those are not supposed to be used directly in proof
   scripts: it is only expected that [solve_pure] internally generates
   subgoals of these classes during proof search.

   To extend [solve_pure]:
   - prefer adding or using existing lemmas in [machine_base.v].
   - only add lemmas in this file if they do not make sense in [machine_base.v]
     (e.g. they involve some internal classes from [classes.v]).
   - do register an appropriate [Hint Mode] in the [cap_pure] hint base for any
     new notion you are adding support to.
   - add hints to the [cap_pure] hint base for the relevant lemmas; be mindful
     of proof search performance; do not register hints that could lead to a
     blow up (including cases where the search fails). A typical example would
     be adding a transitivity lemma as a hint.
   - do add tests (see end of this file) for the kind of goals you are adding
     support to.
   - if needed, update the list of the supported types of goals above


   /!\ Gotchas /!\:
   - see the "Local context management" section below, regarding handling of
     hypotheses from the local context; add [InCtx] hints if needed.
   - do not add a [Hint Resolve] in [cap_pure] whose conclusion is a class from
     [classes.v]. Register it as an instance instead, otherwise the Hint Modes
     won't work as expected.
*)

Class InCtx (P: Prop) := MkInCtx: P.

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
  unfold InCtx in *.

(* Proof search features *)

Create HintDb cap_pure discriminated.

(* ContiguousRegion *)
Hint Mode ContiguousRegion + - : cap_pure.

Lemma ContiguousRegion_InCtx a z :
  InCtx (ContiguousRegion a z) → ContiguousRegion a z.
Proof. auto. Qed.
Hint Resolve ContiguousRegion_InCtx : cap_pure.

Instance IncrAddr_of_ContiguousRegion a z :
  ContiguousRegion a z →
  IncrAddr a z (a ^+ z)%a.
Proof. intros [? ?]. unfold IncrAddr. solve_addr. Qed.

Instance IncrAddr_in_ContiguousRegion (a a': Addr) (z o z' z'': Z) :
  AsWeakAddrIncr a' a z →
  ContiguousRegion a z'' →
  CbvTC (z + o)%Z z' →
  AddrOffsetLe 0 z →
  AddrOffsetLe 0 o →
  AddrOffsetLe z' z'' →
  IncrAddr a' o (a ^+ z')%a.
Proof.
  unfold AsWeakAddrIncr, ContiguousRegion, CbvTC, AddrOffsetLe, IncrAddr.
  intros -> [? ?] <- ? ?. solve_addr.
Qed.

(* SubBounds *)
Hint Mode SubBounds + + - - : cap_pure.

Lemma SubBounds_InCtx b e b' e' :
  InCtx (SubBounds b e b' e') → SubBounds b e b' e'.
Proof. auto. Qed.

Hint Extern 2 (SubBounds _ _ ?b' ?e') =>
  (is_evar b'; is_evar e'; apply SubBounds_InCtx) : cap_pure.

Hint Extern 0 (SubBounds _ _ ?b' ?e') =>
  (without_evars b'; without_evars e';
   apply SubBounds_InCtx) : cap_pure.

(* Consequences of SubBounds in terms of AddrLe/AddrLt *)

Instance SubBounds_le_b_b' b e b' e' :
  SubBounds b e b' e' →
  AddrLe b b'.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.

Instance SubBounds_le_b'_e' b e b' e' :
  SubBounds b e b' e' →
  AddrLe b' e'.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.

Instance SubBounds_le_e_e' b e b' e' :
  SubBounds b e b' e' →
  AddrLe e' e.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.


(* Manually insert the transitive consequences from above, as we don't want to
   have general transitivity instances for AddrLe/AddrLt *)

Instance SubBounds_le_b_e' b e b' e' :
  SubBounds b e b' e' →
  AddrLe b e'.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.

Instance SubBounds_le_b_e b e b' e' :
  SubBounds b e b' e' →
  AddrLe b e.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.

Instance SubBounds_le_b'_e b e b' e' :
  SubBounds b e b' e' →
  AddrLe b' e.
Proof. unfold SubBounds, AddrLe. solve_addr. Qed.

(* transitivity to deduce lt of the outer bounds from lt of the inner bounds *)

Instance SubBounds_lt_of_inner b e b' e' :
  SubBounds b e b' e' →
  AddrLt b' e' →
  AddrLt b e.
Proof. unfold SubBounds, AddrLt. solve_addr. Qed.

(* InBounds *)

Hint Mode InBounds + + + : cap_pure.

Hint Resolve InBounds_sub : cap_pure.

Lemma InBounds_compare (b a e: Addr) :
  AddrLe b a →
  AddrLt a e →
  InBounds b e a.
Proof. unfold AddrLe, AddrLt, InBounds. auto. Qed.
Hint Resolve InBounds_compare : cap_pure.

Lemma withinBounds_InCtx p b e a :
  InCtx (withinBounds (p, b, e, a) = true) →
  InBounds b e a.
Proof.
  unfold InCtx, InBounds. cbn.
  intros [?%Z.leb_le ?%Z.ltb_lt]%andb_true_iff. solve_addr.
Qed.
Hint Resolve withinBounds_InCtx : cap_pure.

(* isCorrectPC *)

Hint Mode isCorrectPC + : cap_pure.

Hint Resolve isCorrectPC_ExecPCPerm_InBounds : cap_pure.

(* IncrAddr *)

(* This is just a proxy lemma, to then use the Hint Mode of IncrAddr. The
   intention is that [a] and [z] are known, and that we want to infer [a']. *)
Lemma IncrAddr_prove a z a' :
  IncrAddr a z a' →
  (a + z)%a = Some a'.
Proof.
  intros ->. reflexivity.
Qed.
Hint Resolve IncrAddr_prove : cap_pure.

Instance IncrAddr_InCtx a z a' :
  InCtx ((a + z)%a = Some a') → IncrAddr a z a'.
Proof. auto. Qed.

(* Proxy lemma for DecodeInstr *)

Lemma DecodeInstr_prove `{MachineParameters} w i :
  DecodeInstr w i →
  decodeInstrW w = i.
Proof.
  intros ->. reflexivity.
Qed.
Hint Resolve DecodeInstr_prove : cap_pure.

(* ExecPCPerm, PermFlows *)

Hint Mode ExecPCPerm + : cap_pure.
Hint Mode PermFlows - + : cap_pure.

Lemma ExecPCPerm_InCtx p :
  InCtx (ExecPCPerm p) → ExecPCPerm p.
Proof. auto. Qed.
Hint Resolve ExecPCPerm_InCtx : cap_pure.

Hint Resolve ExecPCPerm_RX : cap_pure.
Hint Resolve ExecPCPerm_RWX : cap_pure.
Hint Resolve ExecPCPerm_not_E : cap_pure.
Hint Resolve ExecPCPerm_flows_to : cap_pure.
(* TODO: add a test checking the use of ExecPCPerm_flows_to *)
Hint Resolve ExecPCPerm_readAllowed : cap_pure.
Hint Extern 1 (readAllowed _ = true) => reflexivity : cap_pure.

(* withinBounds *)

(* There's no use defining a Hint Mode for withinBounds, as it doesn't appear as
   the head symbol. (in "withinBounds _ = true", (=) is the head symbol).

   That's fine: this proxy lemma applies without risking instantiating any evar,
   and then the Hint Mode on [InBounds] can take effect. *)

Hint Resolve withinBounds_InBounds : cap_pure.

(* is_Get *)
Hint Mode is_Get ! - - : cap_pure.
Hint Resolve is_Get_GetP : cap_pure.
Hint Resolve is_Get_GetB : cap_pure.
Hint Resolve is_Get_GetE : cap_pure.
Hint Resolve is_Get_GetA : cap_pure.

(* is_AddSubLt *)
Hint Mode is_AddSubLt ! - - - : cap_pure.
Hint Resolve is_AddSubLt_Add : cap_pure.
Hint Resolve is_AddSubLt_Sub : cap_pure.
Hint Resolve is_AddSubLt_Lt : cap_pure.

(* *)

Ltac2 solve_pure () :=
  first [ assumption
    | discriminate
    | ltac1:(freeze_hyps);
      typeclasses_eauto with cap_pure typeclass_instances;
      ltac1:(unfreeze_hyps) ].

Ltac solve_pure :=
  ltac2:(solve_pure ()).


(* Tests *)

Goal forall (b: Addr) a (z z': Z),
  ContiguousRegion b z' →
  AsWeakAddrIncr a b z →
  AddrOffsetLt z z' →
  AddrOffsetLe 0 z →
  InBounds b (b ^+ z')%a a.
Proof. intros. typeclasses eauto with cap_pure typeclass_instances. Qed.

Goal forall (a: Addr),
  ContiguousRegion a 5 →
  exists a', IncrAddr a 1 a' ∧ a' = (a ^+ 1)%a.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall (a: Addr),
  ContiguousRegion a 5 →
  exists a', IncrAddr (a ^+ 1)%a 1 a' ∧ a' = (a ^+ 2)%a.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall (r_t1 PC: RegName) `{MachineParameters}, exists r1 r2,
  decodeInstrW (encodeInstrW (Mov r_t1 PC)) = Mov r1 r2 ∧
  r1 = r_t1 ∧ r2 = inr PC.
Proof. do 2 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (inr (p, b, e, a)).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2: RegName), exists r1 r2,
  is_Get (GetB r_t2 r_t1) r1 r2 ∧
  r1 = r_t2 ∧ r2 = r_t1.
Proof. do 2 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (inr (p, b, e, (a ^+ 1)%a)).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2 r_t3: RegName), exists r1 r2 r3,
  is_AddSubLt (Sub r_t2 r_t2 r_t3) r1 (inr r2) (inr r3) ∧
  r1 = r_t2 ∧ r2 = r_t2 ∧ r3 = r_t3.
Proof. do 3 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall a, exists a',
  ContiguousRegion a 2 →
  ((a ^+ 1)%a + 1)%a = Some a' ∧ a' = (a ^+ 2)%a.
Proof. intros. eexists. split. solve_pure. reflexivity. Qed.

Goal forall (a b c: Addr),
  (a + b)%a = Some c →
  exists (a b c: Addr),
  (a + b)%a = Some c.
Proof. intros. do 3 eexists. Fail solve_pure. Abort.

Goal forall (a b: Addr), exists c,
  ContiguousRegion a 5 →
  (a + (b - a))%a = Some c.
Proof. intros. eexists. Fail solve_pure. Abort.

Goal E ≠ RO. solve_pure. Qed.
Goal forall (P: Prop), P → P. intros. solve_pure. Qed.

Goal forall (a: Addr) z, exists z' a',
  ContiguousRegion a z →
  IncrAddr a z' a'.
Proof. intros. do 2 eexists. intros. Fail solve_pure. Abort.
