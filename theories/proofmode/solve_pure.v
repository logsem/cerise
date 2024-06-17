From Coq Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From cap_machine Require Import machine_base machine_parameters addr_reg solve_addr.
From cap_machine Require Export solve_addr_extra classes class_instances.
From cap_machine.rules Require Import rules_Get rules_AddSubLt.
From machine_utils Require Export solve_pure.

Ltac solve_pure_addr := solve_pure_finz.

(* Extend the [solve_pure] tactic from [machine_utils] with additional hints
   for solving goals specific to our machine, involving (additionally from what
   [solve_pure] already handles):

   - ExecPCPerm
   - PermFlows, PermFlowsTo  (TODO: extend)
   - decodeInstrW w = ?
   - readAllowed p (TODO: extend)
   - writeAllowed p (TODO: extend)
   - withinBounds (p, b, e, a) = true
   - is_Get
   - is_AddSubLt

   See the comments in [machine_utils/theories/solve_pure.v] on how to
   extend [solve_pure] with more hints.
*)

Lemma withinBounds_InCtx {z} (b e a : finz z) :
  InCtx (withinBounds b e a = true) →
  InBounds b e a.
Proof.
  unfold InCtx, InBounds. cbn.
  intros [?%Z.leb_le ?%Z.ltb_lt]%andb_true_iff. solve_addr.
Qed.
#[export] Hint Resolve withinBounds_InCtx : solve_pure.

(* isCorrectPC *)

#[export] Hint Mode isCorrectPC + : solve_pure.

#[export] Hint Resolve isCorrectPC_ExecPCPerm_InBounds : solve_pure.

(* Proxy lemma for DecodeInstr *)

Lemma DecodeInstr_prove `{MachineParameters} w i :
  DecodeInstr w i →
  decodeInstrW w = i.
Proof.
  intros ->. reflexivity.
Qed.
#[export] Hint Resolve DecodeInstr_prove : solve_pure.

(* ExecPCPerm, PermFlows *)

#[export] Hint Mode ExecPCPerm + : solve_pure.
#[export] Hint Mode PermFlows - + : solve_pure.

Lemma ExecPCPerm_InCtx p :
  InCtx (ExecPCPerm p) → ExecPCPerm p.
Proof. auto. Qed.
#[export] Hint Resolve ExecPCPerm_InCtx : solve_pure.

#[export] Hint Resolve ExecPCPerm_RX : solve_pure.
#[export] Hint Resolve ExecPCPerm_RWX : solve_pure.
#[export] Hint Resolve ExecPCPerm_flows_to : solve_pure.
(* TODO: add a test checking the use of ExecPCPerm_flows_to (if it is still
   needed) *)
#[export] Hint Resolve ExecPCPerm_readAllowed : solve_pure.
(* Will only work if arguments are concrete terms *)
#[export] Hint Extern 1 (readAllowed _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (writeAllowed _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (PermFlowsTo _ _ = true) => reflexivity : solve_pure.
(* Follows the same behavior as the Hint Mode for PermFlows *)
#[export] Hint Extern 1 (PermFlowsTo ?p ?p' = true) =>
  (without_evars p'; apply PermFlowsToReflexive): solve_pure.

(* withinBounds *)

(* There's no use defining a Hint Mode for withinBounds, as it doesn't appear as
   the head symbol. (in "withinBounds _ = true", (=) is the head symbol).

   That's fine: this proxy lemma applies without risking instantiating any evar,
   and then the Hint Mode on [InBounds] can take effect. *)

#[export] Hint Resolve withinBounds_InBounds : solve_pure.

(* is_Get *)
#[export] Hint Mode is_Get ! - - : solve_pure.
#[export] Hint Resolve is_Get_GetP : solve_pure.
#[export] Hint Resolve is_Get_GetB : solve_pure.
#[export] Hint Resolve is_Get_GetE : solve_pure.
#[export] Hint Resolve is_Get_GetA : solve_pure.
#[export] Hint Resolve is_Get_GetOType : solve_pure.
#[export] Hint Resolve is_Get_GetWType : solve_pure.

(* is_AddSubLt *)
#[export] Hint Mode is_AddSubLt ! - - - : solve_pure.
#[export] Hint Resolve is_AddSubLt_Add : solve_pure.
#[export] Hint Resolve is_AddSubLt_Sub : solve_pure.
#[export] Hint Resolve is_AddSubLt_Lt : solve_pure.

(* is_z *)
#[export] Hint Extern 1 (is_z _ = false) => reflexivity : solve_pure.
#[export] Hint Extern 1 (is_z _ = true) => reflexivity : solve_pure.

(* denote - required for Get *)
#[export] Hint Extern 1 (denote (GetWType _ _) ?w = Some _) =>
  (eapply getwtype_denote ; reflexivity) : solve_pure.
#[export] Hint Extern 1 (rules_Get.denote _ _ = Some _) => reflexivity : solve_pure. (* unification fails if lhs has evars *)

(* Tests *)

Goal forall (r_t1 PC: RegName) `{MachineParameters}, exists r1 r2,
  decodeInstrW (encodeInstrW (Mov r_t1 PC)) = Mov r1 r2 ∧
  r1 = r_t1 ∧ r2 = inr PC.
Proof. do 2 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (WCap p b e a).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2: RegName), exists r1 r2,
  is_Get (GetB r_t2 r_t1) r1 r2 ∧
  r1 = r_t2 ∧ r2 = r_t1.
Proof. do 2 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall p b e a,
  ExecPCPerm p →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (WCap p b e (a ^+ 1)%a).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2 r_t3: RegName), exists r1 r2 r3,
  is_AddSubLt (Sub r_t2 r_t2 r_t3) r1 (inr r2) (inr r3) ∧
  r1 = r_t2 ∧ r2 = r_t2 ∧ r3 = r_t3.
Proof. do 3 eexists. repeat apply conj. solve_pure. all: reflexivity. Qed.

Goal forall (P: Prop), P → P. intros. solve_pure. Qed.
