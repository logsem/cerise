From Coq Require Import ssreflect Eqdep_dec.
From stdpp Require Import gmap fin_maps list countable.
From cap_machine Require Export addr_reg solve_addr.
From iris.proofmode Require Import proofmode.

(* Definition and auxiliary facts on capabilities, permissions and addresses.

   The [solve_cap_pure] tactic automates the proof of some of these facts (see
   solve_cap_pure.v on how to extend it). *)

(* Definitions: capabilities, machine words, machine instructions *)

Inductive Perm: Type :=
| O
| RO
| RW
| RX
| E
| RWX.

Definition SealPerms: Type := bool * bool. (* Permit_Seal x Permit_Unseal *)
Definition permit_seal (s : SealPerms) :=
  s.1.
Definition permit_unseal (s : SealPerms) :=
  s.2.

Inductive Sealable: Type :=
| SCap       (p : Perm) (b e a : Addr)
| SSealRange (sp : SealPerms) (ob oe oa : OType).

(* Having different syntactic categories here simplifies the definition of instructions later, but requires some duplication in defining bounds changes and lea on sealing ranges *)
Inductive Word: Type :=
| WInt (z : Z)
| WSealable (sb : Sealable)
| WSealed (ot : OType) (sb : Sealable).

Notation WCap p b e a := (WSealable (SCap p b e a)).
Notation WSealRange p b e a := (WSealable (SSealRange p b e a)).

Inductive instr: Type :=
| Jmp (r: RegName)
| Jnz (r1 r2: RegName)
| Mov (dst: RegName) (src: Z + RegName)
| Load (dst src: RegName)
| Store (dst: RegName) (src: Z + RegName)
| Lt (dst: RegName) (r1 r2: Z + RegName)
| Add (dst: RegName) (r1 r2: Z + RegName)
| Sub (dst: RegName) (r1 r2: Z + RegName)
| Mod (dst: RegName) (r1 r2: Z + RegName)
| HashConcat (dst: RegName) (r1 r2: Z + RegName)
| Hash (dst: RegName) (src: RegName)
| Lea (dst: RegName) (r: Z + RegName)
| Restrict (dst: RegName) (r: Z + RegName)
| Subseg (dst: RegName) (r1 r2: Z + RegName)
| GetB (dst r: RegName)
| GetE (dst r: RegName)
| GetA (dst r: RegName)
| GetP (dst r: RegName)
| GetWType (dst r : RegName) (* combine IsCap, GetTage and GetSealed all together into a unique encoding *)
| GetOType (dst r: RegName)
| Seal (dst r1 r2: RegName)
| UnSeal (dst r1 r2: RegName)
| EInit (r1 r2: RegName)
| EDeInit (r: RegName)
| EStoreId (dst src: RegName)
| IsUnique (dst src: RegName)
| Fail
| Halt.

(* Convenient coercion when writing instructions *)
Definition regn : RegName → (Z+RegName)%type := inr.
Definition cst : Z → (Z+RegName)%type := inl.
Coercion regn : RegName >-> sum.
Coercion cst : Z >-> sum.

(* Registers and memory: maps from register names/addresses to words *)

Definition Reg := gmap RegName Word.
Definition Mem := gmap Addr Word.

(* State involved in supporting enclaves *)
Definition TIndex := nat.
Definition EIdentity := Z. (* For now, we assume the hash to be unbounded *)
Definition ENum := nat. (* The max # of supported enclaves *)
Definition ETable := gmap TIndex EIdentity. (* Check sail impl. of CHERi-TrEE for how to get table index ? They don't have a table but a distinct memory region *)

(* EqDecision instances *)

Global Instance perm_eq_dec : EqDecision Perm.
Proof. solve_decision. Defined.
Global Instance sealb_eq_dec : EqDecision Sealable.
Proof. solve_decision. Qed.
Global Instance word_eq_dec : EqDecision Word.
Proof. solve_decision. Qed.
Global Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.

Ltac destruct_word w :=
  let z := fresh "z" in
  let c := fresh "c" in
  let sr := fresh "sr" in
  let sd := fresh "sd" in
  destruct w as [ z | [c | sr] | sd].

(***** Identifying parts of words *****)

(* Z <-> Word *)
Definition is_z (w : Word) : bool :=
  match w with
  | WInt z => true
  |  _ => false
  end.

(* Sealable <-> Word *)
Definition is_sealb (w : Word) : bool :=
  match w with
  | WSealable sb => true
  |  _ => false
  end.

(* Capability <-> Word *)
Definition is_cap (w : Word) : bool :=
  match w with
  | WCap p b e a => true
  |  _ => false
  end.

(* SealRange <-> Word *)
Definition is_sealr (w : Word) : bool :=
  match w with
  | WSealRange p b e a => true
  |  _ => false
  end.

(* Sealed <-> Word *)
Definition is_sealed (w : Word) : bool :=
  match w with
  | WSealed a sb => true
  |  _ => false
  end.

Definition is_sealed_with_o (w : Word) (o : OType) : bool :=
  match w with
  | WSealed o' sb => (o =? o')%ot
  | _ => false end.


(* non-E capability or range of seals *)
Definition is_mutable_range (w : Word) : bool:=
  match w with
  | WCap p _ _ _ => match p with | E  => false | _ => true end
  | WSealRange _ _ _ _ => true
  | _ => false end.

(* Auxiliary definitions to work on permissions *)
Definition executeAllowed (p: Perm): bool :=
  match p with
  | RWX | RX | E => true
  | _ => false
  end.

(* Uninitialized capabilities are neither read nor write allowed *)
Definition readAllowed (p: Perm): bool :=
  match p with
  | RWX | RX | RW | RO => true
  | _ => false
  end.

Definition writeAllowed (p: Perm): bool :=
  match p with
  | RWX | RW => true
  | _ => false
  end.

Lemma writeA_implies_readA p :
  writeAllowed p = true → readAllowed p = true.
Proof. destruct p; auto. Qed.

Definition isPerm p p' := @bool_decide _ (perm_eq_dec p p').

Lemma isPerm_refl p : isPerm p p = true.
Proof. destruct p; auto. Qed.
Lemma isPerm_ne p p' : p ≠ p' → isPerm p p' = false.
Proof. intros Hne. destruct p,p'; auto; congruence. Qed.

Definition isPermWord (w : Word) (p : Perm): bool :=
  match w with
  | WCap p' _ _ _  => isPerm p p'
  | _ => false
  end.

Lemma isPermWord_cap_isPerm (w0:Word) p:
  isPermWord w0 p = true →
  ∃ p' b e a, w0 = WCap p' b e a ∧ isPerm p p' = true.
Proof.
  intros Hp. rewrite /isPermWord in Hp.
  destruct_word w0; try congruence.
  eexists _, _, _, _; split; eauto.
Qed.

Definition ExecPCPerm p :=
  p = RX ∨ p = RWX.

Lemma ExecPCPerm_RX: ExecPCPerm RX.
Proof. left; auto. Qed.

Lemma ExecPCPerm_RWX: ExecPCPerm RWX.
Proof. right; auto. Qed.

(* perm-flows-to: the permission lattice.
   "x flows to y" if x is lower than y in the lattice.
  *)

Definition PermFlowsTo (p1 p2: Perm): bool :=
  match p1 with
  | O => true
  | E => match p2 with
        | E | RX | RWX => true
        | _ => false
        end
  | RX => match p2 with
         | RX | RWX => true
         | _ => false
         end
  | RWX => match p2 with
          | RWX => true
          | _ => false
          end
  | RO => match p2 with
         | RO | RX | RW | RWX => true
         | _ => false
         end
  | RW => match p2 with
         | RW | RWX => true
         | _ => false
         end
  end.

Definition PermFlowsToCap (p: Perm) (w: Word) : bool :=
  match w with
  | WCap p' _ _ _ => PermFlowsTo p p'
  | _ => false
  end.

(* Sanity check *)
Lemma PermFlowsToTransitive:
  transitive _ PermFlowsTo.
Proof.
  red; intros; destruct x; destruct y; destruct z; try congruence; auto.
Qed.

(* Sanity check 2 *)
Lemma PermFlowsToReflexive:
  forall p, PermFlowsTo p p = true.
Proof.
  intros; destruct p; auto.
Qed.

(* perm-flows-to as a predicate *)
Definition PermFlows : Perm → Perm → Prop :=
  λ p1 p2, PermFlowsTo p1 p2 = true.

Lemma PermFlows_refl : ∀ p, PermFlows p p.
Proof.
  rewrite /PermFlows /PermFlowsTo.
  destruct p; auto.
Qed.

Lemma PermFlows_trans P1 P2 P3 :
  PermFlows P1 P2 → PermFlows P2 P3 → PermFlows P1 P3.
Proof.
  intros Hp1 Hp2. rewrite /PermFlows /PermFlowsTo.
  destruct P1,P3,P2; simpl; auto; contradiction.
Qed.

Lemma PermFlowsToPermFlows p p':
  PermFlowsTo p p' <-> PermFlows p p'.
Proof.
  rewrite /PermFlows; split; intros; auto.
  destruct (Is_true_reflect (PermFlowsTo p p')); auto.
Qed.

Lemma readAllowed_nonO p p' :
  PermFlows p p' → readAllowed p = true → p' ≠ O.
Proof.
  intros Hfl' Hra. destruct p'; auto. destruct p; inversion Hfl'. inversion Hra.
Qed.

Lemma writeAllowed_nonO p p' :
  PermFlows p p' → writeAllowed p = true → p' ≠ O.
Proof.
  intros Hfl' Hra. apply writeA_implies_readA in Hra. by apply (readAllowed_nonO p p').
Qed.

Lemma PCPerm_nonO p p' :
  PermFlows p p' → p = RX ∨ p = RWX → p' ≠ O.
Proof.
  intros Hfl Hvpc. destruct p'; auto. destruct p; inversion Hfl.
  destruct Hvpc as [Hcontr | Hcontr]; inversion Hcontr.
Qed.

Lemma ExecPCPerm_flows_to p p':
  PermFlows p p' →
  ExecPCPerm p →
  ExecPCPerm p'.
Proof.
  intros H [-> | ->]; cbn in H.
  { destruct p'; cbn in H; try by inversion H; constructor. }
  { destruct p'; try by inversion H; constructor. }
Qed.

Lemma ExecPCPerm_not_E p :
  ExecPCPerm p →
  p ≠ E.
Proof.
  intros [H|H] ->; inversion H.
Qed.

Lemma ExecPCPerm_readAllowed p :
  ExecPCPerm p →
  readAllowed p = true.
Proof.
  intros [-> | ->]; reflexivity.
Qed.

Definition SealPermFlowsTo (s1 s2 : SealPerms): bool :=
  (if permit_seal(s1) then permit_seal(s2) else true) &&
  (if permit_unseal(s1) then permit_unseal(s2) else true).

(* Sanity check *)
Lemma SealPermFlowsToTransitive:
  transitive _ SealPermFlowsTo.
Proof.
  red; intros. unfold SealPermFlowsTo in *. repeat destruct (permit_seal _); repeat destruct (permit_unseal _); auto.
Qed.

(* Sanity check 2 *)
Lemma SealPermFlowsToReflexive:
  forall p, SealPermFlowsTo p p = true.
Proof.
  intros; unfold SealPermFlowsTo. destruct (permit_seal _), (permit_unseal _); auto.
Qed.

(* Sanity check 3 *)
Lemma SealPermFlows_refl : ∀ p, SealPermFlowsTo p p = true.
Proof.
  intros; rewrite /SealPermFlowsTo. destruct (permit_seal _), (permit_unseal _); auto.
Qed.

(* Helper definitions for capabilities *)

(* Turn E into RX into PC after a jump *)
Definition updatePcPerm (w: Word): Word :=
  match w with
  | WCap E b e a => WCap RX b e a
  | _ => w
  end.

Lemma updatePcPerm_cap_non_E p b e a :
  p ≠ E →
  updatePcPerm (WCap p b e a) = WCap p b e a.
Proof.
  intros HnE. cbn. destruct p; auto. contradiction.
Qed.

Definition nonZero (w: Word): bool :=
  match w with
  | WInt n => Zneq_bool n 0
  | _ => true
  end.

Definition cap_size (w : Word) : Z :=
  match w with
  | WCap _ b e _ => (e - b)%Z
  | _ => 0%Z
  end.

(* Bound checking for both otypes and addresses *)

Definition withinBounds {z} (b e a : finz z): bool :=
  (b <=? a)%f && (a <? e)%f.

Lemma withinBounds_true_iff {z} (b e a : finz z) :
  withinBounds b e a = true ↔ (b <= a)%f ∧ (a < e)%f.
Proof.
  unfold withinBounds. solve_addr.
Qed.

Lemma withinBounds_le_addr {z} (b e a : finz z):
  withinBounds b e a = true →
  (b <= a)%f ∧ (a < e)%f.
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma withinBounds_in_seq_1 {z} (b e a : finz z) :
  withinBounds b e a = true -> a ∈ finz.seq_between b e.
  Proof.
    intros Hbounds.
    by apply withinBounds_true_iff, elem_of_finz_seq_between in Hbounds.
Qed.

Lemma withinBounds_in_seq_2 {z} (b e a : finz z) :
  a ∈ finz.seq_between b e -> withinBounds b e a = true.
Proof.
  intros Hbounds.
  apply withinBounds_true_iff.
  apply elem_of_finz_seq_between in Hbounds.
  solve_addr.
Qed.

Lemma withinBounds_in_seq {z} (b e a : finz z) :
  a ∈ finz.seq_between b e <-> withinBounds b e a = true.
Proof.
  split ; intros ; by [apply withinBounds_in_seq_2 | apply withinBounds_in_seq_1].
Qed.

Lemma isWithinBounds_bounds_alt {z} b e (a0 a1 a2 : finz z) :
  withinBounds  b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma isWithinBounds_bounds_alt' {z} b e (a0 a1 a2 : finz z) :
  withinBounds b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 < a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma le_addr_withinBounds {z} (b e a : finz z):
  (b <= a)%f → (a < e)%f →
  withinBounds b e a = true .
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma le_addr_withinBounds' {z} (b e a : finz z):
  (b <= a)%f ∧ (a < e)%f →
  withinBounds b e a = true .
Proof. intros [? ?]. rewrite withinBounds_true_iff //. Qed.

Lemma withinBounds_InBounds {z} (b e a : finz z) :
  InBounds b e a →
  withinBounds b e a = true.
Proof.
  intros [? ?]. unfold withinBounds.
  apply andb_true_intro.
  split; [apply Z.leb_le;solve_addr | apply Z.ltb_lt;auto].
Qed.

Definition isWithin {z} (n1 n2 b e: finz z) : bool :=
  ((b <=? n1) && (n2 <=? e))%f.

Lemma isWithin_refl {z} (b e : finz z) : isWithin b e b e.
Proof.
  rewrite /isWithin Is_true_true; solve_finz.
Qed.

Definition isWithinCap (c: Word) (b e: finz MemNum) : bool :=
  match c with
  | WCap _ n1 n2 _ => isWithin n1 n2 b e
  | _ => false
  end.

Lemma isWithin_implies {z} (a0 a1 b e : finz z):
  isWithin a0 a1 b e = true →
  (b <= a0 ∧ a1 <= e)%f.
Proof.
  rewrite /isWithin. solve_addr.
Qed.

Lemma isWithin_of_le {z} (a0 a1 b e : finz z):
  (b <= a0 ∧ a1 <= e)%f →
  isWithin a0 a1 b e = true.
Proof.
  rewrite /isWithin. solve_addr.
Qed.

(* TODO move in finz *)
Lemma finz_incr_minus_id
  {finz_bound : Z}
  (f : finz finz_bound) (z : Z)
  (finz_lt : (z <? finz_bound)%Z = true)
  (finz_nonneg : (0 <=? z)%Z = true) :
  (f + (z - f))%f = Some (finz.FinZ z finz_lt finz_nonneg).
Proof.
  induction z; cbn in *; try done.
  - replace (0 - f)%Z with (-f)%Z; solve_finz.
  - destruct (Z.pos p - f)%Z eqn:H.
    + assert ( Z.pos p = f ) by lia.
      solve_finz.
    + assert ( Z.pos p = f + Z.pos p0)%Z by lia.
      solve_finz.
    + assert ( Z.pos p = f + Z.neg p0)%Z by lia.
      solve_finz.
Qed.

Lemma finz_dist_add
  {finz_bound : Z} (f1 : finz finz_bound) (n : nat) :
  is_Some (f1 + n)%f → finz.dist f1 (f1 ^+ n)%f = n.
Proof.
  generalize dependent f1.
  induction n; intros f1 [f1' Hf1'].
  - apply finz_dist_0; solve_finz.
  - rewrite finz_dist_S; last solve_finz.
    f_equal.
    replace (f1 ^+ S n)%f with ((f1 ^+ 1) ^+n)%f by solve_finz.
    rewrite IHn; solve_finz.
Qed.

(* Some lemma's to link the implementations of finz.seq_between and withinBounds *)

Lemma finz_0_dist (finz_bound : Z) (f1 f2 : finz finz_bound):
  finz.dist f1 f2 = 0 → (f2 <= f1)%f.
Proof. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_empty_seq_between:
  ∀ (finz_bound : Z) (f1 f2 : finz finz_bound),
    finz.seq_between f1 f2 = [] → (f2 <= f1)%f.
Proof. intros *. rewrite /finz.seq_between /finz.seq.
  destruct (finz.dist f1 f2) eqn:Heq.
  by apply finz_0_dist in Heq.
  intro HFalse; inversion HFalse.
Qed.

Lemma finz_cons_hd (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
  a :: l = finz.seq_between a0 e0 → a = a0.
Proof.
  intros Heql.
  rewrite /finz.seq_between /finz.seq in Heql. destruct (finz.dist a0 e0); inversion Heql; auto. Qed.

Lemma finz_cons_tl (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
  a :: l = finz.seq_between a0 e0 → ∃ a1, (a0 + 1 = Some a1)%f ∧ l = finz.seq_between a1 e0.
Proof.
  intros Heql.
  assert (a0 < e0)%f as Hlt. {
    rewrite /finz.seq_between /finz.seq in Heql.
    destruct (decide (a0 < e0)%f) as [Hlt | Hnlt]; first auto.
    assert (finz.dist a0 e0 = 0) as HFalse.
    {  apply finz_dist_0; solve_finz. }
    rewrite HFalse /= in Heql. by exfalso. }
  rewrite finz_seq_between_cons in Heql; auto.
  injection Heql as _ Hl.
  assert (a0 + 1 = Some (a0 ^+ 1))%f as Heq. { solve_finz. }
  eexists ; eauto.
Qed.

Lemma seq_between_dist_Some {z : Z} (b0 e0 a0 : finz z):
  withinBounds b0 e0 a0 = true
  → finz.seq_between b0 e0 !! finz.dist b0 a0 = Some a0.
Proof.
  remember (finz.seq_between b0 e0) as l. revert Heql. generalize b0.
  induction l.
  - intros b1 Heql Hwb.
    symmetry in Heql; apply finz_empty_seq_between in Heql.
    rewrite /withinBounds in Hwb.
    exfalso. solve_finz.
  - intros b1 Heql Hwb.
    destruct (decide (b1 = a0)%f) as [-> | ].
    + apply finz_cons_hd in Heql as ->.
      rewrite /finz.dist. by rewrite -Zminus_diag_reverse /=.
    + assert (b1 < a0)%f as Hlt.
      {rewrite /withinBounds in Hwb. solve_finz. }
      apply finz_cons_tl in Heql as (a1' & Hp1 & Hleq).
      assert (withinBounds a1' e0 a0 = true) as Hwb'. { unfold withinBounds in *; solve_finz. }
      specialize (IHl _ Hleq Hwb') as IHl.
      rewrite lookup_cons_ne_0.
      2 : { rewrite /finz.dist. solve_finz. }
      rewrite -IHl; apply (f_equal (λ a, l !! a)).
      rewrite /finz.dist. solve_finz.
Qed.


(* isCorrectPC: valid capabilities for PC *)

Inductive isCorrectPC: Word → Prop :=
| isCorrectPC_intro:
    forall p (b e a : Addr),
      (b <= a < e)%a →
      p = RX \/ p = RWX →
      isCorrectPC (WCap p b e a).

Lemma isCorrectPC_dec:
  forall w, { isCorrectPC w } + { not (isCorrectPC w) }.
Proof.
  destruct w.
  - right. red; intros H. inversion H.
  - destruct sb as [p b e a | ].
    -- case_eq (match p with RX | RWX => true | _ => false end); intros.
      + destruct (finz_le_dec b a).
        * destruct (finz_lt_dec a e).
          { left. econstructor; simpl; eauto. by auto.
            destruct p; naive_solver. }
          { right. red; intro HH. inversion HH; subst. solve_addr. }
        * right. red; intros HH; inversion HH; subst. solve_addr.
      + right. red; intros HH; inversion HH; subst. naive_solver.
    -- right. red; intros H. inversion H.
 - right. red; intros H. inversion H.
Qed.

Definition isCorrectPCb (w: Word): bool :=
  match w with
  | WCap p b e a =>
    (b <=? a)%a && (a <? e)%a &&
    (isPerm p RX || isPerm p RWX)
  | _ => false
  end.

Lemma isCorrectPCb_isCorrectPC w :
  isCorrectPCb w = true ↔ isCorrectPC w.
Proof.
  rewrite /isCorrectPCb. destruct_word w.
  1,3,4 : split; try congruence; inversion 1.
  { rewrite !andb_true_iff !orb_true_iff !Z.leb_le !Z.ltb_lt.
    rewrite /isPerm !bool_decide_eq_true.
    split.
    { intros [? ?]. constructor. solve_addr. naive_solver. }
    { inversion 1; subst. split. solve_addr. naive_solver. } }
Qed.

Lemma isCorrectPCb_nisCorrectPC w :
  isCorrectPCb w = false ↔ ¬ isCorrectPC w.
Proof.
  destruct (isCorrectPCb w) eqn:HH.
  { apply isCorrectPCb_isCorrectPC in HH. split; congruence. }
  { split; auto. intros _. intros ?%isCorrectPCb_isCorrectPC. congruence. }
Qed.

Lemma isCorrectPC_ra_wb pc_p pc_b pc_e pc_a :
  isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
  readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a).
Proof.
  intros. inversion H; subst.
  - destruct H2. apply andb_prop_intro. split.
    + destruct H5,pc_p; inversion H1; try inversion H2; auto; try congruence.
    + apply andb_prop_intro.
      split; apply Is_true_eq_left; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma not_isCorrectPC_perm p b e a :
  p ≠ RX ∧ p ≠ RWX → ¬ isCorrectPC (WCap p b e a).
Proof.
  intros (Hrx & Hrwx).
  intros Hvpc. inversion Hvpc;
    destruct H4 as [Hrx' | Hrwx']; contradiction.
Qed.

Lemma not_isCorrectPC_bounds p b e a :
 ¬ (b <= a < e)%a → ¬ isCorrectPC (WCap p b e a).
Proof.
  intros Hbounds.
  intros Hvpc. inversion Hvpc.
  by exfalso.
Qed.

Lemma isCorrectPC_bounds p b e (a0 a1 a2 : Addr) :
  isCorrectPC (WCap p b e a0) →
  isCorrectPC (WCap p b e a2) →
  (a0 ≤ a1 < a2)%Z → isCorrectPC (WCap p b e a1).
Proof.
  intros Hvpc0 Hvpc2 [Hle Hlt].
  inversion Hvpc0.
  - subst; econstructor; auto.
    inversion Hvpc2; subst.
    + destruct H1 as [Hb He]. destruct H2 as [Hb2 He2]. split.
      { apply Z.le_trans with a0; auto. }
      { apply Z.lt_trans with a2; auto. }
Qed.

Lemma isCorrectPC_bounds_alt p b e (a0 a1 a2 : Addr) :
  isCorrectPC (WCap p b e a0)
  → isCorrectPC (WCap p b e a2)
  → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
  → isCorrectPC (WCap p b e a1).
Proof.
  intros Hvpc0 Hvpc2 [Hle0 Hle2].
  apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
  - apply isCorrectPC_bounds with a0 a2; auto.
  - apply finz_to_z_eq in Heq2. rewrite Heq2. auto.
Qed.

Lemma isCorrectPC_withinBounds p b e a :
  isCorrectPC (WCap p b e a) →
  withinBounds b e a = true.
Proof.
  intros HH. inversion HH; subst.
  rewrite /withinBounds !andb_true_iff Z.leb_le Z.ltb_lt. auto.
Qed.

Lemma isCorrectPC_le_addr p b e a :
  isCorrectPC (WCap p b e a) →
  (b <= a)%a ∧ (a < e)%a.
Proof.
  intros HH. by eapply withinBounds_le_addr, isCorrectPC_withinBounds.
Qed.

Lemma correctPC_nonO p p' b e a :
  PermFlows p p' → isCorrectPC (WCap p b e a) → p' ≠ O.
Proof.
  intros Hfl HcPC. inversion HcPC. by apply (PCPerm_nonO p p').
Qed.

Lemma in_range_is_correctPC p b e a b' e' :
  isCorrectPC (WCap p b e a) →
  (b' <= b)%a ∧ (e <= e')%a →
  (b' <= a)%a ∧ (a < e')%a.
Proof.
  intros Hvpc [Hb He].
  inversion Hvpc; simplify_eq. solve_addr.
Qed.

Lemma isCorrectPC_ExecPCPerm_InBounds p b e a :
  ExecPCPerm p →
  InBounds b e a →
  isCorrectPC (WCap p b e a).
Proof.
  unfold ExecPCPerm, InBounds. intros. constructor; eauto.
Qed.

(* Helper tactics *)

Ltac destruct_pair_l c n :=
  match eval compute in n with
  | 0 => idtac
  | _ => let sndn := fresh c in
        destruct c as (c,sndn); destruct_pair_l c (pred n)
  end.

(* Useful instances *)

Global Instance perm_countable : Countable Perm.
Proof.
  set encode := fun p => match p with
    | O => 1
    | RO => 2
    | RW => 3
    | RX => 4
    | E => 5
    | RWX => 6
    end%positive.
  set decode := fun n => match n with
    | 1 => Some O
    | 2 => Some RO
    | 3 => Some RW
    | 4 => Some RX
    | 5 => Some E
    | 6 => Some RWX
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Defined.

Global Instance sealable_countable : Countable Sealable.
Proof.
  set (enc := fun sb =>
       match sb with
       | SCap p b e a => inl (p,b,e,a)
       | SSealRange p b e a => inr (p,b,e,a) end
      ).
  set (dec := fun e =>
       match e with
       | inl (p,b,e,a) => SCap p b e a
       | inr (p,b,e,a) => SSealRange p b e a end
      ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

(* Same here *)
Global Instance word_countable : Countable Word.
Proof.
  set (enc := fun w =>
      match w with
      | WInt z => inl z
      | WSealable sb => inr (inl sb)
      | WSealed x x0 => inr (inr (x, x0))
      end ).
  set (dec := fun e =>
      match e with
      | inl z => WInt z
      | inr (inl sb) => WSealable sb
      | inr (inr (x, x0)) => WSealed x x0
      end ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Qed.

Global Instance word_inhabited: Inhabited Word := populate (WInt 0).
Global Instance addr_inhabited: Inhabited Addr := populate (@finz.FinZ MemNum 0%Z eq_refl eq_refl).
Global Instance otype_inhabited: Inhabited OType := populate (@finz.FinZ ONum 0%Z eq_refl eq_refl).
(* Global Instance enum_inhabited: Inhabited ENum := populate (@finz.FinZ MaxENum 0%Z eq_refl eq_refl). *)
(* Global Instance tindex_inhabited: Inhabited TIndex := populate (@finz.FinZ TableSize 0%Z eq_refl eq_refl). *)
Global Instance etable_inhabited: Inhabited ETable. Proof. solve [typeclasses eauto]. Defined.

Global Instance instr_countable : Countable instr.
Proof.

  set (enc := fun e =>
      match e with
      | Jmp r => GenNode 0 [GenLeaf (inl r)]
      | Jnz r1 r2 => GenNode 1 [GenLeaf (inl r1); GenLeaf (inl r2)]
      | Mov dst src => GenNode 2 [GenLeaf (inl dst); GenLeaf (inr src)]
      | Load dst src => GenNode 3 [GenLeaf (inl dst); GenLeaf (inl src)]
      | Store dst src => GenNode 4 [GenLeaf (inl dst); GenLeaf (inr src)]
      | Lt dst r1 r2 => GenNode 5 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Add dst r1 r2 => GenNode 6 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Sub dst r1 r2 => GenNode 7 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Lea dst r => GenNode 8 [GenLeaf (inl dst); GenLeaf (inr r)]
      | Restrict dst r => GenNode 9 [GenLeaf (inl dst); GenLeaf (inr r)]
      | Subseg dst r1 r2 => GenNode 10 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | GetB dst r => GenNode 11 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetE dst r => GenNode 12 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetA dst r => GenNode 13 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetP dst r => GenNode 14 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetOType dst r => GenNode 15 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetWType dst r => GenNode 16 [GenLeaf (inl dst); GenLeaf (inl r)]
      | Seal dst r1 r2 => GenNode 17 [GenLeaf (inl dst); GenLeaf (inl r1); GenLeaf (inl r2)]
      | UnSeal dst r1 r2 => GenNode 18 [GenLeaf (inl dst); GenLeaf (inl r1); GenLeaf (inl r2)]
      | EInit r1 r2 => GenNode 19 [GenLeaf (inl r1);GenLeaf (inl r2)]
      | EDeInit r => GenNode 20 [GenLeaf (inl r)]
      | EStoreId dst src => GenNode 21 [GenLeaf (inl dst); GenLeaf (inl src)]
      | IsUnique dst src => GenNode 22 [GenLeaf (inl dst); GenLeaf (inl src)]
      | Fail => GenNode 23 []
      | Halt => GenNode 24 []
      | Mod dst r1 r2 => GenNode 25 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | HashConcat dst r1 r2 => GenNode 26 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Hash dst src => GenNode 27 [GenLeaf (inl dst); GenLeaf (inl src)]
      end).
  set (dec := fun e =>
      match e with
      | GenNode 0 [GenLeaf (inl r)] => Jmp r
      | GenNode 1 [GenLeaf (inl r1); GenLeaf (inl r2)] => Jnz r1 r2
      | GenNode 2 [GenLeaf (inl dst); GenLeaf (inr src)] => Mov dst src
      | GenNode 3 [GenLeaf (inl dst); GenLeaf (inl src)] => Load dst src
      | GenNode 4 [GenLeaf (inl dst); GenLeaf (inr src)] => Store dst src
      | GenNode 5 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => Lt dst r1 r2
      | GenNode 6 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => Add dst r1 r2
      | GenNode 7 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => Sub dst r1 r2
      | GenNode 8 [GenLeaf (inl dst); GenLeaf (inr r)] => Lea dst r
      | GenNode 9 [GenLeaf (inl dst); GenLeaf (inr r)] => Restrict dst r
      | GenNode 10 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => Subseg dst r1 r2
      | GenNode 11 [GenLeaf (inl dst); GenLeaf (inl r)] => GetB dst r
      | GenNode 12 [GenLeaf (inl dst); GenLeaf (inl r)] => GetE dst r
      | GenNode 13 [GenLeaf (inl dst); GenLeaf (inl r)] => GetA dst r
      | GenNode 14 [GenLeaf (inl dst); GenLeaf (inl r)] => GetP dst r
      | GenNode 15 [GenLeaf (inl dst); GenLeaf (inl r)] => GetOType dst r
      | GenNode 16 [GenLeaf (inl dst); GenLeaf (inl r)] => GetWType dst r
      | GenNode 17 [GenLeaf (inl dst); GenLeaf (inl r1); GenLeaf (inl r2)] => Seal dst r1 r2
      | GenNode 18 [GenLeaf (inl dst); GenLeaf (inl r1); GenLeaf (inl r2)] => UnSeal dst r1 r2
      | GenNode 19 [GenLeaf (inl r1);GenLeaf (inl r2)] => EInit r1 r2
      | GenNode 20 [GenLeaf (inl r)] => EDeInit r
      | GenNode 21 [GenLeaf (inl dst); GenLeaf (inl src)] => EStoreId dst src
      | GenNode 22 [GenLeaf (inl dst); GenLeaf (inl src)] => IsUnique dst src
      | GenNode 23 [] => Fail
      | GenNode 24 [] => Halt
      | GenNode 25 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => Mod dst r1 r2
      | GenNode 26 [GenLeaf (inl dst); GenLeaf (inr r1); GenLeaf (inr r2)] => HashConcat dst r1 r2
      | GenNode 27 [GenLeaf (inl dst); GenLeaf (inl src)] => Hash dst src
      | _ => Fail (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

Global Instance reg_finite : finite.Finite RegName.
Proof. apply (finite.enc_finite (λ r : RegName, match r with
                                                | PC => S RegNum
                                                | addr_reg.R n fin => n
                                                end)
                (λ n : nat, match n_to_regname n with | Some r => r | None => PC end)
                (S (S RegNum))).
       - intros x. destruct x;auto.
         unfold n_to_regname.
         destruct (Nat.le_dec n RegNum).
         + do 2 f_equal. apply eq_proofs_unicity. decide equality.
         + exfalso. by apply (Nat.leb_le n RegNum) in fin.
       - intros x.
         + destruct x;[lia|]. apply Nat.leb_le in fin. lia.
       - intros i Hlt. unfold n_to_regname.
         destruct (Nat.le_dec i RegNum);auto.
         lia.
Defined.

Lemma rewrite_invert_match_E {prop: Type} (P1 P2 : prop) (p : Perm) :
  p ≠ E ->
  (match p with
   | E => P1
   | _ => P2
   end) = P2.
Proof.
  intros.
  destruct p ; cbn in *; done.
Qed.
