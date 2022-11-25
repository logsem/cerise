From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_maps list countable.
From cap_machine Require Export addr_reg solve_addr stdpp_extra.

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

Definition Cap: Type :=
  Perm * Addr * Addr * Addr.

Inductive Word: Type :=
| WInt (z: Z)
| WCap (p: Perm) (b e a: Addr).

Inductive instr: Type :=
| Jmp (r: RegName)
| Jnz (r1 r2: RegName)
| Mov (dst: RegName) (src: Z + RegName)
| Load (dst src: RegName)
| Store (dst: RegName) (src: Z + RegName)
| Lt (dst: RegName) (r1 r2: Z + RegName)
| Add (dst: RegName) (r1 r2: Z + RegName)
| Sub (dst: RegName) (r1 r2: Z + RegName)
| Lea (dst: RegName) (r: Z + RegName)
| Restrict (dst: RegName) (r: Z + RegName)
| Subseg (dst: RegName) (r1 r2: Z + RegName)
| IsPtr (dst r: RegName)
| GetP (dst r: RegName)
| GetB (dst r: RegName)
| GetE (dst r: RegName)
| GetA (dst r: RegName)
| Fail
| Halt
| CAS (loc r1 r2: RegName)
.

(* Convenient coercion when writing instructions *)
Definition regn : RegName → (Z+RegName)%type := inr.
Definition cst : Z → (Z+RegName)%type := inl.
Coercion regn : RegName >-> sum.
Coercion cst : Z >-> sum.

(* Registers and memory: maps from register names/addresses to words *)

(* Definition CoreNum := 4. *)
Class CoreParameters := {
  coreNum : Z ;
  corePos : (coreNum >= 1)%Z;
}.

Definition CoreN `{CoreParameters} := finz coreNum.
Definition Reg `{CoreParameters} := gmap (CoreN * RegName) Word.
Definition Mem := gmap Addr Word.

(* Instance *)
Instance subseteq_reg `{CoreParameters} : SubsetEq Reg.
Proof.
  rewrite /Reg.
  apply map_subseteq.
Defined.

Instance insert_reg `{CoreParameters} : Insert (CoreN * RegName) Word Reg.
Proof.
  rewrite /Reg.
  apply map_insert.
Defined.

Instance lookup_reg `{CoreParameters} : Lookup (CoreN * RegName) Word Reg.
  rewrite /Reg.
  apply gmap_lookup.
Defined.

Instance finmap_reg `{CoreParameters} : FinMap (CoreN * RegName) (gmap (CoreN * RegName)).
  apply gmap_finmap.
Defined.

Instance union_reg {CP : CoreParameters} : Union (@Reg CP).
Proof.
  intros. rewrite /Reg.
  apply map_union.
Defined.

(* EqDecision instances *)

#[global] Instance perm_eq_dec : EqDecision Perm.
Proof. solve_decision. Defined.
#[global] Instance cap_eq_dec : EqDecision Cap.
Proof. solve_decision. Defined.
#[global] Instance word_eq_dec : EqDecision Word.
Proof. solve_decision. Defined.
#[global] Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.


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
  | WInt _ => false
  | WCap p' _ _ _ => isPerm p p'
  end.

Lemma isPermWord_cap_isPerm (w0:Word) p:
  isPermWord w0 p = true →
  ∃ p' b e a, w0 = WCap p' b e a ∧ isPerm p p' = true.
Proof.
  intros. destruct w0;[done|].
  destruct p; try done;
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
  | WCap _ _ _ _ => true
  | WInt n => Zneq_bool n 0
  end.

Definition cap_size (w : Word) : Z :=
  match w with
  | WCap _ b e _ => (e - b)%Z
  | _ => 0%Z
  end.

Definition is_cap (w: Word): bool :=
  match w with
  | WCap _ _ _ _ => true
  |  _ => false
  end.

(* Bound checking *)

Definition withinBounds b e a: bool :=
  (b <=? a)%a && (a <? e)%a.

Lemma withinBounds_true_iff b e a :
  withinBounds b e a = true ↔ (b <= a)%a ∧ (a < e)%a.
Proof.
  unfold withinBounds. solve_addr.
Qed.

Lemma withinBounds_le_addr b e a:
  withinBounds b e a = true →
  (b <= a)%a ∧ (a < e)%a.
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma isWithinBounds_bounds_alt b e (a0 a1 a2 : Addr) :
  withinBounds  b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma isWithinBounds_bounds_alt' b e (a0 a1 a2 : Addr) :
  withinBounds b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 < a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma le_addr_withinBounds b e a:
  (b <= a)%a → (a < e)%a →
  withinBounds b e a = true .
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma le_addr_withinBounds' b e a:
  (b <= a)%a ∧ (a < e)%a →
  withinBounds b e a = true .
Proof. intros [? ?]. rewrite withinBounds_true_iff //. Qed.


Lemma withinBounds_InBounds b e a :
  InBounds b e a →
  withinBounds b e a = true.
Proof.
  intros [? ?]. unfold withinBounds.
  apply andb_true_intro.
  split; [apply Z.leb_le;solve_addr | apply Z.ltb_lt;auto].
Qed.

Definition isWithin (n1 n2 b e: Addr) : bool :=
  ((b <=? n1) && (n2 <=? e))%a.

Lemma isWithin_implies a0 a1 b e:
  isWithin a0 a1 b e = true →
  (b <= a0 ∧ a1 <= e)%a.
Proof.
  rewrite /isWithin. solve_addr.
Qed.

Lemma isWithin_of_le a0 a1 b e:
  (b <= a0 ∧ a1 <= e)%a →
  isWithin a0 a1 b e = true.
Proof.
  rewrite /isWithin. solve_addr.
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
  - case_eq (match p with RX | RWX => true | _ => false end); intros.
    + destruct (finz_le_dec b a).
      * destruct (finz_lt_dec a e).
        { left. econstructor; simpl; eauto. by auto.
          destruct p; naive_solver. }
        { right. red; intro HH. inversion HH; subst. solve_addr. }
      * right. red; intros HH; inversion HH; subst. solve_addr.
    + right. red; intros HH; inversion HH; subst. naive_solver.
Qed.

Definition isCorrectPCb (w: Word): bool :=
  match w with
  | WInt _ => false
  | WCap p b e a =>
    (b <=? a)%a && (a <? e)%a &&
    (isPerm p RX || isPerm p RWX)
  end.

Lemma isCorrectPCb_isCorrectPC w :
  isCorrectPCb w = true ↔ isCorrectPC w.
Proof.
  rewrite /isCorrectPCb. destruct w.
  { split; try congruence. inversion 1. }
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

(* Useful instances *)

#[global] Instance perm_countable : Countable Perm.
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

#[global] Instance cap_countable : Countable Cap.
Proof.
  (* NB: this relies on the fact that cap_eq_dec has been Defined, because the
  eq decision we have for Cap has to match the one used in the conclusion of the
  lemma... *)
  apply prod_countable.
Defined.

#[global] Instance word_countable : Countable Word.
Proof.
  set (enc := fun w =>
       match w with
       | WInt z => GenNode 0 [GenLeaf (inl z)]
       | WCap p b e a => GenNode 1 [GenLeaf (inr (p, b, e, a))] end).
  set (dec := fun e =>
      match e with
      | GenNode 0 [GenLeaf (inl z)] => WInt z
      | GenNode 1 [GenLeaf (inr (p, b, e, a))] => WCap p b e a
      | _ => WInt 0 (* Dummy *) end ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Qed.

#[global] Instance word_inhabited: Inhabited Word := populate (WInt 0).
#[global] Instance addr_inhabited: Inhabited Addr := populate (@finz.FinZ MemNum 0%Z eq_refl eq_refl).


#[global] Instance instr_countable : Countable instr.
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
      | IsPtr dst r => GenNode 11 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetP dst r => GenNode 13 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetB dst r => GenNode 14 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetE dst r => GenNode 15 [GenLeaf (inl dst); GenLeaf (inl r)]
      | GetA dst r => GenNode 16 [GenLeaf (inl dst); GenLeaf (inl r)]
      | Fail => GenNode 17 []
      | Halt => GenNode 18 []
      | CAS loc r1 r2 => GenNode 19 [GenLeaf (inl loc); GenLeaf (inl r1) ; GenLeaf (inl r2)]
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
      | GenNode 11 [GenLeaf (inl dst); GenLeaf (inl r)] => IsPtr dst r
      | GenNode 13 [GenLeaf (inl dst); GenLeaf (inl r)] => GetP dst r
      | GenNode 14 [GenLeaf (inl dst); GenLeaf (inl r)] => GetB dst r
      | GenNode 15 [GenLeaf (inl dst); GenLeaf (inl r)] => GetE dst r
      | GenNode 16 [GenLeaf (inl dst); GenLeaf (inl r)] => GetA dst r
      | GenNode 17 [] => Fail
      | GenNode 18 [] => Halt
      | GenNode 19 [GenLeaf (inl loc); GenLeaf (inl r1); GenLeaf (inl r2)] => CAS loc r1 r2
      | _ => Fail (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

(* Set of all registers of core i *)
Definition all_registers_s_core `{CoreParameters} (i:CoreN) : gset (CoreN * RegName)
  := set_map (fun r => (i,r)) all_registers_s.

Lemma regmap_full_dom_i `{CP : CoreParameters} {A} (r : gmap (CoreN*RegName) A) (i : CoreN) :
  (∀ x : RegName, is_Some (r !! (i, x)) ∧ (∀ j : CoreN, i ≠ j → r !! (j, x) = None))
  -> dom  r = all_registers_s_core i.
Proof.
  intros Hfull.
  apply forall_and_distr in Hfull.
  rewrite /all_registers_s_core.
  destruct Hfull as [Hfull Hnone].
  apply (anti_symm subseteq) ; rewrite elem_of_subseteq.
  - intros rr Hr. (* apply all_registers_s_correct. *)
    destruct rr as [j rr].
    specialize (Hfull rr).
    specialize (Hnone rr j).
    destruct (decide (i = j)).
    { subst; eauto.
      apply elem_of_map_2.
      apply all_registers_s_correct.
    }
    { exfalso.
      rewrite <- elem_of_gmap_dom in Hr.
      destruct Hr.
      apply Hnone in n.
      rewrite H in n.
      done. }
  - intros rr Hr. rewrite -elem_of_gmap_dom.
    destruct rr as [j rr].
    specialize (Hfull rr).
    specialize (Hnone rr j).
    destruct (decide (i = j)).
    { subst; eauto. }
    { exfalso.
      apply elem_of_map_1 in Hr.
      destruct Hr as (? & ? & ?).
      simplify_eq. }
Qed.

Lemma all_registers_core_union_l `{CoreParameters} (i : CoreN) (r : RegName) :
  {[(i, r)]} ∪ (all_registers_s_core i) = (all_registers_s_core i).
Proof.
  apply (anti_symm subseteq); erewrite elem_of_subseteq.
  2: set_solver.
  rewrite /all_registers_s_core.
  set_solver.
Qed.
