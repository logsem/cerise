From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From Coq.micromega Require Import ZifyClasses.
From stdpp Require Import gmap fin_maps list.
From Coq Require Import ssreflect.
From cap_machine Require Import stdpp_extra.

(* We assume a fixed set of registers, and a finite set of memory addresses.

   The exact size of the address space does not matter, it could be made a
   parameter of the machine.
*)

Definition RegNum: nat := 31.
Definition MemNum: Z := 2000000.

(* ---------------------------------- Registers ----------------------------------------*)

Inductive RegName: Type :=
| PC
| R (n: nat) (fin: n <=? RegNum = true).

Global Instance reg_eq_dec : EqDecision RegName.
Proof. intros r1 r2.  destruct r1,r2; [by left | by right | by right |].
       destruct (nat_eq_dec n n0).
       + subst n0. left.
         assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
         { intros. apply eq_proofs_unicity.
           intros; destruct x; destruct y; auto. }
         rewrite (H _ _ _ fin fin0). reflexivity.
       + right. congruence.
Defined.

Lemma reg_eq_sym (r1 r2 : RegName) : r1 ≠ r2 → r2 ≠ r1. Proof. auto. Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  match nat_le_dec n RegNum with left _ => Some (R n _) | right _ => None end.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
Defined.

Global Instance reg_countable : Countable RegName.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl ()
                               | R n fin => inr n
                               end ;
            decode n := match (decode n) with
                        | Some (inl ()) => Some PC
                        | Some (inr n) => n_to_regname n
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (nat_le_dec n RegNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Nat.leb_le n RegNum) in fin.
Defined.

(* Instances for [zify]: make [lia] work on registers *)
(* TODO: separate the proof parts into lemmas *)

Definition Z_of_regname (r: RegName): Z.
  destruct r. exact 0.
  exact (S n).
Defined.

Instance RegName_InjTyp : InjTyp RegName Z.
  refine (mkinj _ _ Z_of_regname (fun n => n <= RegNum + 1)%Z _).
  intros [|]. cbn. lia. cbn. apply Nat.leb_le in fin. lia.
Defined.
Add Zify InjTyp RegName_InjTyp.

Instance Op_RegName_eq : BinRel (@eq RegName).
  refine ({| TR := @eq Z; TRInj := _ |}).
  cbn. intros r1 r2. split.
  - intros ->; eauto.
  - destruct r1; destruct r2; eauto; cbn; try apply Nat.leb_le in fin; try lia.
    intros ->%Nat2Z.inj%eq_add_S.
    f_equal. apply eq_proofs_unicity. intros [|] [|]; eauto.
Defined.
Add Zify BinRel Op_RegName_eq.

(* Names for registers *)
Definition r_t0 : RegName := R 0 eq_refl.
Definition r_t1 : RegName := R 1 eq_refl.
Definition r_t2 : RegName := R 2 eq_refl.
Definition r_t3 : RegName := R 3 eq_refl.
Definition r_t4 : RegName := R 4 eq_refl.
Definition r_t5 : RegName := R 5 eq_refl.
Definition r_t6 : RegName := R 6 eq_refl.
Definition r_t7 : RegName := R 7 eq_refl.
Definition r_t8 : RegName := R 8 eq_refl.
Definition r_t9 : RegName := R 9 eq_refl.
Definition r_t10 : RegName := R 10 eq_refl.
Definition r_t11 : RegName := R 11 eq_refl.
Definition r_t12 : RegName := R 12 eq_refl.
Definition r_t13 : RegName := R 13 eq_refl.
Definition r_t14 : RegName := R 14 eq_refl.
Definition r_t15 : RegName := R 15 eq_refl.
Definition r_t16 : RegName := R 16 eq_refl.
Definition r_t17 : RegName := R 17 eq_refl.
Definition r_t18 : RegName := R 18 eq_refl.
Definition r_t19 : RegName := R 19 eq_refl.
Definition r_t20 : RegName := R 20 eq_refl.
Definition r_t21 : RegName := R 21 eq_refl.
Definition r_t22 : RegName := R 22 eq_refl.
Definition r_t23 : RegName := R 23 eq_refl.
Definition r_t24 : RegName := R 24 eq_refl.
Definition r_t25 : RegName := R 25 eq_refl.
Definition r_t26 : RegName := R 26 eq_refl.
Definition r_t27 : RegName := R 27 eq_refl.
Definition r_t28 : RegName := R 28 eq_refl.
Definition r_t29 : RegName := R 29 eq_refl.
Definition r_t30 : RegName := R 30 eq_refl.
Definition r_t31 : RegName := R 31 eq_refl.

(* A list of all general purpuse registers (if regnum=31) *)
Definition all_registers : list RegName :=
  [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;r_t7;r_t8;r_t9;r_t10;r_t11;r_t12;r_t13;
     r_t14;r_t15;r_t16;r_t17;r_t18;r_t19;r_t20;r_t21;r_t22;r_t23;r_t24;r_t25;r_t26;
       r_t27;r_t28;r_t29;r_t30;r_t31;PC].

(* Set of all registers *)
Definition all_registers_s : gset RegName := list_to_set all_registers.

Lemma all_registers_NoDup :
  NoDup all_registers.
Proof.
  unfold all_registers.
  repeat (
    apply NoDup_cons_2;
    first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
  ).
  by apply NoDup_nil.
Qed.

(* Spec for all_registers *)

Lemma all_registers_correct r1 :
  r1 ∈ all_registers.
Proof.
  rewrite /all_registers.
  destruct r1.
  - do 32 (apply elem_of_cons; right).
      by apply elem_of_list_singleton.
  - induction n.
    + apply elem_of_cons; left.
      apply f_equal. apply eq_proofs_unicity. decide equality.
    + apply elem_of_list_lookup_2 with (S n).
      repeat (destruct n;
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
      simpl in *. inversion fin.
Qed.

Lemma all_registers_s_correct r:
  r ∈ all_registers_s.
Proof.
  rewrite /all_registers_s elem_of_list_to_set.
  apply all_registers_correct.
Qed.

Lemma all_registers_correct_sub r : NoDup r → r ⊆+ all_registers.
Proof.
  intros Hdup.
  apply NoDup_submseteq;auto. intros r' Hin.
  apply all_registers_correct.
Qed.

Instance setunfold_all_regs:
  forall x, SetUnfoldElemOf x all_registers_s True.
Proof.
  intros. constructor. split; auto.
  intro. eapply all_registers_s_correct.
Qed.

Lemma all_registers_union_l s :
  s ∪ all_registers_s = all_registers_s.
Proof.
  eapply (anti_symm _). 2: set_solver.
  rewrite elem_of_subseteq. intros ? _.
  apply all_registers_s_correct.
Qed.

Lemma all_registers_union_r s :
  all_registers_s ∪ s = all_registers_s.
Proof. rewrite union_comm_L. apply all_registers_union_l. Qed.

Lemma all_registers_subseteq s :
  s ⊆ all_registers_s.
Proof.
  rewrite elem_of_subseteq. intros ? _. apply all_registers_s_correct.
Qed.

Lemma regmap_full_dom {A} (r: gmap RegName A):
  (∀ x, is_Some (r !! x)) →
  dom (gset RegName) r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm _); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite -elem_of_gmap_dom. apply Hfull.
Qed.

(* -------------------------------- Memory addresses -----------------------------------*)

Inductive Addr: Type :=
| A (z : Z) (fin: Z.leb z MemNum = true) (pos: Z.leb 0 z = true).

Definition z_of (a: Addr): Z :=
  match a with
  | A z _ _ => z
  end.

Coercion z_of: Addr >-> Z.

Lemma z_of_eq a1 a2 :
  z_of a1 = z_of a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma eq_z_of a1 a2 :
  a1 = a2 ->
  z_of a1 = z_of a2.
Proof. destruct a1; destruct a2. congruence. Qed.

Lemma z_of_neq a1 a2 :
  z_of a1 <> z_of a2 ->
  a1 <> a2.
Proof. red; intros. apply H. rewrite H0; reflexivity. Qed.

Lemma neq_z_of a1 a2 :
  a1 ≠ a2 → (z_of a1) ≠ (z_of a2).
Proof. intros. intros Heq%z_of_eq. congruence. Qed.

Global Instance addr_eq_dec: EqDecision Addr.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. eapply z_of_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Definition z_to_addr (z : Z) : option Addr.
Proof.
  destruct (Z_le_dec z MemNum),(Z_le_dec 0 z).
  - apply (Z.leb_le z MemNum) in l.
    apply (Z.leb_le 0 z) in l0.
    exact (Some (A z l l0)).
  - exact None.
  - exact None.
  - exact None.
Defined.

Lemma addr_spec (a: Addr) : (a <= MemNum)%Z ∧ (0 <= a)%Z.
Proof.
  destruct a. cbn. rewrite -> Z.leb_le in fin.
  rewrite -> Z.leb_le in pos. lia.
Qed.

Lemma z_to_addr_z_of (a:Addr) :
  z_to_addr a = Some a.
Proof.
  generalize (addr_spec a); intros [? ?].
  set (z := (z_of a)) in *.
  unfold z_to_addr.
  destruct (Z_le_dec z MemNum) eqn:?;
  destruct (Z_le_dec 0 z) eqn:?.
  { f_equal. apply z_of_eq. cbn. lia. }
  all: lia.
Qed.

Lemma z_to_addr_eq_inv (a b:Addr) :
  z_to_addr a = Some b → a = b.
Proof. rewrite z_to_addr_z_of. naive_solver. Qed.

Global Instance addr_countable : Countable Addr.
Proof.
  refine {| encode r := encode (z_of r) ;
            decode n := match (decode n) with
                        | Some z => z_to_addr z
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold z_to_addr. simpl.
  destruct (Z_le_dec z MemNum),(Z_le_dec 0 z).
  - repeat f_equal; apply eq_proofs_unicity; decide equality.
  - exfalso. by apply (Z.leb_le 0 z) in pos.
  - exfalso. by apply (Z.leb_le z MemNum) in fin.
  - exfalso. by apply (Z.leb_le z MemNum) in fin.
Defined.

Definition le_lt_addr : Addr → Addr → Addr → Prop :=
  λ a1 a2 a3, (a1 <= a2 < a3)%Z.
Definition le_addr : Addr → Addr → Prop :=
  λ a1 a2, (a1 <= a2)%Z.
Definition lt_addr : Addr → Addr → Prop :=
  λ a1 a2, (a1 < a2)%Z.
Definition leb_addr : Addr → Addr → bool :=
  λ a1 a2, Z.leb a1 a2.
Definition ltb_addr : Addr → Addr → bool :=
  λ a1 a2, Z.ltb a1 a2.
Definition eqb_addr : Addr → Addr → bool :=
  λ a1 a2, Z.eqb a1 a2.
Definition za : Addr := A 0%Z eq_refl eq_refl.
Definition top : Addr := A MemNum eq_refl eq_refl.
Declare Scope Addr_scope.
Delimit Scope Addr_scope with a.
Notation "a1 <= a2 < a3" := (le_lt_addr a1 a2 a3): Addr_scope.
Notation "a1 <= a2" := (le_addr a1 a2): Addr_scope.
Notation "a1 <=? a2" := (leb_addr a1 a2): Addr_scope.
Notation "a1 < a2" := (lt_addr a1 a2): Addr_scope.
Notation "a1 <? a2" := (ltb_addr a1 a2): Addr_scope.
Notation "a1 =? a2" := (eqb_addr a1 a2): Addr_scope.
Notation "0" := (za) : Addr_scope.

Global Instance Addr_le_dec : RelDecision le_addr.
Proof. intros x y. destruct x,y. destruct (Z_le_dec z z0); [by left|by right]. Defined.
Global Instance Addr_lt_dec : RelDecision lt_addr.
Proof. intros x y. destruct x,y. destruct (Z_lt_dec z z0); [by left|by right]. Defined.

Lemma leb_addr_spec:
  forall a1 a2,
    reflect (le_addr a1 a2) (leb_addr a1 a2).
Proof.
  intros. unfold leb_addr, le_addr.
  apply Z.leb_spec0.
Qed.

Program Definition incr_addr (a: Addr) (z: Z): option Addr :=
  match (Z_le_dec (a + z)%Z MemNum) with
  | left _ =>
    match (Z_le_dec 0 (a + z)%Z) with
    | left _ => Some (A (a + z)%Z _ _)
    | right _ => None
    end
  | right _ => None
  end.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined. 
Notation "a1 + z" := (incr_addr a1 z): Addr_scope.

Definition max (a1 a2: Addr): Addr :=
  match Addr_le_dec a1 a2 with
  | left _ => a2
  | right _ => a1
  end.

Definition min (a1 a2: Addr): Addr :=
  match Addr_le_dec a1 a2 with
  | left _ => a1
  | right _ => a2
  end.

Lemma min_addr_spec (a1 a2: Addr):
  exists a, min a1 a2 = a /\ (a: Z) = Z.min (a1: Z) (a2: Z).
Proof.
  exists (min a1 a2); split; auto.
  unfold min. destruct (Addr_le_dec a1 a2); unfold le_addr in *; lia.
Qed.

Ltac min_addr_as_spec a1 a2 :=
  generalize (min_addr_spec a1 a2); intros [? [? ?]];
  let ax := fresh "ax" in
  set (ax := (min a1 a2)) in *;
  clearbody ax; subst ax.

Lemma max_addr_spec (a1 a2: Addr):
  exists a, max a1 a2 = a /\ (a: Z) = Z.max (a1: Z) (a2: Z).
Proof.
  exists (max a1 a2); split; auto.
  unfold max. destruct (Addr_le_dec a1 a2); unfold le_addr in *; lia.
Qed.

Ltac max_addr_as_spec a1 a2 :=
  generalize (max_addr_spec a1 a2); intros [? [? ?]];
  let ax := fresh "ax" in
  set (ax := (max a1 a2)) in *;
  clearbody ax; subst ax.

Definition get_addr_from_option_addr : option Addr → Addr :=
  λ e_opt, match e_opt with
           | Some e => e
           | None => top%a
           end.

Notation "^ a" := (get_addr_from_option_addr a) (format "^ a", at level 1) : Addr_scope.

Definition incr_addr_default (a: Addr) (z: Z): Addr := (^ (a + z))%a.
Notation "a ^+ z" := (incr_addr_default a z) (at level 50) : Addr_scope.

Lemma addr_unique a a' fin fin' pos pos' :
  a = a' → A a fin pos = A a' fin' pos'.
Proof.
  intros ->. repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

