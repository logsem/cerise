Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From stdpp Require Import gmap fin_maps list.

Definition RegNum: nat := 31.
Definition MemNum: Z := 2000000.

(* ------------------------------------ ADDR -------------------------------------------*)

Inductive Addr: Type :=
| A (z : Z) (fin: Z.leb z MemNum = true). 

Instance addr_eq_dec: EqDecision Addr.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. simplify_eq.
  assert (forall (b: bool) (n m: Z) (P1 P2: Z.leb n m = b), P1 = P2).
  { intros. apply eq_proofs_unicity.
    intros; destruct x; destruct y; auto. }
    by rewrite (H true z0 MemNum fin fin0).
- right. inversion 1. simplify_eq. 
Defined.

Definition z_to_addr (z : Z) : option Addr.
Proof. 
  destruct (Z_le_dec z MemNum).
  - apply (Z.leb_le z MemNum) in l.
    exact (Some (A z l)).
  - exact None. 
Defined. 

Instance addr_countable : Countable Addr.
Proof. 
  refine {| encode r := encode match r with
                               | A z fin => z
                               end ;
              decode n := match (decode n) with
                          | Some z => z_to_addr z
                          | None => None
                          end ;
              decode_encode := _ |}. 
  intro r. destruct r; auto. 
  rewrite decode_encode.
  unfold z_to_addr.
  destruct (Z_le_dec z MemNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Z.leb_le z MemNum) in fin. 
Qed.

Definition le_lt_addr : Addr → Addr → Addr → Prop :=
  λ a1 a2 a3, match a1,a2,a3 with
              | A z1 fin1, A z2 fin2, A z3 fin3 => (z1 <= z2 < z3)%Z
              end.
Definition le_addr : Addr → Addr → Prop :=
  λ a1 a2, match a1,a2 with
           | A z1 fin1, A z2 fin2 => (z1 <= z2)%Z
           end.
Definition lt_addr : Addr → Addr → Prop :=
  λ a1 a2, match a1,a2 with
           | A z1 fin1, A z2 fin2 => (z1 < z2)%Z
           end.
Definition leb_addr : Addr → Addr → bool :=
  λ a1 a2, match a1,a2 with
           | A z1 _, A z2 _ => Z.leb z1 z2
           end.
Definition ltb_addr : Addr → Addr → bool :=
  λ a1 a2, match a1,a2 with
           | A z1 _, A z2 _ => Z.ltb z1 z2
           end.
Definition eqb_addr : Addr → Addr → bool :=
  λ a1 a2, match a1,a2 with
           | A z1 _,A z2 _ => Z.eqb z1 z2
           end.
Definition za : Addr. Proof. refine (A 0%Z _); eauto. Defined.  
Definition special_a : Addr. Proof. refine (A (-42)%Z _); eauto. Defined.
Definition top_a : Addr. Proof. refine (A MemNum _); eauto. Defined. 
Delimit Scope Addr_scope with a.
Notation "a1 <= a2 < a3" := (le_lt_addr a1 a2 a3): Addr_scope.
Notation "a1 < a2" := (lt_addr a1 a2) : Addr_scope. 
Notation "a1 <= a2" := (le_addr a1 a2): Addr_scope.
Notation "a1 <=? a2" := (leb_addr a1 a2): Addr_scope.
Notation "a1 <? a2" := (ltb_addr a1 a2): Addr_scope.
Notation "a1 =? a2" := (eqb_addr a1 a2): Addr_scope.
Notation "0" := (za) : Addr_scope.
Notation "- 42" := (special_a) : Addr_scope.  

Instance Addr_le_dec : RelDecision le_addr. 
Proof. intros x y. destruct x,y. destruct (Z_le_dec z z0); [by left|by right]. Defined.
Instance Addr_lt_dec : RelDecision lt_addr. 
Proof. intros x y. destruct x,y. destruct (Z_lt_dec z z0); [by left|by right]. Defined.


Definition incr_addr : Addr → nat → option Addr.
Proof.
  destruct 1. intros z'. 
  destruct (Z.leb (z + (Z_of_nat' z'))%Z MemNum) eqn:Hlt.
  - by refine (Some (A (z + (Z_of_nat' z'))%Z _)).
  - exact None. 
Defined.
Notation "a1 + n" := (incr_addr a1 n): Addr_scope.

Definition incr_addr_force : Addr → nat → Addr.
Proof.
  destruct 1. intros z'. 
  destruct (Z.leb (z + (Z_of_nat' z'))%Z MemNum) eqn:Hlt.
  - by refine (A (z + (Z_of_nat' z'))%Z _).
  - exact top_a%a.
Defined.
Notation "a1 ++ n" := (incr_addr_force a1 n): Addr_scope.

Lemma Zpred_minus z : (Z.pred z = z - 1)%Z.
Proof. eauto. Qed. 

Lemma Zminus_succ_r z n : (Z.pred (z - (Z_of_nat n)) = z - (Z.succ (Z_of_nat n)))%Z.
Proof.
  induction n; simpl. 
  - rewrite <- Zminus_0_l_reverse. eauto.
  - rewrite Zpred_minus. omega.
Qed.

Lemma Z_minus_plus_leq z z' z'' : (z - z' ≤ z'' ↔ z ≤ z'' + z')%Z.
Proof. split; omega. Qed.

Lemma Z_plus_minus_leq z z' z'' : (z ≤ z'' - z' ↔ z + z' ≤ z'')%Z.
Proof. split; omega. Qed.

Lemma Z_leq_succ z z' : (Z.succ z ≤ Z.succ z' → z ≤ z')%Z.
Proof. intros. omega. Qed. 

Definition decr_addr : Addr → nat → option Addr.
Proof.
  destruct 1. intros z'.
  destruct (Z.leb 0%Z (z - (Z_of_nat' z'))) eqn:Hlt.
  - refine (Some (A (z - (Z_of_nat' z'))%Z _)).
    apply Z.leb_le. induction z'; simpl in *. 
    + rewrite <- Zminus_0_l_reverse. by apply Z.leb_le.
    + rewrite Zpos_P_of_succ_nat. rewrite <- Zminus_succ_r.  
      rewrite Zpred_minus.
      apply Z_minus_plus_leq.
      assert (MemNum + 1 = Z.succ MemNum)%Z; eauto.
      rewrite H. apply Z.le_le_succ_r.
      apply IHz'. apply Z.leb_le. apply Z_plus_minus_leq.
      rewrite Zpos_P_of_succ_nat in Hlt. apply Z.leb_le in Hlt. 
      apply Z_plus_minus_leq in Hlt. 
      assert (∀ z, 0 + z = z)%Z; intros; eauto.
      rewrite H0. rewrite H0 in Hlt. apply Z.le_le_succ_r in Hlt.
      apply Z_leq_succ in Hlt. done.
  - exact None. 
Defined.
Notation "a1 - n" := (incr_addr a1 n): Addr_scope.

Definition decr_addr_force : Addr → nat → Addr.
Proof.
  destruct 1. intros z'.
  destruct (Z.leb 0%Z (z - (Z_of_nat' z'))) eqn:Hlt.
  - refine (A (z - (Z_of_nat' z'))%Z _).
    apply Z.leb_le. induction z'; simpl in *. 
    + rewrite <- Zminus_0_l_reverse. by apply Z.leb_le.
    + rewrite Zpos_P_of_succ_nat. rewrite <- Zminus_succ_r.  
      rewrite Zpred_minus.
      apply Z_minus_plus_leq.
      assert (MemNum + 1 = Z.succ MemNum)%Z; eauto.
      rewrite H. apply Z.le_le_succ_r.
      apply IHz'. apply Z.leb_le. apply Z_plus_minus_leq.
      rewrite Zpos_P_of_succ_nat in Hlt. apply Z.leb_le in Hlt. 
      apply Z_plus_minus_leq in Hlt. 
      assert (∀ z, 0 + z = z)%Z; intros; eauto.
      rewrite H0. rewrite H0 in Hlt. apply Z.le_le_succ_r in Hlt.
      apply Z_leq_succ in Hlt. done.
  - exact 0%a.
Defined.
Notation "a1 -- n" := (decr_addr_force a1 n) (at level 20): Addr_scope.

Definition region_size : Addr → Addr → nat :=
  λ b e, match b, e with
         | A ba _, A ea _ => S (Z.abs_nat (ea - ba))
         end.

Definition get_addr_from_option_addr : option Addr → Addr :=
  λ e_opt, match e_opt with
           | Some e => e
           | None => top_a%a
           end.

Lemma addr_lt_trans a1 a2 a3 : (a1 < a2 → a2 < a3 → a1 < a3)%a.
Proof. destruct a1,a2,a3. unfold lt_addr. intros Hlt1 Hlt2.
       apply (Z.lt_trans z z0 z1); eauto.
Qed.

(* These are not exacty correct: should be ≤. *)
Lemma region_size_minus b a : region_size b (a -- 1)%a = (region_size b a) - 1.
Proof. Admitted. 
Lemma region_size_plus a e : region_size (a ++ 1)%a e = (region_size a e) - 1. 
Proof. Admitted. 

(* ------------------------------------ REG --------------------------------------------*)

Inductive RegName: Type :=
| PC
| R (n: nat) (fin: n <=? RegNum = true).

Instance reg_eq_dec : EqDecision RegName.
Proof. intros r1 r2.  destruct r1,r2; [by left | by right | by right |].
       destruct (nat_eq_dec n n0).
       + subst n0. left.
      assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
      { intros. apply eq_proofs_unicity.
        intros; destruct x; destruct y; auto. }
      rewrite (H _ _ _ fin fin0). reflexivity.
       + right. congruence.
Defined.

Definition n_to_regname (n : nat) : option RegName.
Proof. 
  destruct (nat_le_dec n RegNum).
  - apply (Nat.leb_le n RegNum) in l.
    exact (Some (R n l)).
  - exact None. 
Defined. 

Instance reg_countable : Countable RegName.
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
Qed.