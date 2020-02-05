Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From stdpp Require Import gmap fin_maps list.

Definition RegNum: nat := 31.
Definition MemNum: Z := 2000000.

(* ------------------------------------ ADDR -------------------------------------------*)

Inductive Addr: Type :=
| A (z : Z) (fin: Z.leb z MemNum = true).

Definition z_of (a: Addr): Z :=
  match a with
  | A z _ => z
  end.

Coercion z_of: Addr >-> Z.

Lemma z_of_eq:
  forall a1 a2,
    z_of a1 = z_of a2 ->
    a1 = a2.
Proof.
  intros. destruct a1, a2; simpl in *.
  simplify_eq.
  assert (forall (b: bool) (n m: Z) (P1 P2: Z.leb n m = b), P1 = P2).
  { intros. apply eq_proofs_unicity.
    intros; destruct x; destruct y; auto. }
    by rewrite (H true z0 MemNum fin fin0).
Qed.

Lemma neq_z_of :
  forall a1 a2,
    a1 ≠ a2 → (z_of a1) ≠ (z_of a2).
Proof.
  intros.
  unfold not. intros Heq. apply (z_of_eq a1 a2) in Heq.
  contradiction.
Qed. 

Global Instance addr_eq_dec: EqDecision Addr.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. eapply z_of_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Definition z_to_addr (z : Z) : option Addr.
Proof.
  destruct (Z_le_dec z MemNum).
  - apply (Z.leb_le z MemNum) in l.
    exact (Some (A z l)).
  - exact None. 
Defined. 

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
  destruct (Z_le_dec z MemNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Z.leb_le z MemNum) in fin. 
Qed.

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
Definition za : Addr := A 0%Z eq_refl.
Definition special_a : Addr := A (-42)%Z eq_refl.
Definition top : Addr := A MemNum eq_refl.
Delimit Scope Addr_scope with a.
Notation "a1 <= a2 < a3" := (le_lt_addr a1 a2 a3): Addr_scope.
Notation "a1 <= a2" := (le_addr a1 a2): Addr_scope.
Notation "a1 <=? a2" := (leb_addr a1 a2): Addr_scope.
Notation "a1 < a2" := (lt_addr a1 a2): Addr_scope.
Notation "a1 <? a2" := (ltb_addr a1 a2): Addr_scope.
Notation "a1 =? a2" := (eqb_addr a1 a2): Addr_scope.
Notation "0" := (za) : Addr_scope.
Notation "- 42" := (special_a) : Addr_scope.

Global Instance Addr_le_dec : RelDecision le_addr.
Proof. intros x y. destruct x,y. destruct (Z_le_dec z z0); [by left|by right]. Defined.
Global Instance Addr_lt_dec : RelDecision lt_addr.
Proof. intros x y. destruct x,y. destruct (Z_lt_dec z z0); [by left|by right]. Defined.

Program Definition incr_addr (a: Addr) (z: Z): option Addr :=
  if (Z_le_dec (a + z)%Z MemNum) then Some (A (a + z)%Z _) else None.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined.
Notation "a1 + z" := (incr_addr a1 z): Addr_scope.

Lemma incr_addr_neg:
  forall a z,
    (z <= 0)%Z ->
    exists a', (a + z)%a = Some a'.
Proof.
  intros; unfold incr_addr.
  destruct (Z_le_dec (a + z)%Z MemNum); eauto.
  destruct a. generalize (proj1 (Z.leb_le _ _) fin).
  intros. elim n. simpl. omega.
Qed.

Lemma incr_addr_one_none:
  forall a,
    (a + 1)%a = None ->
    a = top.
Proof.
  unfold incr_addr; intros.
  destruct (Z_le_dec (a + 1)%Z MemNum); try congruence.
  eapply z_of_eq. simpl in *.
  destruct a; simpl in *.
  apply Z.leb_le in fin. omega.
Qed.

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

Definition region_size : Addr → Addr → nat := 
  λ b e, S (Z.abs_nat (e - b)).

Definition get_addr_from_option_addr : option Addr → Addr :=
  λ e_opt, match e_opt with
           | Some e => e
           | None => top%a
           end.

Lemma top_le_eq e' : (top <= e')%a → e' = top.
Proof.
  intros. apply z_of_eq. simpl in *.
  destruct e'. unfold le_addr in *.
  simpl in *. apply Z.leb_le in fin.
  omega.
Qed.

Lemma top_not_le_eq a : ¬ (a < top)%a → a = top.
Proof.
  intros. apply top_le_eq.
  destruct a; unfold le_addr; unfold lt_addr in *; simpl in *.
  apply Z.leb_le in fin. omega.
Qed.

(* ------------------------------------ REG --------------------------------------------*)

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
  if (nat_le_dec n RegNum) then Some (R n _) else None.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
Qed.

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
