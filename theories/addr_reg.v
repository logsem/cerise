From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From Coq.micromega Require Import ZifyClasses.
From stdpp Require Import gmap fin_maps list.

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
  if (nat_le_dec n RegNum) then Some (R n _) else None.
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
Proof. destruct a. cbn. rewrite Z.leb_le in fin. rewrite Z.leb_le in pos. lia. Qed.

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

(* XXX is this handled by solve_addr? *)
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
  if (Z_le_dec (a + z)%Z MemNum) then
    if (Z_le_dec 0 (a + z)%Z) then Some (A (a + z)%Z _ _) else None else None.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined.
Next Obligation.
  intros. apply Z.leb_le; auto.
Defined. 
Notation "a1 + z" := (incr_addr a1 z): Addr_scope.

Definition max (a1 a2: Addr): Addr :=
  if Addr_le_dec a1 a2 then a2 else a1.

Definition min (a1 a2: Addr): Addr :=
  if Addr_le_dec a1 a2 then a1 else a2.

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
Notation "a ^+ b" := (^ (a + b))%a (at level 50) : Addr_scope.

Lemma addr_unique a a' fin fin' pos pos' :
  a = a' → A a fin pos = A a' fin' pos'.
Proof.
  intros ->. repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.


(* ---------------------------------- OTypes ----------------------------------------*)

(* Number of otypes in our system *)
Definition ONum: nat := 1000.
Inductive OType: Type :=
| Oty (n : nat) (fin: n <=? ONum = true).

Definition n_of_otype (o: OType): nat :=
  match o with
  | Oty n _ => n
  end.
Coercion n_of_otype: OType >-> nat.

Program Definition n_to_otype (n : nat) : option OType :=
  if (nat_le_dec n ONum) then Some (Oty n _) else None.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
Defined.

Global Instance otype_eq_dec: EqDecision OType.
Proof. intros o1 o2.  destruct o1,o2.
       destruct (nat_eq_dec n n0).
       + subst n0. left.
         assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
         { intros. apply eq_proofs_unicity.
           intros; destruct x; destruct y; auto. }
         rewrite (H _ _ _ fin fin0). reflexivity.
       + right. congruence.
Defined.

Lemma n_of_to_otype_id (o : OType) : (n_to_otype o) = Some o.
Proof. destruct o. unfold n_of_otype, n_to_otype.
       assert (fin' := fin). rewrite Nat.leb_le in fin'.
       destruct (nat_le_dec _ _) as [? | Hne]; [| congruence].
       repeat f_equal. apply eq_proofs_unicity; decide equality.
Qed.

Global Instance otype_countable : Countable OType.
Proof.
  refine {| encode o := encode (n_of_otype o);
            decode n := match (decode n) with
                        | Some n => n_to_otype n
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro o. destruct o; auto.
  rewrite decode_encode.
  apply n_of_to_otype_id.
Defined.

Program Definition incr_otype (o: OType) (z: Z): option OType :=
  if decide ((o + z) >= 0)%Z then
    let sum := Z.to_nat (o + z)%Z in
    if (Z_le_dec sum ONum) then
      Some (Oty sum _)
    else None
  else None.
Next Obligation.
  intros. apply leb_le. lia.
Defined.
Notation "o + z" := (incr_otype o z).

(* Map Z into OTypes *)
Definition z_to_otype (z : Z) : option OType.
Proof.
  destruct (Z_le_dec 0 z).
  - pose (n := Z.to_nat z).  exact (n_to_otype n).
  - exact None.
Defined.

Lemma otype_spec (o: OType) : (o <= ONum)%Z ∧ (0 <= o)%Z.
Proof. destruct o. cbn. rewrite leb_le in fin. lia. Qed.

Lemma z_to_otype_z_of (o:OType) :
  z_to_otype o = Some o.
Proof.
  generalize (otype_spec o); intros [? ?].
  unfold z_to_otype.
  destruct (Z_le_dec o ONum) eqn:?;
  destruct (Z_le_dec 0 o) eqn:?.
  { f_equal. rewrite <- n_of_to_otype_id. f_equal. lia. }
  all: lia.
Qed.

Lemma z_to_otyp_eq_inv (a b:OType) :
  z_to_otype a = Some b → a = b.
Proof. rewrite z_to_otype_z_of. naive_solver. Qed.

(* Note: no custom scope needed for otypes atm, since they will use the corresponding definitions for 'nat' automatically *)
