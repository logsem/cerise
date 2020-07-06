From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
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

(** Automation *)
(*** A zify-like tactic to send arithmetic on adresses into Z ******)

Lemma addr_spec (a: Addr) : (a <= MemNum)%Z ∧ (0 <= a)%Z.
Proof. destruct a. cbn. rewrite Z.leb_le in fin. rewrite Z.leb_le in pos. lia. Qed.

Lemma incr_addr_spec (a: Addr) (z: Z) :
  (exists (a': Addr),
    (a + z)%a = Some a' /\ a + z <= MemNum /\ 0 ≤ a + z ∧ (a':Z) = a + z)%Z
  \/
  ((a + z)%a = None /\ (a + z > MemNum ∨ a + z < 0))%Z.
Proof.
  unfold incr_addr.
  destruct (Z_le_dec (a + z)%Z MemNum),(Z_le_dec 0 (a + z)%Z); [ left | right; split; auto; try lia..].
  eexists. repeat split; lia. 
Qed.

Ltac incr_addr_as_spec a x :=
  generalize (incr_addr_spec a x); intros [(?&?&?&?&?)|(?&[?|?])];
  let ax := fresh "ax" in
  set (ax := (incr_addr a x)) in *;
  clearbody ax; subst ax.

Lemma Some_eq_inj A (x y: A) :
  Some x = Some y ->
  x = y.
Proof. congruence. Qed.

Ltac zify_addr_op_nonbranching_step :=
  lazymatch goal with
  | |- @eq Addr ?a ?a' =>
    apply z_of_eq
  | H : @eq Addr ?a ?a' |- _ =>
    apply eq_z_of in H
  | |- not (@eq Addr ?a ?a') =>
    apply z_of_neq
  | H : not (@eq Addr ?a ?a') |- _ =>
    apply neq_z_of in H
  | |- @eq (option Addr) (Some _) (Some _) =>
    f_equal
  | H : @eq (option Addr) (Some _) (Some _) |- _ =>
    apply Some_eq_inj in H
  | |- @eq (option Addr) (Some _) None =>
    exfalso
  | |- @eq (option Addr) None (Some _) =>
    exfalso

  (* wrapper definitions to unfold (<=, <, etc) *)
  | |- context [ le_lt_addr _ _ _ ] =>
    unfold le_lt_addr
  | H : context [ le_lt_addr _ _ _ ] |- _ =>
    unfold le_lt_addr in H
  | |- context [ le_addr _ _ ] =>
    unfold le_addr
  | H : context [ le_addr _ _ ] |- _ =>
    unfold le_addr in H
  | |- context [ leb_addr _ _ ] =>
    unfold leb_addr
  | H : context [ leb_addr _ _ ] |- _ =>
    unfold leb_addr in H
  | |- context [ lt_addr _ _ ] =>
    unfold lt_addr
  | H : context [ lt_addr _ _ ] |- _ =>
    unfold lt_addr in H
  | |- context [ ltb_addr _ _ ] =>
    unfold ltb_addr
  | H : context [ ltb_addr _ _ ] |- _ =>
    unfold ltb_addr in H
  | |- context [ eqb_addr _ _ ] =>
    unfold eqb_addr
  | H : context [ eqb_addr _ _ ] |- _ =>
    unfold eqb_addr in H
  | H : context [ min ?a1 ?a2 ] |- _ =>
    min_addr_as_spec a1 a2
  | |- context [ min ?a1 ?a2 ] =>
    min_addr_as_spec a1 a2
  | H : context [ max ?a1 ?a2 ] |- _ =>
    max_addr_as_spec a1 a2
  | |- context [ max ?a1 ?a2 ] =>
    max_addr_as_spec a1 a2
  end.

Ltac zify_addr_nonbranching_step :=
  first [ progress (cbn in *)
        | zify_addr_op_nonbranching_step ].

Ltac zify_addr_op_branching_goal_step :=
  lazymatch goal with
  | |- context [ incr_addr ?a ?x ] =>
    incr_addr_as_spec a x
  end.

Ltac zify_addr_op_branching_hyps_step :=
  lazymatch goal with
  | _ : context [ incr_addr ?a ?x ] |- _ =>
    incr_addr_as_spec a x
  end.

Ltac zify_addr_ty_step :=
  lazymatch goal with
  | a : Addr |- _ =>
    generalize (addr_spec a); intros [? ?];
    let z := fresh "z" in
    set (z := (z_of a)) in *;
    clearbody z;
    first [ clear a | revert dependent a ]
  end.

(** zify_addr **)
(* This greedily translates all the address-related terms in the goal and in the
   context. Because each (_ + _) introduces a disjunction, the number of goals
   quickly explodes if there are many (_ + _) in the context.

   The solve_addr tactic below is more clever and tries to limit the
   combinatorial explosion, but zify_addr does not. *)

Ltac zify_addr :=
  repeat (first [ zify_addr_nonbranching_step
                | zify_addr_op_branching_goal_step
                | zify_addr_op_branching_hyps_step ]);
  repeat zify_addr_ty_step; intros.


(** solve_addr *)
(* From a high-level perspective, [solve_addr] is equivalent to [zify_addr]
   followed by [lia].

   However, this gets very slow when there are many (_ + _) in the context (and
   some of those may not be relevant to prove the goal at hand), so the
   implementation is a bit more clever. Instead, we try to call [lia] as soon as
   possible to quickly terminate sub-goals than can be proved before the whole
   context gets translated. *)

Ltac zify_addr_op_goal_step :=
  first [ zify_addr_nonbranching_step
        | zify_addr_op_branching_goal_step ].

Ltac zify_addr_op_deepen :=
  zify_addr_op_branching_hyps_step;
  repeat zify_addr_nonbranching_step;
  try (
    zify_addr_op_branching_hyps_step;
    repeat zify_addr_nonbranching_step
  ).

Ltac solve_addr_close_proof :=
  repeat zify_addr_ty_step; intros;
  solve [ auto | lia | congruence ].

Ltac solve_addr :=
  intros;
  repeat zify_addr_op_goal_step;
  try solve_addr_close_proof;
  repeat (
    zify_addr_op_deepen;
    try solve_addr_close_proof
  );
  solve_addr_close_proof.

Goal forall a : Addr,
    (a + -(a + 3))%a = None.
Proof.
  intros. solve_addr.
Qed. 

Goal forall (a a' b b' : Addr),
  (a + 1)%a = Some a' ->
  (b + 1)%a = Some b' ->
  (a + 0)%a = Some a.
Proof.
  intros.
  repeat zify_addr_op_goal_step.
  (* Check that we can actually terminate early before translating the whole
     context. *)
  solve_addr_close_proof.
  solve_addr_close_proof.
  solve_addr_close_proof.
Qed.

(* ------------------ *)
(* Hack: modify [zify] to make it support [Z.to_nat] (used in the definition of
   [region_size]). *)
(* TODO: remove the code below whenever we upgrade to Coq 8.11, as the issue has
   been fixed upstream starting from Coq 8.11.
*)

Lemma Z_of_nat_zify : forall x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
  intros x. destruct x.
  - rewrite Z2Nat.id; reflexivity.
  - rewrite Z2Nat.inj_pos. lia.
  - rewrite Z2Nat.inj_neg. lia.
Qed.

Ltac zify_nat_op_extended :=
  match goal with
  | H : context [ Z.of_nat (Z.to_nat ?a) ] |- _ => rewrite (Z_of_nat_zify a) in H
  | |- context [ Z.of_nat (Z.to_nat ?a) ] => rewrite (Z_of_nat_zify a)
  | _ => zify_nat_op
  end.

Global Ltac zify_nat ::=
  repeat zify_nat_rel; repeat zify_nat_op_extended; unfold Z_of_nat' in *.

(* --------------------------- BASIC LEMMAS --------------------------------- *)

(** Address arithmetic *)

Lemma addr_add_0 a: (a + 0)%a = Some a.
Proof. solve_addr. Qed.

Lemma incr_addr_one_none a :
  (a + 1)%a = None ->
  a = top.
Proof. solve_addr. Qed.

Lemma incr_addr_opt_add_twice (a: Addr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ^(^(a + n) + m)%a = ^(a + (n + m)%Z)%a.
Proof. solve_addr. Qed.

Lemma top_le_eq a : (top <= a)%a → a = top.
Proof. solve_addr. Qed.

Lemma top_not_le_eq a : ¬ (a < top)%a → a = top.
Proof. solve_addr. Qed.

Lemma next_lt (a a' : Addr) :
  (a + 1)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma next_lt_i (a a' : Addr) (i : Z) :
  (i > 0)%Z →
  (a + i)%a = Some a' → (a < a')%Z.
Proof. solve_addr. Qed.

Lemma next_le_i (a a' : Addr) (i : Z) :
  (i >= 0)%Z →
  (a + i)%a = Some a' → (a <= a')%Z.
Proof. solve_addr. Qed.

Lemma next_lt_top (a : Addr) i :
  (i > 0)%Z →
  is_Some (a + i)%a → a ≠ top.
Proof. intros ? [? ?] ?. solve_addr. Qed.

Lemma addr_next_le (a e : Addr) :
  (a < e)%Z → ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma addr_next_lt (a e : Addr) :
  (a < e)%Z -> ∃ a', (a + 1)%a = Some a'.
Proof. intros. zify_addr; eauto. exfalso. lia. lia. Qed.

Lemma addr_next_lt_gt_contr (a e a' : Addr) :
  (a < e)%Z → (a + 1)%a = Some a' → (e < a')%Z → False.
Proof. solve_addr. Qed.

Lemma addr_next_lt_le (a e a' : Addr) :
  (a < e)%Z → (a + 1)%a = Some a' → (a' ≤ e)%Z.
Proof. solve_addr. Qed.

Lemma addr_abs_next (a e a' : Addr) :
  (a + 1)%a = Some a' → (a < e)%Z → (Z.abs_nat (e - a) - 1) = (Z.abs_nat (e - a')).
Proof. solve_addr. Qed.

Lemma addr_unique a a' fin fin' pos pos' :
  a = a' → A a fin pos = A a' fin' pos'.
Proof.
  intros ->. repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma incr_addr_trans (a1 a2 a3 : Addr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 → (a2 + z2)%a = Some a3 →
  (a1 + (z1 + z2))%a = Some a3.
Proof. solve_addr. Qed.

Lemma addr_add_assoc (a a' : Addr) (z1 z2 : Z) :
  (a + z1)%a = Some a' →
  (a + (z1 + z2))%a = (a' + z2)%a.
Proof. solve_addr. Qed.

Lemma incr_addr_le (a1 a2 a3 : Addr) (z1 z2 : Z) :
  (a1 + z1)%a = Some a2 -> (a1 + z2)%a = Some a3 -> (z1 <= z2)%Z ->
  (a2 <= a3)%Z.
Proof. solve_addr. Qed.

Lemma incr_addr_ne a i :
  i ≠ 0%Z → a ≠ top →
  ^ (a + i)%a ≠ a.
Proof. intros H1 H2. intro. apply H2. solve_addr. Qed.

Lemma incr_addr_ne_top a z a' :
  (z > 0)%Z → (a + z)%a = Some a' →
  a ≠ top.
Proof. intros. intro. solve_addr. Qed.

Lemma get_addrs_from_option_addr_comm a i k :
  (k >= 0)%Z -> (i >= 0)%Z ->
  (^(^(a + i) + k)%a) =
  (^(a + (i + k)%Z)%a).
Proof. solve_addr. Qed.

Lemma incr_addr_of_z (a a' : Addr) :
  (a + 1)%a = Some a' →
  (a + 1)%Z = a'.
Proof. solve_addr. Qed.

Lemma incr_addr_of_z_i (a a' : Addr) i :
  (a + i)%a = Some a' →
  (a + i)%Z = a'.
Proof. solve_addr. Qed.
