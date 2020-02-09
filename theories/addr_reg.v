From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
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

Lemma z_of_eq a1 a2 :
  z_of a1 = z_of a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma eq_z_of a1 a2 :
  a1 = a2 ->
  z_of a1 = z_of a2.
Proof. destruct a1; destruct a2. congruence. Qed.

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

Definition region_size : Addr → Addr → nat :=
  λ b e, S (Z.abs_nat (e - b)).

Definition get_addr_from_option_addr : option Addr → Addr :=
  λ e_opt, match e_opt with
           | Some e => e
           | None => top%a
           end.

Notation "^ a" := (get_addr_from_option_addr a) (format "^ a", at level 1) : Addr_scope.

(** zify-like tactic to send arithmetic on adresses into Z ******)

Lemma addr_spec (a: Addr) : (a <= MemNum)%Z.
Proof. destruct a. cbn. rewrite Z.leb_le in fin. lia. Qed.

Lemma incr_addr_spec (a: Addr) (z: Z) :
  (exists (a': Addr),
    (a + z)%a = Some a' /\ a + z <= MemNum /\ (a':Z) = a + z)%Z
  \/
  ((a + z)%a = None /\ a + z > MemNum)%Z.
Proof.
  unfold incr_addr.
  destruct (Z_le_dec (a + z)%Z MemNum); [ left | right ].
  { eexists. repeat split; lia. }
  { split; auto; lia. }
Qed.

Ltac incr_addr_as_spec a x :=
  generalize (incr_addr_spec a x); intros [(?&?&?&?)|(?&?)];
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
    generalize (addr_spec a); intro;
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
Qed.

(** Derived lemmas *)

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
