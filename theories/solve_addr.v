From Coq Require Import ZArith Lia.
From stdpp Require Import list.
From cap_machine Require Import addr_reg.

(* Automation: a [solve_addr] tactic that solves address arithmetic *)

(* This is implemented as a zify-like tactic, that sends arithmetic on adresses
   into Z, and then calls lia *)

Lemma incr_addr_spec (a: Addr) (z: Z) :
  (exists (a': Addr),
   (a + z)%a = Some a' ∧ a + z ≤ MemNum ∧ 0 ≤ a + z ∧ (a':Z) = a + z)%Z
  ∨
  ((a + z)%a = None ∧ (a + z > MemNum ∨ a + z < 0))%Z.
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

(* Non-branching lemma for the special case of an assumption [(a + z) = Some a'],
   which is common in practice. *)
Lemma incr_addr_Some_spec (a a': Addr) (z: Z) :
  (a + z)%a = Some a' →
  (a + z ≤ MemNum ∧ 0 ≤ a + z ∧ (a':Z) = a + z)%Z.
Proof.
  unfold incr_addr.
  destruct (Z_le_dec (a + z)%Z MemNum),(Z_le_dec 0 (a + z)%Z); inversion 1.
  repeat split; lia.
Qed.

Lemma Some_eq_inj A (x y: A) :
  Some x = Some y ->
  x = y.
Proof. congruence. Qed.

(* Instantiated in [solve_addr_extra.v] *)
Ltac zify_addr_op_nonbranching_step_hook :=
  fail.

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

  | H : incr_addr _ _ = Some _ |- _ =>
    apply incr_addr_Some_spec in H;
    destruct H as (? & ? & ?)
  end || zify_addr_op_nonbranching_step_hook.

(* We need some reduction, but naively calling "cbn in *" causes performance
   problems down the road. So here we try to:
   - give a "good enough" allow-list
   - reduce all occurences of [length foo], because in practice [foo] often
     unfolds to a concrete list of instructions and we want its length to compute.
*)
Ltac zify_addr_nonbranching_step :=
  first [ progress (cbn [z_of get_addr_from_option_addr top za fst snd length] in * )
        | progress (simpl length in *)
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

(* Faster alternative to [set (H := v) in *] *)
(* https://github.com/coq/coq/issues/13788#issuecomment-767217670 *)
Ltac fast_set H v :=
  pose v as H; change v with H;
  repeat match goal with H' : context[v] |- _ => change v with H in H' end.

Ltac zify_addr_ty_step :=
  lazymatch goal with
  | a : Addr |- _ =>
    generalize (addr_spec a); intros [? ?];
    let z := fresh "z" in
    fast_set z (z_of a);
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
  intros; cbn;
  repeat zify_addr_op_goal_step;
  try solve_addr_close_proof;
  repeat (
    zify_addr_op_deepen;
    try solve_addr_close_proof
  );
  solve_addr_close_proof.

Tactic Notation "solve_addr" := solve_addr.
Tactic Notation "solve_addr" "-" hyp_list(Hs) := clear Hs; solve_addr.
Tactic Notation "solve_addr" "+" hyp_list(Hs) := clear -Hs; solve_addr.

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

Lemma invert_incr_addr (a1 a2: Addr) (z:Z):
      (a1 + z)%a = Some a2 → (a2 + (- z))%a = Some a1.
Proof. solve_addr. Qed.
