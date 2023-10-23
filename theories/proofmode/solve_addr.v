From Coq Require Import ZArith Lia.
From stdpp Require Import list.
From cap_machine Require Import addr_reg.
From machine_utils Require Import solve_finz.

Ltac zify_addr := zify_finz.
Tactic Notation "solve_addr" := solve_finz.
Tactic Notation "solve_addr" "-" hyp_list(Hs) := clear Hs; solve_addr.
Tactic Notation "solve_addr" "+" hyp_list(Hs) := clear -Hs; solve_addr.

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
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. solve_addr. Qed.

Lemma incr_addr_opt_add_twice' (a: Addr) (n m: Z) :
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%a = (a ^+ (n + m)%Z)%a.
Proof. zify_addr;[]. (* only one goal! *) lia. Qed.

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
  (a ^+ i)%a ≠ a.
Proof. intros H1 H2. intro. apply H2. solve_addr. Qed.

Lemma incr_addr_ne_top a z a' :
  (z > 0)%Z → (a + z)%a = Some a' →
  a ≠ top.
Proof. intros. intro. solve_addr. Qed.

Lemma get_addrs_from_option_addr_comm a i k :
  (k >= 0)%Z -> (i >= 0)%Z ->
  (((a ^+ i) ^+ k)%a) =
  ((a ^+ (i + k)%Z)%a).
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
