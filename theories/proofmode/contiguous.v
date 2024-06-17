From iris.proofmode Require Import proofmode.
From cap_machine Require Import addr_reg_sample.


(* This file contains definition and lemmas for contiguous address regions *)
(* It is used mainly in specs of programs where it is necessary to assume  *)
(* that some program lies in memory in a contiguous region                 *)

Section Contiguous.

  Inductive contiguous_between : list Addr -> Addr -> Addr -> Prop :=
    | contiguous_between_nil : ∀ a,
        contiguous_between [] a a
    | contiguous_between_cons : ∀ a a' b l,
        (a + 1)%a = Some a' ->
        contiguous_between l a' b ->
        contiguous_between (a :: l) a b.

  Lemma contiguous_between_vacuous l a b :
    contiguous_between l a b →
    (b < a)%a →
    False.
  Proof. induction 1; intros; solve_addr. Qed.

  Lemma contiguous_between_bounds l a b :
    contiguous_between l a b →
    (a <= b)%a.
  Proof.
    intros HH. generalize (contiguous_between_vacuous _ _ _ HH).
    solve_addr.
  Qed.

  Lemma contiguous_between_nil_inv l a b :
    contiguous_between l a b →
    (b <= a)%a →
    l = [].
  Proof.
    induction 1; eauto.
    destruct (Z.eq_dec a b).
    { intros. exfalso.
      eapply (contiguous_between_vacuous l a' b). 2: solve_addr. eauto. }
    { intros. exfalso. eapply contiguous_between_vacuous; eauto. solve_addr. }
  Qed.

  Lemma contiguous_between_cons_inv a b e ai :
    contiguous_between (a :: ai) b e →
    a = b ∧ ∃ a', (a+1)%a = Some a' ∧ contiguous_between ai a' e.
  Proof. inversion 1; eauto. Qed.

  Lemma contiguous_between_cons_inv_first l a a' b :
    contiguous_between (a' :: l) a b →
    a' = a.
  Proof. inversion 1; eauto. Qed.

  Lemma contiguous_between_last (a : list Addr) a0 an ai :
    contiguous_between a a0 an →
    list.last a = Some ai →
    (ai + 1)%a = Some an.
  Proof.
    revert ai. induction 1 as [| * X Y].
    { inversion 1. }
    { destruct l.
      - cbn. inversion 1. inversion Y; subst. auto.
      - eauto. }
  Qed.

  Lemma contiguous_between_middle_to_end (a: list Addr) (a0 an: Addr) i ai k :
    contiguous_between a a0 an →
    a !! i = Some ai →
    i + k = length a →
    (ai + k)%a = Some an.
  Proof.
    intros * Ha. revert i k ai. induction Ha; [done |].
    intros [| i] k ai; cbn.
    { intros. simplify_eq. enough ((a' + length l)%a = Some b) by solve_addr.
      inversion Ha; subst; cbn. solve_addr.
      apply (IHHa 0); eauto. }
    { eauto. }
  Qed.

  Lemma contiguous_between_of_region_addrs_aux l a b n :
    l = finz.seq a n →
    (a + n)%a = Some b →
    contiguous_between l a b.
  Proof.
    revert a b l. induction n.
    { intros. cbn in *. subst l. assert (a = b) as -> by solve_addr.
      constructor. }
    { intros * -> ?. cbn. eapply (contiguous_between_cons _ (a^+1)%a). solve_addr.
      apply IHn; auto. solve_addr. }
  Qed.

  Lemma region_addrs_aux_of_contiguous_between l a b (n:nat) :
    contiguous_between l a b →
    (a + n)%a = Some b →
    l = finz.seq a n.
  Proof.
    revert a b l. induction n.
    { intros. cbn in *.
      apply (contiguous_between_nil_inv l a b); eauto; solve_addr. }
    { intros * Hl Hn. cbn.
      destruct l as [| a' l].
      { inversion Hl; subst. exfalso. solve_addr. }
      { inversion Hl; subst. f_equal. eapply (IHn _ b). 2: solve_addr.
        assert ((a^+1)%a = a'0) as -> by solve_addr. auto. } }
  Qed.

  Lemma contiguous_between_of_region_addrs l a b :
    (a <= b)%a →
    l = finz.seq_between a b →
    contiguous_between l a b.
  Proof.
    intros ? ->. eapply contiguous_between_of_region_addrs_aux; eauto.
    rewrite /finz.dist. solve_addr.
  Qed.

  Lemma contiguous_between_region_addrs a e :
    (a <= e) %a → contiguous_between (finz.seq_between a e) a e.
  Proof. intros; by apply contiguous_between_of_region_addrs. Qed.

  Lemma region_addrs_of_contiguous_between l a b :
    contiguous_between l a b →
    l = finz.seq_between a b.
  Proof.
    intros.
    destruct (Z.le_dec a b).
    { eapply region_addrs_aux_of_contiguous_between; eauto.
      rewrite /finz.dist. solve_addr. }
    { rewrite /finz.seq_between (_: finz.dist a b = 0) /=.
      2: unfold finz.dist; solve_addr.
      eapply contiguous_between_nil_inv; eauto. solve_addr. }
  Qed.

  Lemma contiguous_between_length a i j :
    contiguous_between a i j →
    (i + length a = Some j)%a.
  Proof. induction 1; cbn; solve_addr. Qed.

  Lemma contiguous_between_length_minus a i j :
    contiguous_between a i j →
    (j + - (length a) = Some i)%a.
  Proof. induction 1; cbn; solve_addr. Qed.

  Lemma contiguous_between_middle_bounds (a : list Addr) i (ai a0 an : Addr) :
    contiguous_between a a0 an →
    a !! i = Some ai →
    (a0 <= ai ∧ ai < an)%a.
  Proof.
    intro HH. revert ai i. induction HH as [| * Ha Hc Hi]; [ by inversion 1 |].
    intros * Hi'. destruct i as [| i].
    { cbn in Hi'. inversion Hi'; subst; clear Hi'. split; [ solve_addr |].
      destruct (decide (a' = b)).
      { subst a'. inversion Hc; subst; solve_addr. }
      { apply contiguous_between_length in Hc. solve_addr. } }
    { cbn in Hi'. split. enough (a' <= ai)%a by solve_addr.
      all: eapply Hi; eauto. }
  Qed.

  Lemma contiguous_between_middle_bounds' (a : list Addr) (ai a0 an : Addr) :
    contiguous_between a a0 an →
    ai ∈ a →
    (a0 <= ai ∧ ai < an)%a.
  Proof.
    intros Hc Hin.
    apply elem_of_list_lookup_1 in Hin as [? ?].
    eapply contiguous_between_middle_bounds; eauto.
  Qed.

  Lemma contiguous_between_incr_addr (a: list Addr) (i : nat) a0 ai an :
    contiguous_between a a0 an →
    a !! i = Some ai →
    (a0 + i)%a = Some ai.
  Proof.
    intros Hc. revert i ai. induction Hc.
    - inversion 1.
    - intros i ai. destruct i as [| i].
      { cbn. inversion 1; subst. solve_addr. }
      { cbn. intros Hi. specialize (IHHc _ _ Hi). solve_addr. }
  Qed.

  (* the i'th element is the same as adding i to the first element *)
  Lemma contiguous_between_link_last (a : list Addr) a_first a_last ai :
    contiguous_between a a_first a_last ->
    length a > 0 ->
    (ai + 1)%a = Some a_last -> list.last a = Some ai.
  Proof.
    revert a_first. induction a; intros a_first Ha Hlen Hlink.
    - inversion Hlen.
    - destruct a0.
      + inversion Ha. subst. inversion H4. subst. cbn. solve_addr.
      + simpl in *. apply IHa with f;[|lia|auto].
        inversion Ha; subst.
        apply contiguous_between_cons_inv_first in H4 as Heq.
        congruence.
  Qed.

  Lemma contiguous_between_incr_addr_middle (a : list Addr) a0 an (i j : nat) ai aj :
    contiguous_between a a0 an ->
    a !! i = Some ai -> a !! (i + j) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros HH Hi Hj.
    pose proof (contiguous_between_incr_addr _ _ _ _ _ HH Hi).
    pose proof (contiguous_between_incr_addr _ _ _ _ _ HH Hj). solve_addr.
  Qed.

  Lemma contiguous_between_incr_addr_middle' (a : list Addr) a0 an (i : nat) (j: Z) ai aj :
    contiguous_between a a0 an →
    (0 <= i + j < length a)%Z →
    a !! i = Some ai -> a !! (Z.to_nat (i + j)%Z) = Some aj -> (ai + j)%a = Some aj.
  Proof.
    intros HH ? Hi Hj.
    pose proof (contiguous_between_incr_addr _ _ _ _ _ HH Hi).
    pose proof (contiguous_between_incr_addr _ _ _ _ _ HH Hj). solve_addr.
  Qed.

  Lemma contiguous_between_app a a1 a2 (i j k: Addr) :
    a = a1 ++ a2 →
    contiguous_between a i j →
    (i + length a1 = Some k)%a →
    contiguous_between a1 i k ∧ contiguous_between a2 k j.
  Proof.
    revert a a2 i j k. induction a1 as [| aa a1].
    { intros * ->.  simpl. intros. assert (i = k) by solve_addr. subst i. split; auto.
      apply contiguous_between_nil. }
    { intros * ->. cbn. inversion 1. subst. intros.
      unshelve epose proof (IHa1 (a1 ++ a2) a2 _ _ _ eq_refl _ _) as [IH1 IH2];
        [ shelve | shelve | shelve | ..]; eauto; cycle 1.
      split; [| eapply IH2]. 2: by solve_addr.
      eapply contiguous_between_cons; eauto. }
  Qed.

  Lemma contiguous_between_spec (l: list Addr) a0 an :
      contiguous_between l a0 an →
      (∀ i ai aj,
       l !! i = Some ai →
       l !! (i + 1) = Some aj →
       (ai + 1)%a = Some aj).
  Proof.
    intros Hl.
    induction Hl as [| * Ha' Hl Hind].
    { intros *. inversion 1. }
    { intros * Hi Hi'. destruct i as [| i].
      { cbn in *. inversion Hi; subst ai; clear Hi.
        destruct Hl; inversion Hi'; [ subst aj; clear Hi' ]. auto. }
      { cbn in *. eauto. } }
  Qed.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}.

  (* Note that we are assuming that both prog1 and prog2 are nonempty *)
  Lemma contiguous_between_program_split prog1 prog2 (φ : Addr → Word → iProp Σ) a i j :
    contiguous_between a i j →
    ⊢ (([∗ list] a_i;w_i ∈ a;prog1 ++ prog2, φ a_i w_i) -∗
    ∃ (a1 a2 : list Addr) (k: Addr),
      ([∗ list] a_i;w_i ∈ a1;prog1, φ a_i w_i)
        ∗ ([∗ list] a_i;w_i ∈ a2;prog2, φ a_i w_i)
        ∗ ⌜contiguous_between a1 i k
           ∧ contiguous_between a2 k j
           ∧ a = a1 ++ a2
           ∧ (i + length a1 = Some k)%a⌝)%I.
  Proof.
    iIntros (Ha) "Hprog".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    rewrite app_length in Hlength.
    set (n1 := length prog1) in *.
    set (n2 := length prog2) in *.
    rewrite -(take_drop n1 a). set (k := (i ^+ n1)%a).
    iExists (take n1 a), (drop n1 a), k.
    iDestruct (big_sepL2_app' with "Hprog") as "[Hprog1 Hprog2]".
    { subst n1. rewrite take_length. lia. }
    iFrame. iPureIntro.
    pose proof (contiguous_between_length _ _ _ Ha).
    destruct (contiguous_between_app a (take n1 a) (drop n1 a) i j k); auto.
    by rewrite take_drop.
    { rewrite take_length Hlength. subst k. solve_addr. }
    rewrite take_length. repeat split; eauto. rewrite Nat.min_l; subst k; solve_addr.
  Qed.

  Lemma contiguous_between_inj l:
    forall a1 b1 b2,
      contiguous_between l a1 b1 ->
      contiguous_between l a1 b2 ->
      b1 = b2.
  Proof.
    induction l; intros.
    - inv H; inv H0; auto.
    - inv H; inv H0. rewrite H2 in H3; inv H3.
      eapply IHl; eauto.
  Qed.

End Contiguous.

Definition isCorrectPC_range p b e a0 an :=
  ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (WCap p b e ai).

Lemma isCorrectPC_inrange p b (e a0 an a: Addr) :
  isCorrectPC_range p b e a0 an →
  (a0 <= a < an)%Z →
  isCorrectPC (WCap p b e a).
Proof.
  unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
Qed.

Lemma isCorrectPC_contiguous_range p b e a0 an a l :
  isCorrectPC_range p b e a0 an →
  contiguous_between l a0 an →
  a ∈ l →
  isCorrectPC (WCap p b e a).
Proof.
  intros Hr Hc Hin.
  eapply isCorrectPC_inrange; eauto.
  eapply contiguous_between_middle_bounds'; eauto.
Qed.

Lemma isCorrectPC_range_perm p b e a0 an :
  isCorrectPC_range p b e a0 an →
  (a0 < an)%a →
  p = RX ∨ p = RWX.
Proof.
  intros Hr H0n.
  assert (isCorrectPC (WCap p b e a0)) as HH by (apply Hr; solve_addr).
  inversion HH; auto.
Qed.

(* Lemma isCorrectPC_range_perm_non_E p b e a0 an : *)
(*   isCorrectPC_range p b e a0 an → *)
(*   (a0 < an)%a → *)
(*   p ≠ E. *)
(* Proof. *)
(*   intros HH1 HH2. pose proof (isCorrectPC_range_perm _ _ _ _ _ HH1 HH2). *)
(*   naive_solver. *)
(* Qed. *)

Lemma isCorrectPC_range_restrict p b e a0 an a0' an' :
  isCorrectPC_range p b e a0 an →
  (a0 <= a0')%a ∧ (an' <= an)%a →
  isCorrectPC_range p b e a0' an'.
Proof.
  intros HR [? ?] a' [? ?]. apply HR. solve_addr.
Qed.
