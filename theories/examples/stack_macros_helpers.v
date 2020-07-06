From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec List.
From cap_machine Require Import cap_lang region contiguous.

Section helpers.

  (* ---------------------------- Helper Lemmas --------------------------------------- *)
  (* TODO: move to lang *)
  Lemma isCorrectPC_bounds_alt p g b e (a0 a1 a2 : Addr) :
    isCorrectPC (inr (p, g, b, e, a0))
    → isCorrectPC (inr (p, g, b, e, a2))
    → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
    → isCorrectPC (inr (p, g, b, e, a1)).
  Proof.
    intros Hvpc0 Hvpc2 [Hle0 Hle2].
    apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
    - apply isCorrectPC_bounds with a0 a2; auto.
    - apply z_of_eq in Heq2. rewrite Heq2. auto.
  Qed.

  Lemma isWithinBounds_bounds_alt p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma isWithinBounds_bounds_alt' p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 < a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Definition isCorrectPC_range p g b e a0 an :=
    ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (inr (p, g, b, e, ai)).

  Lemma isCorrectPC_inrange p g b (e a0 an a: Addr) :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a < an)%Z →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
  Qed.

  Lemma isCorrectPC_contiguous_range p g b e a0 an a l :
    isCorrectPC_range p g b e a0 an →
    contiguous_between l a0 an →
    a ∈ l →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    intros Hr Hc Hin.
    eapply isCorrectPC_inrange; eauto.
    eapply contiguous_between_middle_bounds'; eauto.
  Qed.

  Lemma isCorrectPC_range_perm p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p = RX ∨ p = RWX ∨ p = RWLX.
  Proof.
    intros Hr H0n.
    assert (isCorrectPC (inr (p, g, b, e, a0))) as HH by (apply Hr; solve_addr).
    inversion HH; auto.
  Qed.

  

  Lemma delete_eq {A : Type} (a : list A) i :
    strings.length a ≤ i -> a = delete i a.
  Proof.
    revert i. induction a; intros i Hle.
    - done.
    - destruct i; [inversion Hle|].
      simpl. f_equiv. apply IHa. simpl in Hle. lia.
  Qed. 
  
  Lemma delete_insert_list {A : Type} i (l : list A) (a : A) :
    <[i := a]> (delete 0 l) = delete 0 (<[S i := a]> l).
  Proof.
    induction l.
    - done.
    - simpl in *. destruct l; auto. 
  Qed.

  Lemma insert_delete_list {A : Type} (l : list A) (a : A) :
    delete 0 (<[0 := a]> l) = delete 0 l.
  Proof.
    induction l; done.
  Qed. 

End helpers. 

  
