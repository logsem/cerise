From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec List.
From cap_machine Require Import lang region contiguous. 

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

  (* Helper lemma to extract registers from a big_sepL2 *)
  Lemma big_sepL2_extract_l {Σ : gFunctors} {A B : Type} (i : nat) (ai : A) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    a !! i = Some ai ->
    (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
     ([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ ∃ b, φ ai b)%I.
  Proof. 
    iIntros (Hsome) "Hl".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.      
    assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
    assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
    rewrite -Heqa -Heqb.
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { apply lookup_lt_Some in Hsome.
      do 2 (rewrite take_length_le;[|lia]). done. 
    }
    apply take_drop_middle in Hsome as Hcons.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). congruence. }
    rewrite -Hh.
    iDestruct (big_sepL2_length with "Hdrop") as %Hlength'.      
    destruct (drop i b);[inversion Hlength'|].
    iDestruct "Hdrop" as "[Hφ Hdrop]".
    iSplitR "Hφ";[|eauto].
    rewrite Hcons. iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl".
    rewrite Heqb. rewrite (delete_take_drop a).
    rewrite (delete_take_drop b).
    assert (drop (S i) b = l) as Hb.
    { apply app_inv_head with (take i b ++ [b0]). repeat rewrite -app_assoc.
      repeat rewrite -cons_middle. rewrite (region.drop_S _ _ _ b0 l);auto.
      apply app_inv_head with (take i b). rewrite Heqb. apply take_drop. }
    rewrite Hb. iFrame. 
  Qed.

  Lemma big_sepL2_extract {Σ : gFunctors} {A B : Type} (i : nat) (ai : A) (bi : B) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    a !! i = Some ai -> b !! i = Some bi ->
    (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
     ([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ φ ai bi)%I.
  Proof. 
    iIntros (Hsome Hsome') "Hl".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.      
    assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
    assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
    rewrite -Heqa -Heqb.
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { apply lookup_lt_Some in Hsome.
      do 2 (rewrite take_length_le;[|lia]). done. 
    }
    apply take_drop_middle in Hsome as Hcons.
    apply take_drop_middle in Hsome' as Hcons'.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). congruence. }
    assert (bi :: drop (S i) b = drop i b) as Hhb.
    { apply app_inv_head with (take i b). congruence. }
    rewrite -Hh. rewrite -Hhb.
    iDestruct "Hdrop" as "[Hφ Hdrop]".
    iSplitR "Hφ";[|eauto].
    rewrite Hcons. rewrite Hcons'. iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl".
    rewrite (delete_take_drop b). rewrite (delete_take_drop a). iFrame. 
  Qed.

  Lemma delete_eq {A : Type} (a : list A) i :
    strings.length a ≤ i -> a = delete i a.
  Proof.
    revert i. induction a; intros i Hle.
    - done.
    - destruct i; [inversion Hle|].
      simpl. f_equiv. apply IHa. simpl in Hle. lia.
  Qed. 
  
  Lemma big_sepL2_close_l {Σ : gFunctors} {A B : Type} (i : nat) (ai : A) (bi : B) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    length a = length b ->
    a !! i = Some ai ->
    (([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ φ ai bi -∗
                                                               ([∗ list] a_i;b_i ∈ a;<[i:= bi]> b, φ a_i b_i) )%I.
  Proof. 
    iIntros (Hlen Hsome) "[Hl Hb]".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.
    repeat rewrite delete_take_drop.
    apply lookup_lt_Some in Hsome as Hlt.
    assert (i < strings.length b) as Hlt';[lia|].
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { repeat rewrite take_length. lia. }
    apply take_drop_middle in Hsome as Hcons.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). rewrite Hcons. by rewrite take_drop. }
    iAssert ([∗ list] y1;y2 ∈ ai :: drop (S i) a;bi :: drop (S i) b, φ y1 y2)%I
      with "[Hb Hdrop]" as "Hdrop";[iFrame|].
    rewrite Hh.
    iDestruct (big_sepL2_app with "Htake Hdrop") as "Hab".
    rewrite take_drop.
    assert (take i b ++ bi :: drop (S i) b = <[i:=bi]> b) as ->;[|iFrame].
    assert (<[i:=bi]> b !! i = Some bi) as Hsome'.
    { apply list_lookup_insert. lia. }
    apply take_drop_middle in Hsome'. rewrite -Hsome'.
    rewrite take_insert;[|lia]. rewrite drop_insert;[|lia]. done. 
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

  
