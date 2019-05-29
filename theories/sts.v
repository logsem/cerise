From iris.algebra Require Import auth agree gmap.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import tactics.
Import uPred.


(** The CMRA for the heap of STS.
    We register the state and the transition relation. *)
Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizC positive))).

Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizC (positive → positive → Prop)))).

Definition STS_states := gmap positive positive.
Definition STS_rels := gmap positive (positive → positive → Prop).

(** The CMRA for the thread pool. *)
Class STSG Σ :=
  { sts_state_inG :> inG Σ sts_stateUR;
    sts_rel_inG :> inG Σ sts_relUR;
    sts_state_name : gname;
    sts_rel_name : gname; }.

Section definitionsS.
  Context `{STSG Σ} `{Countable A}.

  Definition sts_state (i : positive) (x : A) : iProp Σ
    := own (A := sts_stateUR) sts_state_name (◯ {[ i := Excl (encode x) ]}).

  Definition convert_rel (R : A → A → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  Definition sts_rel (i : positive) (R : A → A → Prop) : iProp Σ :=
    own (A := sts_relUR) sts_rel_name (◯ {[ i := to_agree (convert_rel R) ]}).

  (* very weird bug!!!
     Any two of these conjuncts are ok on their own but not all three!
     But, it works with program!!!!!!!!!!! *)
  Program Definition sts_full `{STSG Σ} (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (⌜dom (gset positive) fs = dom (gset positive) fr⌝
        ∗ own (A := sts_stateUR) sts_state_name (● (Excl <$> fs))
          ∗ own (A := sts_relUR) sts_rel_name (● (to_agree <$> fr)))%I.

  Definition related_sts (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i x y r r', fs !! i = Some x → gs !! i = Some y →
                  fr !! i = Some r → gr !! i = Some r' → r = r' ∧ rtc r x y.

  Global Instance sts_rel_Persistent i R : Persistent (sts_rel i R).
  Proof. apply _. Qed.

  Global Instance sts_rel_Timeless i R : Timeless (sts_rel i R).
  Proof. apply _. Qed.

  Global Instance sts_state_Timeless i x : Timeless (sts_state i x).
  Proof. apply _. Qed.

  Global Instance sts_full_Timeless fs fr : Timeless (sts_full fs fr).
  Proof. apply _. Qed.

End definitionsS.

Typeclasses Opaque sts_state sts_rel sts_full related_sts.

Section STS.
  Context `{STSG Σ} `{Countable A}.
  Implicit Types x y : positive.
  Implicit Types a b : A.
  Implicit Types fs gs : STS_states.
  Implicit Types fr gr : STS_rels.
  Implicit Types R : A → A → Prop.
  Implicit Types Rp : positive → positive → Prop.

  Lemma related_sts_refl fs fr : related_sts fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_trans fs fr gs gr hs hr :
    related_sts fs gs fr gr → related_sts gs hs gr hr → related_sts fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i x y r r' Hfs Hhs Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf1; eauto; destruct Hf2; eauto.
    edestruct Hf3; eauto; edestruct Hg3; eauto; simplify_eq.
    split; etrans; eauto.
  Qed.

  Lemma sts_full_rel fs fr i R :
    sts_full fs fr -∗ sts_rel i R -∗ ⌜fr !! i = Some (convert_rel R)⌝.
  Proof.
    rewrite /sts_full /sts_rel.
    iIntros "[% [_ H1]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= left_id singleton_included;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) eqn:Heq; rewrite Heq /= in Hz, Hv; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu; intros Hz'%to_agree_inj%leibniz_equiv; simplify_eq.
    by eauto.
  Qed.

  Lemma sts_full_state fs fr i a :
    sts_full fs fr -∗ sts_state i a -∗ ⌜fs !! i = Some (encode a)⌝.
  Proof.
    rewrite /sts_full /sts_state.
    iIntros "[% [H1 _]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= left_id singleton_included;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_alloc fs fr a R :
    sts_full fs fr ==∗
             ∃ i, sts_full (<[i := encode a ]>fs) (<[i := convert_rel R ]>fr)
                  ∗ ⌜i ∉ dom (gset positive) fs⌝ ∗ ⌜i ∉ dom (gset positive) fr⌝
                  ∗ sts_state i a ∗ sts_rel i R.
  Proof.
    rewrite /sts_full /sts_rel /sts_state.
    iIntros "[Hd [H1 H2]]".
    iDestruct "Hd" as %Hd.
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom (gset positive) fs) := encode a]> fs)
            ⋅ ◯ {[fresh (dom (gset positive) fs) := Excl (encode a)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      apply is_fresh. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs) := convert_rel R]> fr)
            ⋅ ◯ {[fresh (dom (gset positive) fs) := to_agree (convert_rel R)]})
            with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap Hd.
      apply is_fresh. }
    iModIntro.
    iExists _; iFrame.
    repeat iSplit; iPureIntro;
      rewrite ?dom_insert_L ?Hd; by try apply is_fresh.
  Qed.

  Lemma sts_update fs fr i a b :
    sts_full fs fr -∗ sts_state i a ==∗
    sts_full (<[i := encode b ]>fs) fr ∗ sts_state i b.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state with "Hsf Hi") as %Hfs.
    rewrite /sts_full /sts_rel /sts_state.
    iDestruct "Hsf" as "[Hd [H1 H2]]".
    iDestruct "Hd" as %Hd.
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode b)]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode b)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    rewrite fmap_insert dom_insert_L subseteq_union_1_L;
      first by iModIntro; iFrame.
    apply elem_of_subseteq_singleton, elem_of_dom; eauto.
  Qed.

End STS.
