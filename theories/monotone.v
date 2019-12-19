From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.
  
  Lemma region_state_nwl_monotone W W' a l :
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W W' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl /std_sta /std_rel.
    intros Hsome Hrelated Hstate.
    destruct l.
    - apply (related_sts_rel_std W W') in Hsome as Hsome'; 
        [|destruct Hrelated as [Hrelated1 Hrelated2]; split; apply related_sts_pub_priv; auto].
      destruct Hrelated as [ [Hdom_sta [Hdom_rel Hrelated] ] _]. simpl in *.
      specialize (Hrelated (countable.encode a) _ _ _ _ Hsome Hsome') as (_ & _ & Hrelated).
      assert (is_Some (W'.1.1 !! countable.encode a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
      specialize (Hrelated (countable.encode Permanent) y Hstate Hy).
      destruct (decide (y = countable.encode Permanent)); subst; auto.
      apply std_rel_pub_rtc_Permanent in Hrelated; auto. contradiction. 
    - apply (related_sts_rel_std W W') in Hsome as Hsome';
        [|destruct Hrelated as [Hrelated1 Hrelated2]; split; apply related_sts_pub_priv; auto].
      destruct Hrelated as [ [Hdom_sta [Hdom_rel Hrelated] ] _]. simpl in *.
      specialize (Hrelated (countable.encode a) _ _ _ _ Hsome Hsome') as (_ & _ & Hrelated).
      assert (is_Some (W'.1.1 !! countable.encode a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. }
      destruct Hstate as [HTemp | HPerm].
      + left. 
        specialize (Hrelated (countable.encode Temporary) y HTemp Hy).
        destruct (decide (y = countable.encode Temporary)); subst; auto.
        apply std_rel_pub_rtc_Temporary in Hrelated; auto. contradiction. 
      + right.
        specialize (Hrelated (countable.encode Permanent) y HPerm Hy).
        destruct (decide (y = countable.encode Permanent)); subst; auto.
        apply std_rel_pub_rtc_Permanent in Hrelated; auto. contradiction. 
  Qed.

  Lemma region_state_nwl_monotone_nl W W' a :
    rel_is_std_i W (countable.encode a) →
    related_sts_priv_world W W' →
    region_state_nwl W a Global -> region_state_nwl W' a Global.
  Proof.
    rewrite /region_state_nwl /std_sta /std_rel.
    intros Hsome Hrelated Hstate.
    apply (related_sts_rel_std W W') in Hsome as Hsome'; auto. 
    
    destruct Hrelated as [ [Hdom_sta [Hdom_rel Hrelated] ] _].
    specialize (Hrelated (countable.encode a) _ _ _ _ Hsome Hsome') as (_ & _ & Hrelated).
    assert (is_Some (W'.1.1 !! countable.encode a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated (countable.encode Permanent) y Hstate Hy).
    destruct (decide (y = countable.encode Permanent)); subst; auto.
    apply std_rel_rtc_Permanent in Hrelated; auto. contradiction. 
  Qed.

  Lemma region_state_pwl_monotone W W' a :
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W W' →
    region_state_pwl W a -> region_state_pwl W' a.
  Proof.
    rewrite /region_state_pwl /std_sta /std_rel.
    intros Hsome Hrelated Hstate.
    apply (related_sts_rel_std W W') in Hsome as Hsome'; 
      [|destruct Hrelated as [Hrelated1 Hrelated2]; split; apply related_sts_pub_priv; auto].
    destruct Hrelated as [ [Hdom_sta [Hdom_rel Hrelated] ] _]. simpl in *.
    specialize (Hrelated (countable.encode a) _ _ _ _ Hsome Hsome') as (_ & _ & Hrelated).
    assert (is_Some (W'.1.1 !! countable.encode a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated (countable.encode Temporary) y Hstate Hy).
    destruct (decide (y = countable.encode Temporary)); subst; auto.
    apply std_rel_pub_rtc_Temporary in Hrelated; auto. contradiction. 
  Qed.

  Lemma region_state_Revoked_monotone (W W' : WORLD) (a : Addr) :
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W W' →
    (std_sta W) !! (countable.encode a) = Some (countable.encode Revoked) ->
    (std_sta W') !! (countable.encode a) = Some (countable.encode Revoked) ∨
    (std_sta W') !! (countable.encode a) = Some (countable.encode Temporary).
  Proof.
    rewrite /region_state_pwl /std_sta /std_rel.
    intros Hsome Hrelated Hstate.
    apply (related_sts_rel_std W W') in Hsome as Hsome'; 
      [|destruct Hrelated as [Hrelated1 Hrelated2]; split; apply related_sts_pub_priv; auto].
    destruct Hrelated as [ [Hdom_sta [Hdom_rel Hrelated] ] _]. simpl in *.
    specialize (Hrelated (countable.encode a) _ _ _ _ Hsome Hsome') as (_ & _ & Hrelated).
    assert (is_Some (W'.1.1 !! countable.encode a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated (countable.encode Revoked) y Hstate Hy).
    apply std_rel_pub_rtc_Revoked in Hrelated; auto.
    destruct Hrelated as [Htemp | Hrev]; subst; auto. 
  Qed.
  
  Lemma rel_is_std_i_monotone (W W' : WORLD) (a : Addr) :
    related_sts_pub_world W W' →
    rel_is_std_i W (countable.encode a) →
    rel_is_std_i W' (countable.encode a).
  Proof.
    rewrite /rel_is_std_i.
    intros [(Hdom_sta & Hdom_rel & Htransition) _] Hstd.
    apply elem_of_subseteq in Hdom_rel.
    assert ((countable.encode a) ∈ dom (gset positive) (std_rel W)) as Hin.
    { apply elem_of_dom. eauto. }
    specialize (Hdom_rel (countable.encode a) Hin).
    apply elem_of_dom in Hdom_rel as [ [r1' r2'] Hr'].
    apply elem_of_dom in Hin as [ [r1 r2] Hr].
    specialize (Htransition (countable.encode a) r1 r2 r1' r2' Hr Hr') as (Heq1 & Heq2 & _). 
    simplify_eq. rewrite Hstd in Hr. inversion Hr. subst. auto.
  Qed. 
    
  Lemma interp_monotone W W' w :
    (⌜related_sts_pub_world W W'⌝ →
    interp W w -∗ interp W' w)%I. 
  Proof.
    iIntros (Hrelated) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
      iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
      iPureIntro. split; [apply region_state_nwl_monotone with W|apply related_sts_rel_std with W]; auto.
      apply related_sts_pub_priv_world; auto.
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
      iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
      iPureIntro. split; [apply region_state_nwl_monotone with W|apply related_sts_rel_std with W]; auto.
      apply related_sts_pub_priv_world; auto.
    - destruct l; auto. 
      iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
      iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
      iPureIntro. split; [apply region_state_pwl_monotone with W|apply related_sts_rel_std with W]; auto.
      apply related_sts_pub_priv_world; auto. 
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists _. iSplitR;[eauto|].
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
        iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
        iPureIntro. split; [apply region_state_nwl_monotone with W|apply related_sts_rel_std with W]; auto.
        apply related_sts_pub_priv_world; auto. }
      iAlways.
      iIntros (a' r' W'' Hin).
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_priv_trans_world with W'; auto. }
        iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_trans_world with W'; auto. } 
        iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated").
        iFrame.
    - iAlways. iIntros (r W'').
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_priv_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists p. iSplit;[auto|].
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
        iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
        iPureIntro. split; [apply region_state_nwl_monotone with W|apply related_sts_rel_std with W]; auto.
        apply related_sts_pub_priv_world; auto. }
      iAlways. iIntros (a' r W'' Hin).
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans_world with W'; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans_world with W'; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
    - destruct l;auto. 
      iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists p. iSplit;[auto|].
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
        iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
        iPureIntro. split; [apply region_state_pwl_monotone with W|apply related_sts_rel_std with W]; auto.
        apply related_sts_pub_priv_world; auto. }
      iAlways. iIntros (a' r W'' Hin).
      iIntros (Hrelated').
      iAssert (future_world Local W W'')%I as "Hrelated".
      { iPureIntro.
        apply related_sts_pub_trans_world with W'; auto.
      }
      iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
      iFrame.
  Qed.

  Lemma interp_monotone_nl W W' w :
    (⌜related_sts_priv_world W W'⌝ → ⌜isLocalWord w = false⌝ →
    interp W w -∗ interp W' w)%I. 
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
      iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      split; [apply region_state_nwl_monotone_nl with W|apply related_sts_rel_std with W]; auto.
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
      iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      split; [apply region_state_nwl_monotone_nl with W|apply related_sts_rel_std with W]; auto.
    - destruct l; auto. discriminate. 
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists _. iSplitR;[eauto|].
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
        iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
        iPureIntro. destruct l; try discriminate.
        split; [apply region_state_nwl_monotone_nl with W|apply related_sts_rel_std with W]; auto. }
      iAlways.
      iIntros (a' r' W'' Hin).
      destruct l; simpl; try discriminate.
      iIntros (Hrelated').
      iAssert (future_world Global W W'')%I as "Hrelated".
      { iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
      iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated").
      iFrame.
    - iAlways. iIntros (r W'').
      destruct l; simpl; try discriminate.
      iIntros (Hrelated').
      iAssert (future_world Global W W'')%I as "Hrelated".
      { iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
      iSpecialize ("Hw" $! r W'' with "Hrelated").
      iFrame.
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists p. iSplit;[auto|].
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "#[Hrw [Hst Hrel] ]". iFrame "#".
        iDestruct "Hst" as %Hst; iDestruct "Hrel" as %Hrel. 
        iPureIntro. destruct l; try discriminate. 
        split; [apply region_state_nwl_monotone_nl with W|apply related_sts_rel_std with W]; auto. }
      iAlways. iIntros (a' r W'' Hin).
      destruct l; simpl; try discriminate.
      iIntros (Hrelated').
      iAssert (future_world Global W W'')%I as "Hrelated".
      { iPureIntro.
        apply related_sts_priv_trans_world with W'; auto.
      }
      iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
      iFrame.
    - destruct l; try discriminate. done. 
  Qed.
    
End monotone. 