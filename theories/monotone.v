From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

    
  Lemma region_state_nwl_monotone W W' a l :
    (std_rel W) !! (countable.encode a) = Some (convert_rel (Rpub : relation region_type),
                                                convert_rel (Rpriv : relation region_type)) →
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

  Lemma region_state_pwl_monotone W W' a :
    (std_rel W) !! (countable.encode a) = Some (convert_rel (Rpub : relation region_type),
                                                convert_rel (Rpriv : relation region_type)) →
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
      iIntros (n y Hsome) "#[Hrw %]". iFrame "#".
      iPureIntro. apply region_state_nwl_monotone with W; auto. 
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists _. iSplitR;[eauto|]. iFrame "#".
      iAlways.
      iIntros (a' r' W'' Hin).
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated").
        iFrame.
    - iAlways. iIntros (r W'').
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists p. iSplit;[auto|].
      iFrame "#". iAlways. iIntros (a' r W'' Hin).
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
    - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists p. iSplit;[auto|].
      iFrame "#". iAlways. iIntros (a' r W'' Hin).
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated").
        iFrame.
  Qed.
    
End monotone. 