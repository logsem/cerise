From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Lemma full_sts_world_is_Some_rel_std W (a : Addr) :
    is_Some ((std_sta W) !! (countable.encode a)) →
    sts_full_world sts_std W -∗ ⌜(std_rel W) !! (countable.encode a) = Some (convert_rel (Rpub : relation region_type),
                                                                             convert_rel (Rpriv : relation region_type))⌝.
  Proof. 
    iIntros (Hsome) "[[% [% _] ] _]".
    iPureIntro. apply elem_of_subseteq in H3.
    apply elem_of_gmap_dom in Hsome. 
    specialize (H3 _ Hsome).
    specialize (H4 (countable.encode a)). apply H4. 
    apply elem_of_gmap_dom. auto.
  Qed.

  Lemma related_sts_preserve_std W W' :
    related_sts_priv_world W W' →
    (∀ i, is_Some ((std_rel W) !! i) →
          (std_rel W) !! i = Some (convert_rel (Rpub : relation region_type),
                                   convert_rel (Rpriv : relation region_type))) →
    (∀ i, is_Some ((std_rel W) !! i) →
          (std_rel W') !! i = Some (convert_rel (Rpub : relation region_type),
                                    convert_rel (Rpriv : relation region_type))).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]; simpl.
    destruct W' as [ [Wstd_sta' Wstd_rel'] Wloc']; simpl.
    intros [ [Hdom_sta [Hdom_rel Hrelated] ] _] Hstd i Hi. simpl in *.
    apply elem_of_gmap_dom in Hi. apply elem_of_subseteq in Hdom_rel.
    specialize (Hdom_rel _ Hi).
    apply elem_of_gmap_dom in Hdom_rel as [ [r1' r2'] Hr'].
    apply elem_of_gmap_dom in Hi as Hr.
    specialize (Hstd _ Hr). 
    specialize (Hrelated i _ _ _ _ Hstd Hr') as (-> & -> & Hrelated). 
    auto.
  Qed.

  Lemma related_sts_rel_std W W' i :
    related_sts_priv_world W W' →
    (std_rel W) !! i = Some (convert_rel (Rpub : relation region_type),
                             convert_rel (Rpriv : relation region_type)) ->
    (std_rel W') !! i = Some (convert_rel (Rpub : relation region_type),
                              convert_rel (Rpriv : relation region_type)).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]; simpl.
    destruct W' as [ [Wstd_sta' Wstd_rel'] Wloc']; simpl.
    intros [ [Hdom_sta [Hdom_rel Hrelated] ] _] Hi. simpl in *.
    assert (is_Some (Wstd_rel' !! i)) as [ [r1' r2'] Hr'].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_rel.
      apply Hdom_rel. apply elem_of_gmap_dom. eauto. }
    specialize (Hrelated i _ _ _ _ Hi Hr') as (-> & -> & Hrelated).
    eauto. 
  Qed.

  Lemma std_rel_pub_Permanent x :
    rtc (convert_rel std_rel_pub) (countable.encode Permanent) x → x = countable.encode Permanent.
  Proof.
    intros Hrtc.
    Admitted. 
    
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
      rewrite /std_rel_pub /convert_rel /= in Hrelated. 
      rewrite -(std_rel_pub_Permanent y); auto. 
    - admit.
  Admitted. 

  Lemma interp_monotone W W' w :
    (⌜related_sts_pub_world W W'⌝ →
    interp W w -∗ interp W' w)%I. 
  Proof.
    Admitted. 
    (* iIntros (Hrelated) "#Hw". *)
    (* rewrite /interp /= fixpoint_interp1_eq /=.  *)
    (* destruct w; rewrite fixpoint_interp1_eq /=; auto. *)
    (* destruct c,p,p,p,p; auto.  *)
    (* - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]". *)
    (*   iExists _. iSplitR;[eauto|]. iFrame "#". *)
    (*   iAlways. *)
    (*   iIntros (a' r' W'' Hin). *)
    (*   destruct l; simpl. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Global W W'')%I as "Hrelated". *)
    (*     { iPureIntro.  *)
    (*       apply related_sts_pub_priv_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated"). *)
    (*     iFrame. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Local W W'')%I as "Hrelated". *)
    (*     { iPureIntro. *)
    (*       apply related_sts_pub_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r' W'' Hin with "Hrelated"). *)
    (*     iFrame. *)
    (* - iAlways. iIntros (r W''). *)
    (*   destruct l; simpl. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Global W W'')%I as "Hrelated". *)
    (*     { iPureIntro. *)
    (*       apply related_sts_pub_priv_trans with W'.1 W'.2; auto. *)
    (*     } *)
    (*     iSpecialize ("Hw" $! r W'' with "Hrelated"). *)
    (*     iFrame. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Local W W'')%I as "Hrelated". *)
    (*     { iPureIntro. *)
    (*       apply related_sts_pub_trans with W'.1 W'.2; auto. *)
    (*     } *)
    (*     iSpecialize ("Hw" $! r W'' with "Hrelated"). *)
    (*     iFrame. *)
    (* - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]". *)
    (*   iExists p. iSplit;[auto|]. *)
    (*   iFrame "#". iAlways. iIntros (a' r W'' Hin).  *)
    (*   destruct l; simpl. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Global W W'')%I as "Hrelated". *)
    (*     { iPureIntro.  *)
    (*       apply related_sts_pub_priv_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated"). *)
    (*     iFrame.  *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Local W W'')%I as "Hrelated". *)
    (*     { iPureIntro. *)
    (*       apply related_sts_pub_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated"). *)
    (*     iFrame. *)
    (* - iDestruct "Hw" as (p Hfl) "[Hbe Hexec]". *)
    (*   iExists p. iSplit;[auto|]. *)
    (*   iFrame "#". iAlways. iIntros (a' r W'' Hin).  *)
    (*   destruct l; simpl. *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Global W W'')%I as "Hrelated". *)
    (*     { iPureIntro.  *)
    (*       apply related_sts_pub_priv_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated"). *)
    (*     iFrame.  *)
    (*   + iIntros (Hrelated'). *)
    (*     iAssert (future_world Local W W'')%I as "Hrelated". *)
    (*     { iPureIntro. *)
    (*       apply related_sts_pub_trans with W'.1 W'.2; auto.  *)
    (*     } *)
    (*     iSpecialize ("Hexec" $! a' r W'' Hin with "Hrelated"). *)
    (*     iFrame.  *)
  (* Qed. *)
    
End monotone. 