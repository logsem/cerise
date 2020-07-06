From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants region_invariants_uninitialized.
Import uPred.

Section region_alloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* Lemmas for extending the region map *)

  Lemma static_extend_preserve W (M : relT) (Mρ : gmap Addr region_type) (l : Addr) g ρ :
    l ∉ dom (gset Addr) (std W) ->
    dom (gset Addr) (std W) = dom (gset Addr) M ->
    dom (gset Addr) Mρ = dom (gset Addr) M ->
    (∀ a' : Addr, a' ∈ dom (gset Addr) g → Mρ !! a' = Some (Static g)) ->
    ∀ a' : Addr, a' ∈ dom (gset Addr) g → <[l:=ρ]> Mρ !! a' = Some (Static g).
  Proof.
    intros Hl Hdom1 Hdom2 Hall.
    intros a' Hin. pose proof (Hall _ Hin) as Hcontr.
    assert (a' ∈ dom (gset Addr) Mρ) as Hincontr;[apply elem_of_gmap_dom;eauto|].
    rewrite Hdom2 in Hincontr. apply elem_of_gmap_dom in Hincontr. clear Hcontr.
    assert (is_Some (std W !! a')) as Hcontr.
    { apply elem_of_gmap_dom. rewrite Hdom1. apply elem_of_gmap_dom. eauto. }
    apply elem_of_gmap_dom in Hcontr.
    assert (a' ≠ l) as Hne';[intros Heq;subst;contradiction|].
    rewrite lookup_insert_ne;auto.
  Qed.

  Lemma extend_region_temp_pwl E W l p v φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     l ∉ dom (gset Addr) (std W) →
     (pwl p) = true →
     (future_pub_mono φ v →
     sts_full_world W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world (<s[l := Temporary ]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame "∗ #".
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,_,φ. iSplitR;[auto|]. iFrame "∗ #".
        iSplitR;[auto|]. iExists v. iFrame.
        rewrite Hpwl. iFrame "#". iSplitR;[auto|].
        iNext. iApply "Hmono"; eauto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_temp_nwl E W l p v φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     l ∉ dom (gset Addr) (std W) →
     (pwl p) = false →
     (future_priv_mono φ v →
     sts_full_world W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world (<s[l := Temporary ]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
     iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,_,φ. iSplitR;[auto|]. iFrame "∗ #".
        iSplitR;[done|]. iExists _. iFrame.
        rewrite Hpwl. iFrame "#". repeat iSplit;auto.
        iNext. iApply "Hmono"; eauto.
        iPureIntro. by apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_perm E W l p v φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     l ∉ dom (gset Addr) (std W) →
     (future_priv_mono φ v →
     sts_full_world W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Permanent ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world (<s[l := Permanent ]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W l Permanent) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Permanent. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,_,φ. iSplitR;[auto|]. iFrame "∗ #".
        iSplitR;[done|]. iExists _. iFrame. repeat iSplit;auto.
        iNext. iApply "Hmono"; eauto.
        iPureIntro. by apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  (* The following allocates a Revoked region. This allocates the saved predicate and the region state, *)
  (* but since a revoked region is empty, there is no need to assume any resources for that region *)

  Lemma extend_region_revoked E W l p φ `{∀ Wv, Persistent (φ Wv)} :
     l ∉ dom (gset Addr) (std W) →
     (sts_full_world W -∗ region W ={E}=∗ region (<s[l := Revoked ]s>W)
                                               ∗ rel l p φ
                                               ∗ sts_full_world (<s[l := Revoked ]s>W))%I.
  Proof.
    iIntros (Hnone1) "Hfull Hreg".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,p)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l Revoked
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W l Revoked) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Revoked. iFrame. iSplitR.
        iPureIntro;apply lookup_insert.
        iExists _,_,_. iFrame "#". iSplit;eauto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_perm_sepL2 E W l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     Forall (λ k, std W !! k = None) l1 →
     (sts_full_world W -∗ region W -∗
     ([∗ list] k;v ∈ l1;l2, k ↦ₐ[p] v ∗ φ (W, v) ∗ future_priv_mono φ v)

     ={E}=∗

     region (std_update_multiple W l1 Permanent)
     ∗ ([∗ list] k ∈ l1, rel k p φ)
     ∗ sts_full_world (std_update_multiple W l1 Permanent))%I.
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros * ? [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (cap_duplicate_false with "[$H1 $H2]"). auto. }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iDestruct (extend_region_perm with "Hf Hsts Hr Ha [Hφ]") as ">(? & ? & ?)"; auto.
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
        eapply Forall_impl; eauto.
        intros. by rewrite not_elem_of_dom. }
      iModIntro. cbn. iFrame. }
  Qed.

  Lemma extend_region_static_single E W l p v φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     l ∉ dom (gset Addr) (std W) →
     (sts_full_world W -∗ region W -∗ l ↦ₐ[p] v
     ={E}=∗
     region (<s[l := Static {[l := v]}]s>W)
     ∗ rel l p φ
     ∗ sts_full_world (<s[l := Static {[l := v]} ]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1) "Hfull Hreg Hl".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HdomM & HdomMρ & Hpreds)".
    iDestruct "HdomM" as %HdomM. iDestruct "HdomMρ" as %HdomMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l (Static {[l:=v]})
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    eapply (related_sts_pub_world_fresh W l (Static {[l:=v]})) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomM. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists (Static {[l:=v]}). iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,_,φ. iSplitR;[auto|]. iFrame "∗ #".
        iSplitR;[done|]. iExists _. iFrame. repeat iSplit;auto.
        iPureIntro. apply lookup_singleton.
        iPureIntro. intro. rewrite dom_singleton elem_of_singleton.
        intros ->. apply lookup_insert. }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_static_single_sepM E W (m: gmap Addr Word) p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     (∀ k, is_Some (m !! k) → std W !! k = None) →
     (sts_full_world W -∗ region W -∗
     ([∗ map] k↦v ∈ m, k ↦ₐ[p] v)

     ={E}=∗

     region (override_uninitializedW m W)
     ∗ ([∗ map] k↦_ ∈ m, rel k p φ)
     ∗ sts_full_world (override_uninitializedW m W))%I.
  Proof.
    induction m using map_ind.
    { intros. rewrite !override_uninitializedW_empty !big_sepM_empty.
      iIntros. by iFrame. }
    { iIntros (? HnW) "Hsts Hr H". rewrite big_sepM_insert //.
      iDestruct "H" as "(Hk & Hm)".
      rewrite !override_uninitializedW_insert.
      iMod (IHm with "Hsts Hr Hm") as "(Hr & Hm & Hsts)"; auto.
      { intros. apply HnW. rewrite lookup_insert_is_Some.
        destruct (decide (i = k)); auto. }
      iDestruct (extend_region_static_single with "Hsts Hr Hk")
        as ">(Hr & Hrel & Hsts)"; auto.
      { rewrite override_uninitializedW_dom'.
        rewrite not_elem_of_union !not_elem_of_dom. split; auto.
        apply HnW. rewrite lookup_insert //. eauto. }
      iFrame. iModIntro. iApply big_sepM_insert; eauto. }
  Qed.

End region_alloc.
