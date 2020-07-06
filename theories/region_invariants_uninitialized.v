From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra region_invariants multiple_updates
     region_invariants_revocation region_invariants_static sts.
Require Import stdpp.countable.
Import uPred.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Lemma related_sts_priv_world_revoked_to_uninit W a w :
    (std W) !! a = Some Revoked ->
    related_sts_priv_world W (<s[a:=Static {[a:=w]}]s> W).
  Proof.
    intros Hrev.
    split;[|apply related_sts_priv_refl]. 
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a)).
      + simplify_map_eq.
        right with Temporary;[left;constructor|]. 
        eright;[|left].
        right. constructor.
      + simplify_map_eq. left.
  Qed.

  Lemma related_sts_priv_world_uninit_to_revoked W a w :
    (std W) !! a = Some (Static {[a:=w]}) ->
    related_sts_priv_world W (<s[a:=Revoked]s> W).
  Proof.
    intros Hrev.
    split;[|apply related_sts_priv_refl]. 
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a)).
      + simplify_map_eq.
        right with Temporary;[left;constructor|]. 
        eright;[|left].
        right. constructor.
      + simplify_map_eq. left.
  Qed.

  Lemma related_sts_pub_world_uninit_to_temporary W a w :
    (std W) !! a = Some (Static {[a:=w]}) ->
    related_sts_pub_world W (<s[a:=Temporary]s> W).
  Proof.
    intros Hrev.
    split;[|apply related_sts_pub_refl]. 
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a)).
      + simplify_map_eq.
        right with Temporary;[|left].
        constructor.
      + simplify_map_eq. left.
  Qed.

  (* Lemma that extracts all temporary addresses in W from a list of addresses l *)
  Lemma extract_temps_from_range W (l : list Addr) :
    NoDup l ->
    ∃ l', NoDup l'
          ∧ Forall (λ (a : Addr), (std W) !! a = Some Temporary <-> a ∈ l') l
          ∧ Forall (λ (a : Addr), (std W) !! a = Some Temporary) l'.
  Proof.
    exists (filter (λ a, (std W) !! a = Some Temporary) l). 
    split.
    - apply NoDup_filter. auto.
    - split.
      + apply Forall_forall. intros x Hx. split;intros. 
        * apply elem_of_list_filter. split;auto.
        * apply elem_of_list_filter in H0 as [Htemp Hin]. auto.
      + apply Forall_forall. intros x Hx. apply elem_of_list_filter in Hx as [Htemp Hin]. auto. 
  Qed.

  Notation "m1 ∖∖ m2" := (map_difference_het m1 m2) (at level 40, left associativity).
   
  Definition override_uninitialized : (gmap Addr Word) -> STS_STD → STS_STD :=
    λ (m : gmap Addr Word) (Wstd : gmap Addr region_type),
    (map_imap (λ a w, Some (Static {[a:=w]})) m) ∪ (Wstd ∖∖ m).
  
  Definition override_uninitializedW : (gmap Addr Word) -> WORLD → WORLD :=
    λ m W, (override_uninitialized m W.1,W.2). 
  
  Notation "m1 >> W" := (override_uninitializedW m1 W) (at level 40, left associativity).

  Lemma override_uninitializedW_empty W :
    (∅ : gmap Addr Word) >> W = W.
  Proof.
    rewrite /override_uninitializedW /override_uninitialized difference_het_empty /=.
    destruct W. f_equiv. simpl. rewrite left_id_L. auto. 
  Qed.

  Lemma override_uninitializedW_insert W (m : gmap Addr Word) a w :
    (<[a:=w]> m) >> W = std_update (m >> W) a (Static {[a:=w]}).
  Proof.
    rewrite /override_uninitializedW /override_uninitialized difference_het_insert_r /=. 
    destruct W. rewrite /std_update /=. f_equiv. rewrite map_imap_insert. 
    rewrite -insert_union_l //.
    rewrite map_eq'.
    assert (map_imap (λ (a0 : Addr) (w0 : Word), Some (Static {[a0 := w0]})) m ##ₘ o ∖∖ m) as Hdisj.
    { apply map_disjoint_spec. intros i t y Ht Hy.
      apply difference_het_lookup_Some in Hy as [_ Hnone].
      rewrite map_lookup_imap in Ht. rewrite Hnone /= in Ht. done. }
    intros k v. split; intros Hx.
    - destruct (decide (a = k));[subst;simplify_map_eq;auto|simplify_map_eq]. 
      apply lookup_union_Some in Hx as [Hx | Hx]. 
      + apply lookup_union_Some_l. auto.
      + rewrite lookup_delete_ne in Hx;auto. apply lookup_union_Some_r; auto.
      + apply map_disjoint_delete_r. auto.
    - destruct (decide (a = k));[subst;simplify_map_eq;auto|simplify_map_eq].
      apply lookup_union_Some in Hx as [Hx | Hx]. 
      + apply lookup_union_Some_l. auto.
      + apply lookup_union_Some_r. apply map_disjoint_delete_r;auto.
        rewrite lookup_delete_ne;auto.
      + auto.
  Qed.

  Lemma override_uninitializedW_commute W (m : gmap Addr Word) :
     m >> (revoke W) = revoke (m >> W). 
   Proof.
     induction m using map_ind; [by rewrite !override_uninitializedW_empty|].
     rewrite !override_uninitializedW_insert. 
     rewrite IHm. 
     rewrite /std_update /revoke /loc /std /=. repeat f_equiv. rewrite map_eq'. 
     intros k v.
     destruct (decide (k = i)).
     - subst. rewrite lookup_insert revoke_monotone_lookup_same;rewrite lookup_insert; auto.
     - rewrite !lookup_insert_ne //. split; intros.
       + rewrite -(revoke_monotone_lookup (m >> W).1);auto.
         rewrite lookup_insert_ne;auto.
       + rewrite -(revoke_monotone_lookup (m >> W).1) in H0;auto.
         rewrite lookup_insert_ne;auto.
   Qed.

   Lemma override_uninitializedW_lookup_some W (m : gmap Addr Word) i w :
     m !! i = Some w ->
     (m >> W).1 !! i = Some (Static {[i:=w]}).
   Proof.
     intros Hsome. rewrite /override_uninitializedW /override_uninitialized /=.
     apply (lookup_union_Some_l (M:=gmap Addr)). rewrite map_lookup_imap Hsome /=. auto.
   Qed.

   Lemma override_uninitializedW_lookup_none W (m : gmap Addr Word) i :
     m !! i = None ->
     (m >> W).1 !! i = W.1 !! i.
   Proof.
     intros Hnone. rewrite /override_uninitializedW /override_uninitialized /=.
     destruct (W.1 !! i) eqn:Hsome.
     - apply (lookup_union_Some_r (M:=gmap Addr)).
       { apply map_disjoint_spec. intros j t y Ht Hy.
         apply difference_het_lookup_Some in Hy as [_ Hnone'].
         rewrite map_lookup_imap /= in Ht. rewrite Hnone' /= in Ht. done. }
       apply difference_het_lookup_Some. split;auto.
     - apply (lookup_union_None (M:=gmap Addr)).
       split.
       + rewrite map_lookup_imap Hnone /=. done.
       + apply difference_het_lookup_None;[|left;auto]. exact Temporary. 
   Qed.

   Lemma override_uninitializedW_lookup_nin W (m : gmap Addr Word) i :
     i ∉ (dom (gset Addr) m) -> (m >> W).1 !! i = W.1 !! i.
   Proof.
     intros Hnin.
     apply override_uninitializedW_lookup_none.
     apply (not_elem_of_dom (D:=gset Addr)).
     auto. 
   Qed. 

   Lemma override_uninitializedW_elem_of W (m : gmap Addr Word) i :
     i ∈ dom (gset Addr) W.1 -> i ∈ dom (gset Addr) (m >> W).1.
   Proof.
     intros Hin%elem_of_gmap_dom.
     apply elem_of_gmap_dom. destruct (m !! i) eqn:Hsome.
     - apply override_uninitializedW_lookup_some with (W:=W) in Hsome. eauto.
     - apply override_uninitializedW_lookup_none with (W:=W) in Hsome.
       rewrite -Hsome in Hin. eauto.
   Qed.

   Lemma override_uninitializedW_elem_of_overwritten W (m : gmap Addr Word) i :
     i ∈ dom (gset Addr) m -> i ∈ dom (gset Addr) (m >> W).1.
   Proof.
     intros Hin%elem_of_gmap_dom.
     apply elem_of_gmap_dom. destruct Hin as [w Hsome]. 
     apply override_uninitializedW_lookup_some with (W:=W) in Hsome. eauto.
   Qed. 
   
   Lemma override_uninitializedW_dom W (m : gmap Addr Word) :
     dom (gset Addr) W.1 ⊆ dom (gset Addr) (m >> W).1.
   Proof.
     apply elem_of_subseteq.
     intros x Hx.
     apply override_uninitializedW_elem_of. auto.
   Qed. 

   Lemma override_uninitializedW_dom' W (m: gmap Addr Word) :
     dom (gset Addr) (override_uninitializedW m W).1 =
     dom (gset Addr) m ∪ dom (gset Addr) W.1.
   Proof.
     rewrite /override_uninitializedW /override_uninitialized.
     rewrite dom_union_L dom_difference_het.
     rewrite dom_map_imap_full. 2: by intros; eauto.
     set Dm := dom (gset Addr) m.
     set DW := dom (gset Addr) W.1. clearbody Dm DW.
     rewrite elem_of_equiv_L. intro x.
     rewrite !elem_of_union !elem_of_difference.
     split.
     - intros [? | [? ?] ]. auto. auto.
     - intros [? | ?]. auto. destruct (decide (x ∈ Dm)); auto.
   Qed.

   Lemma related_sts_priv_world_override_uninitializedW W (m : gmap Addr Word) :
     Forall (λ a : Addr, ∃ ρ, (std W) !! a = Some ρ /\ ρ <> Permanent) (elements (dom (gset Addr) m)) →
     related_sts_priv_world W (m >> W).
   Proof.
     induction m using map_ind; intros.
     - rewrite override_uninitializedW_empty.
       apply related_sts_priv_refl_world.
     - rewrite override_uninitializedW_insert.
       erewrite dom_insert in H0.
       erewrite elements_union_singleton in H0; [|eapply not_elem_of_dom; eauto].
       eapply Forall_cons in H0. destruct H0 as [A B].
       eapply related_sts_priv_trans_world with (m >> W).
       + eapply IHm. eauto.
       + destruct A as [ρ [A1 A2] ].
         split;[|apply related_sts_priv_refl].
         split.
         * rewrite dom_insert_L. set_solver.
         * intros r p q Hp Hq.
           destruct (decide (r = i)).
           { subst r. rewrite override_uninitializedW_lookup_nin in Hp; [|eapply not_elem_of_dom; eauto].
             rewrite A1 in Hp; inv Hp. rewrite lookup_insert in Hq.
             inv Hq. destruct p; try congruence.
             - eright. right; constructor.
               left.
             - eright. left; constructor.
               eright. right; constructor.
               left.
             - eright. left; constructor.
               eright. right; constructor.
               left. }
           { simplify_map_eq. left. }
   Qed.

   (* following lemma takes a map of addresses to words, where the addresses are in a revoked state, and makes them
      uninitialized *)
   Lemma region_revoked_to_uninitialized W m :
    (sts_full_world (revoke W)
    ∗ region (revoke W)
    ∗ ([∗ map] a↦w ∈ m, ∃ p φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] w ∗ rel a p φ)
    ==∗ (sts_full_world (m >> (revoke W))
      ∗ region (m >> (revoke W))))%I.
   Proof.
    iIntros "(Hfull & Hr & Hl)".
    iInduction (m) as [|a w m] "IH" using map_ind. 
    - rewrite override_uninitializedW_empty. iFrame. done. 
    - rewrite override_uninitializedW_insert. 
      iDestruct (big_sepM_insert with "Hl") as "[Hx Hl]";[apply H|]. 
      iMod ("IH" with "Hfull Hr Hl") as "[Hfull Hr] /=".
      iDestruct "Hx" as (p φ Hpers Hne) "[Hx #Hrel]".
      rewrite region_eq /region_def.
      iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
      iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
      rewrite rel_eq /rel_def RELS_eq /RELS_def REL_eq /REL_def. 
      iDestruct "Hrel" as (γpred) "[HR Hsaved]". 
      iDestruct (reg_in with "[$HM $HR]") as %HMeq. 
      rewrite HMeq.
      iDestruct (big_sepM_delete with "Hr") as "[HX Hr]";[apply lookup_insert|]. 
      iDestruct "HX" as (ρ Hρ) "[Hstate HX]".
      iDestruct "HX" as (γpred' p' φ' Heq Hpers') "[#Hsaved' HX]". 
      inversion Heq;subst.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hx. 
      destruct ρ.
      { iDestruct "HX" as (v' Hne') "[Hx' _]".
        iDestruct (cap_duplicate_false with "[$Hx $Hx']") as "Hf"; auto. }
      { iDestruct "HX" as (v' Hne') "[Hx' _]".
        iDestruct (cap_duplicate_false with "[$Hx $Hx']") as "Hf"; auto. }
      2: { iDestruct "HX" as (v' Hx' Hne') "[Hx' _]".
           iDestruct (cap_duplicate_false with "[$Hx $Hx']") as "Hf"; auto. }
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[rewrite Hρ; auto|]. 
      iDestruct (region_map_insert_singleton (Static {[a:=w]}) with "Hr") as "Hr";[eauto|].
      apply (related_sts_priv_world_revoked_to_uninit (m >> revoke W) a w)
        in Hx as Hrelated. 
      iDestruct (monotone_revoke_list_region_def_mono $! Hrelated with "[Hfull] Hr") as "[Hfull Hr]".
      { rewrite override_uninitializedW_commute;auto. }
      iMod (sts_update_std _ _ _ (Static {[a:=w]}) with "Hfull Hstate") as "[Hfull Hstate] /=".
      iDestruct (big_sepM_delete with "[Hstate Hx $Hr]") as "Hr";[apply lookup_insert|..]. 
      { iExists (Static {[a:=w]}). iFrame. iSplit;[iPureIntro;apply lookup_insert|].
        iExists _,_,_. iFrame "# ∗". repeat iSplit;eauto. iExists _. iFrame.
        repeat iSplit;auto;iPureIntro;[apply lookup_singleton|].
        intros a' Ha'. apply elem_of_gmap_dom in Ha' as [x Ha'].
        destruct (decide (a = a'));[subst;simplify_map_eq;auto|simplify_map_eq]. 
      }
      rewrite -HMeq. iModIntro. iSplitL "Hfull".
      { rewrite override_uninitializedW_commute;auto. }
      iExists M,(<[a:=Static {[a:=w]}]>Mρ). iFrame. iPureIntro. split.
      + rewrite -Hdom. rewrite dom_insert_L.
        assert (a ∈ dom (gset Addr) (m >> (revoke W)).1) as Hin.
        { rewrite Hdom HMeq dom_insert_L. set_solver. }
        set_solver.
      + rewrite dom_insert_L -Hdom'. assert (a ∈ dom (gset Addr) Mρ) as Hin;[apply elem_of_gmap_dom;eauto|]. 
        set_solver. 
  Qed.

   
   (* the following lemma takes some uninitilized states and revokes them. For simplicity we ignore their values *)
   (* this lemma is used to revoke the range needed for the local stack frame *)
   Lemma region_uninitialized_to_revoked W (l: list Addr) p φ:
     NoDup l ->
     ([∗ list] a ∈ l, ⌜exists w, std W !! a = Some (Static {[a:=w]})⌝ ∗ rel a p φ)
   ∗ sts_full_world (revoke W)
   ∗ region (revoke W) ==∗
     sts_full_world (std_update_multiple (revoke W) l Revoked)
   ∗ region (std_update_multiple (revoke W) l Revoked)
   ∗ ([∗ list] a ∈ l, ∃ v, a ↦ₐ[p] v). 
   Proof.
    iIntros (Hdup) "(Ha & Hsts & Hr)".
    iInduction (l) as [|x l] "IH". 
    - simpl. iFrame. done. 
    - iDestruct (big_sepL_cons with "Ha") as "[Hx Ha]".
      iDestruct "Hx" as "[% Hrelx]". destruct H as [w Hw].
      apply NoDup_cons in Hdup as [Hnin Hdup].
      iMod ("IH" with "[] Ha Hsts Hr") as "[Hfull [Hr Hx] ] /=";[auto|auto|..].
      
      rewrite region_eq /region_def.
      iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
      iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
      assert (is_Some (M !! x)) as [ρ Hρ].
      { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. apply std_sta_update_multiple_is_Some. eauto.
        rewrite /revoke /revoke_std_sta lookup_fmap Hw /=. eauto. }
      iDestruct (big_sepM_delete with "Hr") as "[Hw Hr]";[eauto|]. 
      iDestruct "Hw" as (ρ' Hρ') "[Hstate HX]".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hx.
      rewrite std_sta_update_multiple_lookup_same_i in Hx;auto.
      rewrite /revoke /revoke_std_sta lookup_fmap Hw /= in Hx. inversion Hx; subst.
      iDestruct "HX" as (γpred' p' φ' Heq Hpers') "[#Hsaved' HX]". 
      iDestruct "HX" as (v Hlookup Hne) "[HX _]".

      iDestruct (monotone_revoke_list_region_def_mono with "[] [Hfull] Hr") as "[Hfull Hr]".
      { iPureIntro. apply related_sts_priv_world_uninit_to_revoked with w.
        rewrite std_sta_update_multiple_lookup_same_i //.
        rewrite /revoke /revoke_std_sta lookup_fmap Hw /=. reflexivity. }
      { rewrite std_update_multiple_revoke_commute. iFrame. auto. }
      
      iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate] /=".
      iDestruct (region_map_delete_singleton with "Hr") as "Hr";[rewrite Hρ';eauto|]. 
      iDestruct (region_map_insert_nonstatic Revoked with "Hr") as "Hr";[auto|].
      
      iDestruct (big_sepM_delete with "[$Hr Hstate]") as "Hr";[eauto|..]. 
      { iExists Revoked. iSplit;[rewrite lookup_insert;auto|]. iFrame. iExists _,_,_. repeat iSplit;eauto. }
      iFrame.
      iSplitL "Hfull".
      { rewrite std_update_multiple_revoke_commute //. }

      rewrite RELS_eq/ RELS_def rel_eq /rel_def REL_eq /REL_def.
      iDestruct "Hrelx" as (γpred) "[Hrelx Hpredx]".
      iDestruct (reg_in with "[$HM $Hrelx]") as %HMeq.
      rewrite HMeq in Hρ. rewrite lookup_insert in Hρ. inv Hρ.
      inv H0.

      iModIntro. iSplitL "HM Hr". 
      + iExists M,(<[x:=Revoked]> Mρ). iFrame. repeat iSplit.
        ++ iPureIntro. rewrite dom_insert_L. rewrite Hdom.
           assert (x ∈ dom (gset Addr) M) as Hin. apply elem_of_gmap_dom;eauto.
           rewrite HMeq lookup_insert; eauto.
           set_solver.
        ++ iPureIntro. rewrite dom_insert_L. rewrite Hdom'.
           assert (x ∈ dom (gset Addr) M) as Hin. apply elem_of_gmap_dom;eauto.
           rewrite HMeq lookup_insert; eauto.
           set_solver.
      + simplify_map_eq. iExists v. iFrame. 
  Qed.

   Lemma std_update_id W a ρ :
     std W !! a = Some ρ -> <s[a:=ρ]s>W = W.
   Proof.
     intros Hstate. destruct W; simpl in *.
     rewrite /std_update /=. f_equiv. rewrite insert_id;auto.
   Qed. 

   (* The following lemma reinstates temporary regions, after they have been uninitialized. The list of previously 
      uninitialized resources may have turned temporary in the public future world we consider *)
   Lemma region_uninitialized_to_temporary_mid_open W W' (m : gmap Addr Word) l :
     related_sts_pub_world W W' ->
     (∀ a w, m !! a = Some w -> std W !! a = Some Temporary ∨ std W !! a = Some (Static {[a:=w]})) ->
     (elements (dom (gset Addr) m)) ## l ->
     (□ ([∗ map] a↦w ∈ m, ∃ φ p, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                 ∗ ⌜p ≠ O⌝
                                 ∗ ▷ φ (W',w)
                                 ∗ rel a p φ
                                 ∗ (if pwl p then future_pub_mono φ w
                                    else future_priv_mono φ w))
        -∗ open_region_many l W'
        -∗ sts_full_world W
        ==∗
        open_region_many l W'
        ∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Temporary))%I.
   Proof.
     iIntros (Hrelated Hforall Hdisj) "#Hvalid Hr Hsts". 
     iInduction (m) as [|a w m] "IH" using map_ind. 
     - rewrite dom_empty_L elements_empty /=. iFrame. done.
     - rewrite dom_insert_L.
       assert (a ∉ dom (gset Addr) m) as Hnin;[apply not_elem_of_dom;auto|].
       assert (a ∉ l) as Hninl.
       { intros Hcontr. apply elem_of_disjoint in Hdisj. apply Hdisj in Hcontr;auto.
         rewrite dom_insert_L. rewrite elements_union_singleton;auto. constructor. }
       apply elements_union_singleton in Hnin.
       apply (std_update_multiple_permutation W _ _ Temporary) in Hnin. rewrite Hnin /=. 
       iDestruct (big_sepM_delete with "Hvalid") as "[Ha Hvalid_rest]";[apply lookup_insert|]. 
       rewrite delete_insert;auto.

       iMod ("IH" with "[] [] Hvalid_rest Hr Hsts") as "[Hr Hsts]".
       { iPureIntro. intros a' w' Ha'. apply Hforall. simplify_map_eq. auto. }
       { iPureIntro. apply elem_of_disjoint. intros x Hm Hx. destruct (decide (a = x));[congruence|].
         apply elem_of_disjoint in Hdisj. apply Hdisj in Hx;auto.
         rewrite dom_insert_L. rewrite elements_union_singleton;[apply elem_of_cons;right;auto|].
         apply not_elem_of_dom. auto. 
       }       
       assert (<[a:=w]> m !! a = Some w) as Ha;[apply lookup_insert|]. 
       apply Hforall in Ha as [Htemp | Huninit].
       + rewrite std_update_id. iFrame. done.
         rewrite std_sta_update_multiple_lookup_same_i;auto.
         intros Hcontr%elem_of_elements%elem_of_gmap_dom. destruct Hcontr. congruence.
       + rewrite open_region_many_eq /open_region_many_def.
         iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
         iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
         assert (is_Some (M !! a)) as [ρ Hρ].
         { apply elem_of_gmap_dom. rewrite -Hdom. destruct Hrelated as [ [Hsub _] _]. apply Hsub.
           apply elem_of_gmap_dom. eauto. }
         iDestruct (big_sepM_delete with "Hr") as "[Hw Hr]";[rewrite lookup_delete_list_notin;eauto|]. 
         iDestruct "Hw" as (ρ' Hρ') "[Hstate HX]".
         iDestruct (sts_full_state_std with "Hsts Hstate") as %Hx.

         assert (a ∉ elements (dom (gset Addr) m)) as Hnina.
         { intros Hcontr%elem_of_elements%elem_of_gmap_dom. destruct Hcontr. congruence. }
         
         rewrite std_sta_update_multiple_lookup_same_i in Hx;auto. 
         rewrite Huninit in Hx;inversion Hx;subst. 
         iDestruct "HX" as (γpred' p' φ' Heq Hpers') "[#Hsaved' HX]". 
         iDestruct "HX" as (v Hlookup Hne) "[HX _]".

         iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hfull Hstate] /=".
         iDestruct (region_map_delete_singleton with "Hr") as "Hr";[rewrite Hρ';eauto|]. 
         iDestruct (region_map_insert_nonstatic Temporary with "Hr") as "Hr";[auto|].

         iDestruct "Ha" as (φ p Hpers Hne') "(Hφ & Hrel & Hmono)".
         rewrite rel_eq /rel_def. iDestruct "Hrel" as (γpred'') "[HREL Hsaved]". 
         rewrite REL_eq RELS_eq /REL_def /RELS_def.
         iDestruct (reg_in with "[$HM $HREL]") as %Hmeq.
         
         iDestruct (big_sepM_delete with "[$Hr HX Hstate]") as "Hr";[rewrite lookup_delete_list_notin;eauto|..]. 
         { iExists Temporary. iSplit;[rewrite lookup_insert;auto|]. iFrame.
           rewrite Hmeq lookup_insert in Hρ. inversion Hρ. 
           iExists _,_,_. repeat iSplit;eauto.
           iExists _. iFrame "∗ #". simplify_eq. repeat iSplit;eauto. simplify_map_eq. iFrame. 
         }
         iFrame.
         iModIntro.
         iExists M,(<[a:=Temporary]> Mρ). iFrame. repeat iSplit.
         ++ iPureIntro. auto. 
         ++ iPureIntro. rewrite dom_insert_L. rewrite Hdom'.
            assert (a ∈ dom (gset Addr) M) as Hin. apply elem_of_gmap_dom;eauto. 
            set_solver.
         ++ rewrite delete_list_insert;auto. 
   Qed.

   Lemma region_uninitialized_to_temporary_mid W W' (m : gmap Addr Word) :
     related_sts_pub_world W W' ->
     (∀ a w, m !! a = Some w -> std W !! a = Some Temporary ∨ std W !! a = Some (Static {[a:=w]})) ->
     (□ ([∗ map] a↦w ∈ m, ∃ φ p, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                 ∗ ⌜p ≠ O⌝
                                 ∗ ▷ φ (W',w)
                                 ∗ rel a p φ
                                 ∗ (if pwl p then future_pub_mono φ w
                                    else future_priv_mono φ w))
        -∗ region W'
        -∗ sts_full_world W
        ==∗
        region W'
        ∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Temporary))%I.
   Proof.
     iIntros (Hrelated HW) "Htemps Hr Hsts".
     iDestruct (region_open_nil with "Hr") as "Hr". 
     iMod (region_uninitialized_to_temporary_mid_open with "Htemps Hr Hsts") as "[Hr Hsts]";auto.
     { apply elem_of_disjoint. intros x Hx Hcontr. inversion Hcontr. }
     iDestruct (region_open_nil with "Hr") as "Hr". 
     iFrame. done.
   Qed. 
     
   Lemma dom_eq_uninit_to_temporary_region W (m : gmap Addr Word) :
     (∀ a, a ∈ dom (gset Addr) m -> std W !! a = Some Temporary ∨ ∃ w, std W !! a = Some (Static {[a:=w]})) ->
     dom (gset Addr) W.1 = dom (gset Addr) (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).1.
   Proof.
     intros Hforall. 
     apply std_update_multiple_dom_equal. intros i Hin%elem_of_elements.
     apply elem_of_gmap_dom. apply Hforall in Hin as [Hx | [w Hx] ];eauto.
   Qed.      
     
   Lemma related_sts_pub_world_uninit_to_temporary_region W (m : gmap Addr Word) :
     (∀ a, a ∈ dom (gset Addr) m -> std W !! a = Some Temporary ∨ ∃ w, std W !! a = Some (Static {[a:=w]})) ->
     related_sts_pub_world W (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).
   Proof.
     intros Hforall.
     split;[|rewrite std_update_multiple_loc;apply related_sts_pub_refl]. 
     split.
     - rewrite (dom_eq_uninit_to_temporary_region _ m);auto.
     - intros i x y Hx Hy.
       destruct (decide (i ∈ dom (gset Addr) m)).
       + apply Hforall in e as HW.
         rewrite std_sta_update_multiple_lookup_in_i in Hy.
         2: { apply elem_of_elements. auto. }
         inversion Hy;subst.
         destruct HW as [Htemp | [w Huninit] ].
         rewrite Hx in Htemp. simplify_eq. left.
         rewrite Hx in Huninit. simplify_eq. eright;[|left]. constructor.
       + rewrite std_sta_update_multiple_lookup_same_i in Hy.
         2: { intros Hcontr%elem_of_elements. congruence. }
         rewrite Hy in Hx. simplify_eq. left.
   Qed.    
   
   Lemma region_uninitialized_to_temporary W (m : gmap Addr Word) :
     (∀ a w, m !! a = Some w -> std W !! a = Some Temporary ∨ std W !! a = Some (Static {[a:=w]})) ->
     (□ ([∗ map] a↦w ∈ m, ∃ φ p, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                 ∗ ⌜p ≠ O⌝
                                 ∗ ▷ φ ((std_update_multiple W (elements (dom (gset Addr) m)) Temporary),w)
                                 ∗ rel a p φ
                                 ∗ (if pwl p then future_pub_mono φ w
                                    else future_priv_mono φ w))
        -∗ region W
        -∗ sts_full_world W
        ==∗
        region (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
        ∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Temporary))%I.
   Proof.
     iIntros (Hforall) "#Hvalid Hr Hsts".
     iDestruct (region_monotone with "[] [] Hr") as "Hr".
     { iPureIntro. apply dom_eq_uninit_to_temporary_region with (m:=m).
       intros a Hin%elem_of_gmap_dom. destruct Hin as [w Hin]. apply Hforall in Hin as [Htemp | Huninit];eauto. }
     { iPureIntro. apply related_sts_pub_world_uninit_to_temporary_region.
       intros a Hin%elem_of_gmap_dom. destruct Hin as [w Hin]. apply Hforall in Hin as [Htemp | Huninit];eauto. }
     iMod (region_uninitialized_to_temporary_mid with "Hvalid Hr Hsts") as "[Hr Hsts]";[|auto|].
     { apply related_sts_pub_world_uninit_to_temporary_region.
       intros a Hin%elem_of_gmap_dom. destruct Hin as [w Hin]. apply Hforall in Hin as [Htemp | Huninit];eauto. }
     iModIntro. iFrame. 
   Qed.

   Lemma std_update_elements_app_union {A : Type} W (m1 m2 : gmap Addr A) ρ :
     std_update_multiple W (elements (dom (gset Addr) (m1 ∪ m2))) ρ =
     std_update_multiple W (elements (dom (gset Addr) m1) ++ elements (dom (gset Addr) m2)) ρ.
   Proof.
     rewrite (surjective_pairing (std_update_multiple W (elements (dom _ _) ) _)).
     erewrite surjective_pairing. 
     repeat rewrite std_update_multiple_loc. f_equiv.
     apply map_eq'. 
     intros a v. 
     split.
     + intros Ha.
       destruct (decide (a ∈ elements (dom (gset Addr) m2))).
       * rewrite std_sta_update_multiple_lookup_in_i in Ha. inversion Ha.
         apply std_sta_update_multiple_lookup_in_i.
         apply elem_of_app;right;auto. revert e;rewrite elem_of_elements =>e. 
         apply elem_of_elements. rewrite dom_union_L. set_solver. 
       * destruct (decide (a ∈ elements (dom (gset Addr) m1))).
         ** rewrite std_sta_update_multiple_lookup_in_i in Ha. inversion Ha.
            apply std_sta_update_multiple_lookup_in_i.
            apply elem_of_app;left;auto. apply elem_of_elements in e.
            repeat rewrite dom_union_L. apply elem_of_elements. set_solver.
         ** rewrite std_sta_update_multiple_lookup_same_i in Ha.
            rewrite std_sta_update_multiple_lookup_same_i;auto.
            apply not_elem_of_app. split;auto. intros Hcontr%elem_of_elements.
            rewrite dom_union_L in Hcontr.
            apply elem_of_union in Hcontr as [Hcontr | Hcontr].
            { apply elem_of_elements in Hcontr. done. }
            { apply elem_of_elements in Hcontr. done. }
     + intros Ha.
       destruct (decide (a ∈ (elements (dom (gset Addr) m1) ++ elements (dom (gset Addr) m2)))).
       * rewrite std_sta_update_multiple_lookup_in_i in Ha;auto. inversion Ha.
         apply std_sta_update_multiple_lookup_in_i.
         apply elem_of_elements. rewrite dom_union_L.
         apply elem_of_app in e as [e | e]; apply elem_of_elements in e;set_solver.
       * rewrite std_sta_update_multiple_lookup_same_i in Ha;auto.
         rewrite std_sta_update_multiple_lookup_same_i;auto.
         rewrite elem_of_elements. apply not_elem_of_app in n.
         revert n. repeat rewrite elem_of_elements. intros [n1 n2].
         rewrite dom_union_L. set_solver.
   Qed.




   (* ------------------------------------------ REINSTATE --------------------------------------------------------- *)
   (* The following lemma reinstates all relevant static and uninitialized invariants to Temporary. It is in the 
      format typically applied in proofs: the local stack frame and leftovers are open, the uninitialized part of the 
      adversary stack is still in region. We need to update both before we close *)

   (* open_region_many is monotone wrt public future worlds *)
   Lemma open_region_many_monotone l W W':
     dom (gset Addr) W.1 = dom (gset Addr) W'.1 →
     related_sts_pub_world W W' →
     (open_region_many l W -∗ open_region_many l W')%I.
   Proof.
     iIntros (Hdomeq Hrelated) "HW". rewrite open_region_many_eq /open_region_many_def.
     iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)". iExists M, Mρ. iFrame.
     iSplitR;[iPureIntro;rewrite -Hdomeq;auto|]. 
     iSplitR; auto.
     iApply region_map_monotone; eauto.
   Qed.
   
   (* The following lemma assumes that m_static contains more than one address *)
   Lemma region_close_static_and_uninitialized_to_temporary (m_static: gmap Addr Word)
         (m_uninit: gmap Addr Word) W W' :
     (W' = (std_update_temp_multiple W (elements (dom (gset Addr) m_static) ++
                                                 elements (dom (gset Addr) m_uninit)))) →
     size m_static > 1 ->
     (∀ a w, m_uninit !! a = Some w -> std W !! a = Some Temporary ∨ std W !! a = Some (Static {[a:=w]})) ->
    open_region_many (elements (dom (gset Addr) m_static)) W
    ∗ sts_full_world W
    (* The static resources *)                 
    ∗ ([∗ map] a↦v ∈ m_static, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
        temp_resources W' φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m_static (Static m_static)
    (* Knowledge about the uninitialized resources *)
    ∗ (□ ([∗ map] a↦w ∈ m_uninit, ∃ φ p, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                 ∗ ⌜p ≠ O⌝
                                 ∗ ▷ φ (W',w)
                                 ∗ rel a p φ
                                 ∗ (if pwl p then future_pub_mono φ w
                                    else future_priv_mono φ w)))
    ==∗
    sts_full_world W'
    ∗ region W'.
  Proof.
    iIntros (Heq Hsize Hunint) "(HR & Hsts & Hres & Hst & #Hvalid)".

    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    assert (related_sts_pub_world W W') as Hrelated.
    { rewrite Heq. rewrite /std_update_temp_multiple. rewrite std_update_multiple_app.
      eapply related_sts_pub_trans_world;[apply related_sts_pub_world_static_to_temporary with m_static;eauto|].
      apply related_sts_pub_world_uninit_to_temporary_region. intros a Hin.
      destruct (decide (a ∈ elements (dom (gset Addr) m_static))).
      - left. apply std_sta_update_multiple_lookup_in_i. auto.
      - rewrite std_sta_update_multiple_lookup_same_i;auto.
        apply elem_of_gmap_dom in Hin as [w Hin]. apply Hunint in Hin as [Htemp | Huninit];eauto. 
    }

    assert (elements (dom (gset Addr) m_uninit) ## elements (dom (gset Addr) m_static)) as Hdisj.
    { rewrite elem_of_disjoint. intros x Hxuninit Hxstatic.
      apply elem_of_elements,elem_of_gmap_dom in Hxuninit as [w Hw].
      apply Hunint in Hw as [Htemp | Huninit].
      - revert H;rewrite Forall_forall =>H. apply H in Hxstatic. congruence.
      - revert H;rewrite Forall_forall =>H. apply H in Hxstatic.
        destruct (decide (m_static = {[x:=w]}));[subst;rewrite map_size_singleton in Hsize;lia|congruence].
    }
    
    iDestruct (open_region_many_monotone _ _ W' with "HR") as "HR";auto.
    { rewrite Heq. apply std_update_multiple_dom_equal. intros a Hin%elem_of_app.
      revert H;rewrite Forall_forall =>H. 
      destruct Hin as [Hin | Hin].
      - apply elem_of_gmap_dom. eauto.
      - apply elem_of_elements,elem_of_gmap_dom in Hin as [w Hw].
        apply Hunint in Hw as [Htemp | Huninit]; apply elem_of_gmap_dom;eauto. 
    }
    
    iMod (region_uninitialized_to_temporary_mid_open with "Hvalid HR Hsts") as "[Hr Hsts]";[auto..|].
    iDestruct (region_update_multiple_states _ _ _ Temporary with "[$Hsts $Hst]") as ">[Hsts Hst]".
    iModIntro.
    (* iDestruct (open_region_world_static_to_temporary with "Hr") as "Hr"; eauto. *)
    repeat rewrite -std_update_multiple_app std_update_multiple_app_commute. rewrite Heq.  
    iDestruct (region_close_temporary_many with "[Hr Hres Hst Hsts]") as "(?&?)"; iFrame.
  Qed.
       
End heap. 
