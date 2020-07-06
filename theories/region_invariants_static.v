From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra iris_extra region_invariants
     multiple_updates region_invariants_revocation sts.
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

  (* This file provides three main lemmas:
     - one that opens all of a static region at once
     - one that closes what was a static region and turns it into a temporary one
     - one that turns a revoked region into a static region
   *)

  (* --------------------------------------------------------------------------------- *)
  (* Auxiliary definitions around opened regions *)

  (* A collection of sts_state_std *)
  Definition sts_state_std_many {V} (m: gmap Addr V) (ρ: region_type) :=
    ([∗ map] a↦_ ∈ m, sts_state_std a ρ)%I.

  (* Bulk update of the state of a [sts_state_std_many] *)
  Lemma region_update_multiple_states W (m : gmap Addr Word) st st' :
    sts_full_world W ∗ sts_state_std_many m st
    ==∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) st')
    ∗ sts_state_std_many m st'.
  Proof.
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind.
    - rewrite /sts_state_std_many dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iDestruct (sts_full_state_std with "Hfull Hx") as %Hstate. 
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH".
      iMod (sts_update_std _ _ _ st' with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      erewrite (std_update_multiple_permutation _ (elements (_ ∪ _))).
      2: { rewrite elements_union_singleton // not_elem_of_dom //. }      
      iAssert (⌜is_Some ((std_update_multiple W (elements (dom (gset Addr) m)) st').1 !! x)⌝%I)
        as %Hsome.
      { rewrite /sts_full_world /sts_full_std /=. 
        iPureIntro. apply std_sta_update_multiple_is_Some.
        eauto. }
      iFrame.
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- Opening a static region ------------------------------- *)

  Lemma region_map_delete_static (M: gmap Addr _) (Mρ: gmap Addr _) W m l γ p v:
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ →
    M !! l = Some (γ,p) →
    Mρ !! l = Some (Static m) →
    m !! l = Some v →
    region_map_def M Mρ W -∗
    region_map_def (delete l M) Mρ W ∗
    l ↦ₐ[p] v ∗ sts_state_std l (Static m).
  Proof.
    intros Hdom HMl HMρ Hm.
    iIntros "Hr". 
    iDestruct (big_sepM_delete _ _ l with "Hr") as "(Hl & Hr)"; eauto; [].
    iFrame. iDestruct "Hl" as (ρ' Hρ') "(? & Hst)".
    assert (ρ' = Static m) as -> by congruence.
    iDestruct "Hst" as (? ? ?) "(% & ? & ? & H)".
    iDestruct "H" as (v') "(% & ? & ? & _)". 
    assert (v' = v) as -> by (congruence). simplify_eq. iFrame.
  Qed.

  Definition static_resources (m: gmap Addr Word) :=
    ([∗ map] a↦v ∈ m, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] v)%I.

  Lemma region_map_open_some_static (M: gmap Addr _) Mρ W (m m_all: gmap Addr Word) :
    m ⊆ m_all →
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m_all)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ RELS M 
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, rel a p φ)
    -∗
    region_map_def (M ∖∖ m) Mρ W
    ∗ RELS M
    ∗ sts_full_world W
    ∗ static_resources m
    ∗ sts_state_std_many m (Static m_all).
  Proof.
    pattern m. revert m. refine (map_ind _ _ _).
    - intros **. iIntros "(?&?&?&?)".
      rewrite !difference_het_empty /static_resources /sts_state_std_many !big_sepM_empty /=.
      iFrame; eauto.
    - intros a v m Hma HI Hsub_all Hm_all Hdom.
      iIntros "(Hr & HM & Hsts & Hrels)".
      assert (a ∈ dom (gset Addr) Mρ).
      { specialize (Hm_all a).
        feed pose proof Hm_all. rewrite dom_insert; set_solver.
        rewrite -elem_of_gmap_dom. eauto. }
      assert (a ∈ dom (gset Addr) M) by (rewrite -Hdom; auto).
      rewrite difference_het_insert_r //.
      feed specialize HI; eauto.
      { transitivity (<[a:=v]> m); auto. by apply insert_subseteq. }
      { intros a' Ha'. apply Hm_all. rewrite dom_insert. set_solver. }
      iDestruct (big_sepM_insert with "Hrels") as "[Ha Hrels]";auto. 
      iDestruct (HI with "[Hr HM Hsts Hrels]") as "(Hr & HM & Hfull & ? & Hmap)"; [by iFrame|..].
      rewrite rel_eq /rel_def. iDestruct "Ha" as (? ? ?) "[HREL ?]".
      rewrite REL_eq RELS_eq /REL_def /RELS_def.
      iDestruct (reg_in with "[$HREL $HM]") as %HMeq. 
      apply elem_of_gmap_dom in H0. destruct H0. destruct x. 
      iDestruct (region_map_delete_static _ _ _ m_all a with "Hr") as "(? & ? & ?)".
      { rewrite dom_difference_het. rewrite Hdom. set_solver. }
      { apply difference_het_lookup_Some. split;eauto. }
      { apply Hm_all. rewrite dom_insert; set_solver. }
      { eapply lookup_weaken; [| apply Hsub_all]. by rewrite lookup_insert. }
      rewrite HMeq in H0. simplify_map_eq. 
      iFrame. rewrite /static_resources /sts_state_std_many !big_sepM_insert //.
      iFrame. iExists _,_. iFrame. rewrite rel_eq /rel_def REL_eq /REL_def. iExists _. iFrame. 
  Qed.

  Lemma region_map_open_all_static M Mρ W (m: gmap Addr Word) :
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world W
    ∗ RELS M
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, rel a p φ)
    -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ sts_full_world W
    ∗ sts_state_std_many m (Static m)
    ∗ static_resources m
    ∗ RELS M.
  Proof.
    iIntros (HH Hdom) "(Hr & Hsts & HM & Hrels)".
    iDestruct (region_map_open_some_static M Mρ W m m with "[Hr Hsts HM Hrels]")
      as "(Hr & HM & Hsts & ? & ?)"; auto; iFrame.
    iApply (big_sepM_mono with "Hr").
    iIntros (k γp HMk) "H". iDestruct "H" as (ρ HMρ) "(Hst & Hρ)". iExists ρ.
    rewrite difference_het_lookup_Some in HMk * => HMk. destruct HMk as [HMk Hmk].
    iSplitR. iPureIntro. by rewrite difference_het_lookup_Some; eauto.
    iFrame. destruct ρ as [| | | m']; (try by iFrame); [].
    iDestruct "Hρ" as (γpred p φ Heq Hpers) "[Hsaved Hρ]". 
    iDestruct "Hρ" as (v Hm') "(? & ? & Hothers)". iDestruct "Hothers" as %Hothers.
    iExists _,_,_. iFrame. repeat iSplitR;auto. iExists _. iFrame. iPureIntro. split; eauto.
    intros a' Ha'. rewrite difference_het_lookup_Some. split; eauto.
    destruct (m !! a') eqn:?; eauto. exfalso.
    specialize (HH a'). feed specialize HH. by rewrite -elem_of_gmap_dom; eauto.
    specialize (Hothers a'). feed specialize Hothers; auto.
    assert (m' = m) by congruence. congruence.
  Qed.

  Lemma region_map_has_static_addr M Mρ W (l: Addr) m :
    (std W) !! l = Some (Static m) →
    dom (gset Addr) (std W) = dom (gset Addr) M →
    region_map_def M Mρ W ∗ sts_full_world W -∗
    ⌜(forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m))⌝ ∗
    ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl Hdom) "(Hr & Hsts)". 
    assert (is_Some (M !! l)) as [ρ Hρ].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_lookup _ _ l with "Hr") as "Hl"; eauto.
    iDestruct "Hl" as (ρ' Hρ') "(Hst & Hρ)".
    iDestruct (sts_full_state_std with "Hsts Hst") as %HH.
    rewrite HWl in HH. apply Some_eq_inj in HH. subst ρ'.
    iDestruct "Hρ" as (? ? ?) "(? & ? & ? & Hρ)". 
    iDestruct "Hρ" as (? ? ?) "(? & %)".
    intros. iPureIntro. split; eauto.
    rewrite -elem_of_gmap_dom; eauto.
  Qed.

  Lemma region_rel_get_all (W : WORLD) (a : Addr) :
    is_Some ((std W) !! a) ->
    (region W ∗ sts_full_world W ==∗
     region W ∗ sts_full_world W ∗ ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ rel a p φ)%I.
  Proof.
    iIntros ([x Hlookup]) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    rewrite RELS_eq /RELS_def. 
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    (* rewrite /region_map_def. iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. *)
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]". 
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''.
    rewrite Hlookup in Hx''. inversion Hx''. subst. 
    iDestruct "Hstate" as (γpred p φ Heq Hpers) "(#Hsaved & Ha)". 
    (* iDestruct "Ha" as (v Hne) "(Ha & Hmono & #Hφ)". *)
    destruct γp as [γpred' p']; inversion Heq; subst. 
    iDestruct (big_sepM_delete _ _ a with "[Hρ Ha $Hr]") as "Hr";[eauto| |].
    { iExists ρ. iSplit;auto. iFrame. iExists γpred, p, φ. iFrame "∗ #". repeat iSplit; auto. }
    iModIntro. 
    iSplitL "HM Hr".
    { iExists M. iFrame. auto. }
    iFrame. iExists p,φ. iSplit;auto. rewrite rel_eq /rel_def REL_eq /REL_def. iExists γpred. 
    iFrame "Hsaved Hrel".
  Qed. 

  Lemma region_map_has_static_rels W m' m a :
    m' ⊆ m →
    (std W) !! a = Some (Static m) ->
    (region W ∗ sts_full_world W ==∗
     region W ∗ sts_full_world W ∗ ([∗ map] a↦v ∈ m', ∃ p φ, rel a p φ))%I.
  Proof.
    iIntros (Hsub Hsta) "[Hr Hsts]".
    iInduction (m') as [|l x] "IH" using map_ind. 
    - iFrame. iModIntro. iApply big_sepM_empty. done.
    - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;eauto.
      assert (is_Some (std W !! l)) as Hsta'.
      { assert (l ∈ dom (gset Addr) m) as Hin.
        { revert Hsub. rewrite map_subseteq_spec =>Hsub. apply elem_of_gmap_dom.
          exists x. apply Hsub. apply lookup_insert. }
        apply Hforall in Hin. rewrite /static in Hin. rewrite /std.
        destruct (W.1 !! l);inversion Hin;eauto. 
      }
      iMod (region_rel_get_all with "[$Hr $Hsts]") as "(Hr & Hsts & Hrel)";eauto. 
      iMod ("IH" with "[] Hr Hsts") as "(Hr & Hsts & Hrels)".
      { iPureIntro. trans (<[l:=x]> m0);auto. apply insert_subseteq. auto. }
      iFrame. iModIntro. iApply big_sepM_insert;auto. iFrame.
      iDestruct "Hrel" as (p φ Hpers) "Hrel".
      iExists p,φ. iFrame.
  Qed.

  Lemma region_map_has_static_rels_all W m a :
    (std W) !! a = Some (Static m) ->
    (region W ∗ sts_full_world W ==∗
     region W ∗ sts_full_world W ∗ ([∗ map] a↦v ∈ m, ∃ p φ, rel a p φ))%I.
  Proof.
    iIntros (Hsta) "[Hr Hsts]". 
    iApply region_map_has_static_rels;eauto. iFrame.
  Qed. 

  Lemma region_open_static W (m: gmap Addr Word) (l: Addr) :
    (std W) !! l = Some (Static m) →
    region W ∗ sts_full_world W ==∗
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ sts_state_std_many m (Static m)
    ∗ static_resources m
    ∗ ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl) "(Hr & Hsts)".
    iMod (region_map_has_static_rels_all with "[$Hr $Hsts]") as "(Hr & Hsts & Hrels)";eauto. 
    iModIntro. rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
    iDestruct (region_map_has_static_addr with "[HM Hr Hsts]")
      as %(Hstatic & ?); eauto; [by iFrame|].
    iDestruct (region_map_open_all_static M Mρ W m with "[HM Hr Hsts Hrels]")
      as "(Hr & Hsts & ? & ? & ?)"; eauto; [iFrame|].
    iFrame. iSplitL; eauto. rewrite open_region_many_eq /open_region_many_def.
    iExists M,Mρ. iFrame. do 2 (iSplitR; eauto).
    rewrite !delete_elements_eq_difference_het. eauto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ---------------------- Turn a static region into a temporary one ---------------- *)

  Lemma related_sts_pub_world_static_to_temporary (l: list Addr) m W:
    Forall (λ (a:Addr), (std W) !! a = Some (Static m)) l →
    related_sts_pub_world W (std_update_multiple W l Temporary).
  Proof.
    intros Hforall.
    induction l.
    - apply related_sts_pub_refl_world.
    - rewrite Forall_cons in Hforall *; move=>[Ha Hforall].
      eapply related_sts_pub_trans_world;[by apply IHl|].
      cbn. set W' := std_update_multiple W l Temporary.
      rewrite /std_update /related_sts_pub_world /=. split.
      2: { apply related_sts_pub_refl. }
      unfold related_sts_std_pub. rewrite dom_insert_L.
      repeat split_and; [set_solver ..|].
      intros i x y Hx Hy.
      (* apply std_update_multiple_rel_is_std with (l:=l) (ρ:=Temporary) in Hstd. *)
      (* rewrite -/W' in Hstd. *)
      (* feed pose proof (Hstd i) as Hstdi; eauto. rewrite /rel_is_std_i /= in Hstdi. *)
      destruct (decide (i = a)).
      { subst i. simplify_map_eq. 
        destruct (decide (a ∈ l)).
        { rewrite std_sta_update_multiple_lookup_in_i // in Hx. simplify_eq. reflexivity. }
        rewrite std_sta_update_multiple_lookup_same_i /std // in Hx. simplify_eq.
        eapply rtc_once. rewrite Ha in Hx;inversion Hx. constructor. }
      {  rewrite lookup_insert_ne // in Hy.
        rewrite Hx in Hy; simplify_eq. reflexivity. }
  Qed.

  Lemma open_region_world_static_to_temporary l m W :
    Forall (λ (a:Addr), (std W) !! a = Some (Static m)) l →
    open_region_many l W
    -∗
    open_region_many l (std_update_multiple W l Temporary).
  Proof.
    intros. iApply open_region_many_monotone.
    { apply elem_of_equiv_L. intro.
      rewrite -std_update_multiple_dom_equal; auto.
      intros i Hi. apply elem_of_gmap_dom.
      eexists. eapply Forall_forall in H; eauto. }
    { eapply related_sts_pub_world_static_to_temporary; eauto. }
  Qed.

  Lemma region_close_temporary_many (m: gmap Addr Word) W:
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
        temp_resources W φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m Temporary
    ∗ sts_full_world W
    -∗
    region W ∗ sts_full_world W.
  Proof.
    pattern m. revert m. eapply map_ind.
    - iIntros "(Hor & ? & ? & Hsts)". rewrite dom_empty_L elements_empty.
      iDestruct (region_open_nil with "Hor") as "Hor". iFrame.
    - iIntros (a γp m Hma HInd) "(HR & Htmp & Hst & Hsts)".
      iDestruct (open_region_many_permutation with "HR") as "HR".
      { rewrite dom_insert elements_union_singleton // not_elem_of_dom //. }
      iDestruct (big_sepM_insert with "Hst") as "[Hsta Hst]"; eauto.
      iDestruct (sts_full_state_std with "Hsts Hsta") as %HWa.
      iDestruct (big_sepM_insert with "Htmp") as "[Ha Htmp]"; eauto.
      iDestruct "Ha" as (? ? ?) "(Hatmp&?)".
      iDestruct "Hatmp" as (? ?) "(?&?&?)".
      iApply HInd. iFrame.
      iApply (region_close_next _ _ _ a _ _ Temporary).
      + congruence.
      + intros [? ?]. congruence.
      + intros [? ?]%elem_of_elements%elem_of_gmap_dom. congruence.
      + iFrame. iSplitR; auto. unfold monotonicity_guarantees_region.
        destruct (pwl _); eauto.
  Qed.

  Lemma future_priv_mono_is_future_pub_mono (φ: _ → iProp Σ) v:
    (future_priv_mono φ v -∗ future_pub_mono φ v)%I.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    eauto using related_sts_pub_priv_world.
  Qed.

  Lemma sts_full_state_std_many {V} (m: gmap Addr V) (ρ:region_type) W:
    sts_full_world W
    ∗ sts_state_std_many m ρ
    -∗
    ⌜Forall (λ (a:Addr), std W !! a = Some ρ) (elements (dom (gset Addr) m))⌝.
  Proof.
    pattern m. revert m. apply map_ind.
    - iIntros. iPureIntro. rewrite dom_empty elements_empty //.
    - iIntros (a x m ? IH) "(Hsts & Hst)".
      iDestruct (big_sepM_insert with "Hst") as "[Hsta Hst]"; auto.
      iDestruct (sts_full_state_std with "Hsts Hsta") as %Hsta.
      iDestruct (IH with "[Hsts Hst]") as %?. by iFrame.
      iPureIntro. rewrite dom_insert elements_union_singleton ?not_elem_of_dom //.
      constructor; eauto.
  Qed.

  Lemma region_close_static_to_temporary (m: gmap Addr Word) W :
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         temp_resources W φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m (Static m)
    ==∗
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
    ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).
  Proof.
    iIntros "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_update_multiple_states with "[$Hsts $Hst]") as ">[Hsts Hst]".
    iModIntro.
    iDestruct (open_region_world_static_to_temporary with "HR") as "HR"; eauto.
    iDestruct (region_close_temporary_many with "[HR Hres Hst Hsts]") as "(?&?)".
    { iFrame. iApply (big_sepM_mono with "Hres"). iIntros (a pv ?) "H".
      iDestruct "H" as (p φ ?) "(Htmp & ?)". iExists p, φ. iSplitR;eauto.
      iFrame. unfold temp_resources. iDestruct "Htmp" as (v ?) "(Ha&Hmon&?)".
      iExists v. iSplitR; eauto. iFrame "Ha".
      iAssert (future_pub_mono φ v)%I with "[Hmon]" as "#Hφ".
      { destruct (pwl p); eauto. by iApply future_priv_mono_is_future_pub_mono. }
      iFrame. iApply "Hφ"; eauto. iPureIntro.
      eapply related_sts_pub_world_static_to_temporary; eauto. }
    iFrame.
  Qed.

  (* In this version the user is only required to show that the resources are valid in the updated world *)
  Lemma region_close_static_to_temporary_alt (m: gmap Addr Word) W :
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         temp_resources (std_update_multiple W (elements (dom (gset Addr) m)) Temporary) φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m (Static m)
    ==∗
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
    ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).
  Proof.
    iIntros "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_update_multiple_states with "[$Hsts $Hst]") as ">[Hsts Hst]".
    iModIntro.
    iDestruct (open_region_world_static_to_temporary with "HR") as "HR"; eauto.
    iDestruct (region_close_temporary_many with "[HR Hres Hst Hsts]") as "(?&?)"; iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------ Allocate a Static region from a Revoked one ------------------ *)

  Lemma related_sts_pub_world_static W W' m i :
    (std W !! i) = Some (Static m) ->
    related_sts_pub_world W W' ->
    (std W' !! i) = Some (Static m) ∨ (std W' !! i) = Some Temporary.
  Proof.
    intros Hsta [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy]. 
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    eapply std_rel_pub_rtc_Static in Hsta;[|eauto].
    destruct Hsta as [-> | ->];auto. 
  Qed. 
    
  Lemma related_sts_priv_world_static W l (m' : gmap Addr Word) :
    Forall (λ a : Addr, (std W) !! a = Some Revoked) l →
    related_sts_priv_world W (std_update_multiple W l (Static m')).
  Proof.
    intros Hforall.
    induction l. 
    - apply related_sts_priv_refl_world. 
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto. 
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split. 
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               rewrite Hi in Hx0. inversion Hx0; subst. 
               right with Temporary.
               { left. constructor. }
               right with (Static m');[|left]. right. constructor. 
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  Lemma related_sts_priv_world_static2 W l (m' : gmap Addr Word) :
    Forall (λ a : Addr, ∃ ρ, (std W) !! a = Some ρ /\ ρ <> Permanent) l →
    related_sts_priv_world W (std_update_multiple W l (Static m')).
  Proof.
    intros Hforall.
    induction l. 
    - apply related_sts_priv_refl_world. 
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto. 
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split. 
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               destruct Hi as [ρ [Hi Hi']].
               rewrite Hi in Hx0. inversion Hx0; subst.
               destruct x0; try congruence.
               { eright. right. constructor.
                 left. }
               { eright. left; econstructor.
                 eright. right. constructor.
                 left. }
               { eright. left; econstructor.
                 eright. right. constructor.
                 left. }
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  Lemma std_update_multiple_dom_equal_eq W (M: gmap Addr (gname * Perm)) (m: gmap Addr Word) ρ :
    dom (gset Addr) (std W) = dom (gset Addr) M -> 
    dom (gset Addr) m ⊆ dom (gset Addr) M ->
    dom (gset Addr) (std (std_update_multiple W (elements (dom (gset Addr) m)) ρ)) = dom (gset Addr) M.
  Proof.
    intros Hdom Hsub.
    induction m using map_ind.
    - rewrite dom_empty_L elements_empty /=. rewrite Hdom. auto.
    - rewrite dom_insert_L.
      assert (elements ({[i]} ∪ dom (gset Addr) m) ≡ₚ i :: elements (dom (gset Addr) m)) as Heq.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply std_update_multiple_permutation with (W:=W) (ρ:=ρ) in Heq.
      rewrite Heq /= dom_insert_L /=. rewrite IHm.
      + assert (i ∈ dom (gset Addr) M) as Hin.
        { apply Hsub. rewrite dom_insert_L. set_solver. }
        set_solver.
      + rewrite dom_insert_L in Hsub. set_solver. 
  Qed. 
  
  (* The difficulty with static regions is that if one of the addresses is in its static state, all others must be.
     We can therefore not update them one by one (since invariants will break in the middle of the state change).
     Instead, we need to:
              (1) assert that the states are all curently Revoked + delete them from the region map
              (2) update the full sts for all addresses in the static region
              (3) insert the updated states back into the region map
   *)

  (* (1) assert that the states are all curently Revoked + delete them from the region map *)
  Lemma region_revoked_to_static_preamble W M Mρ (m: gmap Addr Word) :
    region_map_def M Mρ W -∗
    ([∗ map] a↦v ∈ m, ∃ p φ, ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ) -∗
    RELS M -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ RELS M
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗
                              a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std a Revoked).
  Proof.
    iIntros "Hr Hmap HM".
    iInduction (m) as [|x l] "IH" using map_ind. 
    - rewrite difference_het_empty difference_het_empty /= big_sepM_empty big_sepM_empty.
      iFrame. 
    - rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct ("IH" with "Hr Hmap HM") as "(Hr & HM & Hmap)". iClear "IH".
      iDestruct "Hx" as (p φ Hne) "[Hx Hrel]".
      rewrite rel_eq /rel_def REL_eq /REL_def RELS_eq /RELS_def.
      iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
      iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
      assert (M ∖∖ m = <[x:=(γpred, p)]> (delete x (M ∖∖ m))) as HMeq'.
      { rewrite HMeq. rewrite insert_delete insert_delete. rewrite difference_het_insert_l; auto.
        by rewrite insert_insert. }
      rewrite HMeq'.
      iDestruct (big_sepM_insert with "Hr") as "[Hxinv Hr]";[by rewrite lookup_delete|].
      iDestruct "Hxinv" as (ρ Hρ) "[Hstate Hinv]".
      iAssert (⌜ρ = Revoked⌝)%I as %Heqρ.
      { destruct ρ;auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (γpred' p' φ' Heqpred Hpers) "[Hsaved Hinv]"; simplify_eq. 
          iDestruct "Hinv" as (v' Hne') "[Hinv _]". 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (γpred' p' φ' Heqpred Hpers) "[Hsaved Hinv]"; simplify_eq. 
          iDestruct "Hinv" as (v' Hne') "[Hinv _]". 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (γpred' p' φ' Heqpred Hpers) "[Hsaved Hinv]"; simplify_eq. 
          iDestruct "Hinv" as (v Hlookup Hne') "[Hinv _]"; simplify_eq. 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
      }
      subst ρ. iDestruct "Hinv" as (γpred' p' φ' Heq' Hpers) "[#Hsaved _]". 
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros;by rewrite Hρ|]. 
      iFrame. iSplitL "Hr". 
      { rewrite delete_insert;[|by rewrite lookup_delete]. iFrame. }
      iApply big_sepM_insert;auto. iFrame. iExists p,φ'. simplify_eq. repeat iSplit;auto.
  Qed.

  (* (2) is simply lemma [region_update_multiple_states] *)

  (* (3) insert the updated states back into the region map *)
  (* note that the following statement is a generalisation of the lemma which has fully updated the map *)
  (* m' represents the part of the map which has been closed thus far. This lemma can be applied to m' = m, 
     where we would need to establish that indeed all adresses in the domain of (m \\ m) are Static (that is 
     to say that none of the addresses in the beginning are Static) *)
  Lemma region_revoked_to_static_close_mid W M M' Mρ m m' :
    (forall (x : Addr) (γp : gname * Perm), M !! x = Some γp -> M' !! x = Some γp) ->
    dom (gset Addr) m ⊆ dom (gset Addr) m' ->
    (forall a ρ, m !! a = Some ρ -> m' !! a = Some ρ) ->
    (∀ a, is_Some(m !! a) -> is_Some(M !! a)) ->
    (∀ a' : Addr, a' ∈ dom (gset Addr) (m' ∖∖ m) → ((Mρ ∖∖ m) !! a' = Some (Static m'))) ->
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ ->
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ RELS M'
    -∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std a (Static m'))
    -∗ ∃ Mρ', region_map_def M Mρ' W
            ∗ RELS M'
            ∗ ⌜dom (gset Addr) Mρ' = dom (gset Addr) Mρ⌝
            ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m' → Mρ' !! a' = Some (Static m')⌝.
  Proof.
    iIntros (HsubM Hsub Hsame HmM Hmid Hdom) "Hr HM Hmap".
    iRevert (HsubM HmM Hmid Hdom). iInduction (m) as [|x w] "IH" using map_ind forall (M Mρ) . 
    - iIntros (HsubM HmM Hmid Hdom). rewrite difference_het_empty difference_het_empty /=. iExists Mρ. iFrame.
      rewrite !difference_het_empty in Hmid. auto.
    - iIntros (HsubM HmM Hmid Hdom).
      rewrite !difference_het_insert_r !difference_het_delete_assoc.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct "Hx" as (p φ Hpers Hne) "(Hx & #Hrel & Hstate)".
      iAssert (region_map_def (delete x M ∖∖ m) (<[x:=Static m']> Mρ ∖∖ m) W) with "[Hr]" as "Hr".
      { iApply (big_sepM_mono with "Hr").
        iIntros (a y Ha) "Hr".
        iDestruct "Hr" as (ρ Ha') "[Hstate Hρ]".
        assert (a ≠ x) as Hne'.
        { intros Hcontr; subst a. rewrite -difference_het_delete_assoc lookup_delete in Ha. done. }
        iExists ρ. iFrame. iSplitR.
        { rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          rewrite -difference_het_delete_assoc lookup_delete_ne in Ha';auto. }
        destruct ρ; iFrame. iDestruct "Hρ" as (? ? ? Heq' Hpers') "[Hsaved Hρ]".
        iDestruct "Hρ" as (v' ? ?) "[Ha #Hforall]".
        iExists _,_,_. repeat iSplit;auto. iExists v'. repeat iSplit;auto. iDestruct "Hforall" as %Hforall.
        iPureIntro. intros a' Hag. destruct (decide (x = a')).
        - subst. apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete in Hag. done.
        - rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete_ne in Hag;auto.
      }
      iDestruct ("IH" with "[] [] Hr HM Hmap [] [] [] []") as (Mρ') "(Hr & HM & #Hforall)".
      { rewrite dom_insert_L in Hsub. iPureIntro. set_solver. }
      { iPureIntro. intros a ρ Ha. apply Hsame. by simplify_map_eq. }
      { iPureIntro. intros x0 γp Hx0.
        assert (x ≠ x0) as Hne';[intros Hcontr;subst;rewrite lookup_delete in Hx0;done|]. 
        rewrite lookup_delete_ne in Hx0; auto. }
      { iPureIntro. intros a [y Ha]. destruct (decide (a = x)).
        - subst. rewrite Ha in H. done.
        - rewrite lookup_delete_ne;auto. apply HmM. rewrite lookup_insert_ne;auto. rewrite Ha. eauto. 
      }
      { iPureIntro. intros a' Hin.
        destruct (decide (x = a')).
        - subst. rewrite difference_het_insert_l; auto. apply lookup_insert. 
        - rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          repeat rewrite difference_het_insert_r in Hmid.
          specialize (Hmid a'). rewrite lookup_delete_ne in Hmid;auto. apply Hmid.
          rewrite dom_delete. set_solver.
      }
      { iPureIntro. rewrite dom_delete dom_insert_L. set_solver. }
      iDestruct "Hforall" as %[Hdom' Hforall]. 
      assert (is_Some (M !! x)) as [γp HMx].
      { apply HmM. rewrite lookup_insert. eauto. }
      assert (M' !! x = Some γp) as HM'x;auto.
      rewrite rel_eq /rel_def RELS_eq /RELS_def REL_eq /REL_def.
      iDestruct "Hrel" as (γpred') "[HREL Hsaved']".
      iDestruct (reg_in γrel M' with "[$HM $HREL]") as %HMeq.
      rewrite HMeq in HM'x. rewrite lookup_insert in HM'x. inversion HM'x. 
      iDestruct (big_sepM_insert _ _ x γp with "[$Hr Hx Hstate]") as "Hr";[by rewrite lookup_delete|..].
      { iExists (Static m').
        iSplitR.
        - iPureIntro. apply Hforall. rewrite dom_insert_L in Hsub. set_solver. 
        - iFrame. iExists _,_,_. repeat iSplit;auto.
          iExists w. iFrame. repeat iSplit;auto. iPureIntro. apply Hsame. subst. apply lookup_insert. 
      }
      apply insert_id in HMx. rewrite insert_delete HMx. 
      iExists Mρ'. iFrame. repeat iSplit;auto. iPureIntro.
      rewrite Hdom' dom_insert_L.
      assert (x ∈ dom (gset Addr) Mρ) as Hin;[|set_solver].
      apply elem_of_subseteq in Hdom. apply Hdom. apply elem_of_gmap_dom. apply HmM. rewrite lookup_insert; eauto. 
  Qed.

  Lemma RELS_sub M (m : gmap Addr Word) :
    RELS M -∗ ([∗ map] a↦_ ∈ m, ∃ p φ, rel a p φ) -∗
    ⌜∀ (a : Addr), is_Some(m !! a) -> is_Some(M !! a)⌝. 
  Proof.
    iIntros "HM Hmap".
    iIntros (a [x Hx]).
    iDestruct (big_sepM_delete _ _ a with "Hmap") as "[Ha _]";eauto.
    iDestruct "Ha" as (p φ) "Hrel".
    rewrite rel_eq /rel_def REL_eq RELS_eq /REL_def /RELS_def.
    iDestruct "Hrel" as (γpred) "[Hown _]".
    iDestruct (reg_in with "[$HM $Hown]") as %HMeq.
    rewrite HMeq. rewrite lookup_insert. eauto.
  Qed.

  Lemma region_revoked_to_static_close W M Mρ m :
    dom (gset Addr) M = dom (gset Addr) Mρ ->
    RELS M
    -∗ region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std a (Static m))
    -∗ RELS M ∗ ∃ Mρ, region_map_def M Mρ W
                   ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)⌝
                   ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝.
  Proof.
    iIntros (Hdom) "HM Hr Hmap".
    iDestruct (RELS_sub with "HM [Hmap]") as %Hsub.
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Ha".
      iDestruct "Ha" as (p φ Hpers Hne) "(_ & Hrel & _)". eauto.
    }
    iDestruct (region_revoked_to_static_close_mid _ _ _ _ m with "Hr HM [Hmap]") as "HH"; auto.
    { rewrite difference_het_eq_empty dom_empty_L. intros a' Hin. set_solver. }
    { rewrite Hdom. set_solver. }
    iDestruct "HH" as (Mρ') "(? & ? & % & ?)". iFrame. iExists _. iFrame. iPureIntro. congruence. 
  Qed.

  Lemma region_revoked_to_static W (m: gmap Addr Word) :
    (sts_full_world (revoke W)
    ∗ region (revoke W)
    ∗ ([∗ map] a↦v ∈ m, ∃ p φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
    ==∗ (sts_full_world (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Static m))
      ∗ region (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Static m))))%I.
  Proof.
    iIntros "(Hfull & Hr & Hmap)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    iDestruct (region_revoked_to_static_preamble with "Hr [Hmap] HM") as "(Hr & HM & Hmap)".
    { iApply (big_sepM_mono with "Hmap"). iIntros (k x Hk) "Hr". iDestruct "Hr" as (? ? ? ?) "[? ?]".
      iExists _,_. iFrame. auto. }
    iAssert ([∗ map] a↦v ∈ m, (∃ (p : Perm) φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
                                 ∗ sts_state_std a Revoked)%I with "[Hmap]" as "Hmap".
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Hx".
      iDestruct "Hx" as (p φ Hpers Hne) "(Ha & Hrel & Hstate)".
      iFrame. iExists _,_. iFrame. auto. }
    iAssert (⌜Forall (λ a : Addr, std (revoke W) !! a = Some (Revoked)) (elements (dom (gset Addr) m))⌝%I)
      as %Hforall.
    { rewrite Forall_forall. iIntros (x Hx).
      apply elem_of_elements in Hx.
      apply elem_of_gmap_dom in Hx as [pw Hpw]. 
      iDestruct (big_sepM_delete with "Hmap") as "[[Hx Hstate] Hmap]";[apply Hpw|].
      iDestruct "Hx" as (p φ Hpers Hne) "(Hx & #Hrel)". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup. auto. 
    }
    iDestruct (monotone_revoke_list_region_def_mono with "[] Hfull Hr") as "[Hfull Hr]".
    { iPureIntro. apply related_sts_priv_world_static with (m':=m). apply Hforall. }
    iDestruct (big_sepM_sep with "Hmap") as "[Hmap Hstates]". 
    iMod (region_update_multiple_states _ _ with "[$Hfull $Hstates]") as "[Hfull Hstates]". 
    iModIntro.
    iDestruct (region_revoked_to_static_close with "HM Hr [Hmap Hstates]") as "[HM Hr]";auto.
    { iDestruct (big_sepM_sep with "[$Hmap $Hstates]") as "Hmap".
      iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "[Hx Hstate]".
      iDestruct "Hx" as (p φ Hne) "(Ha & Hrel)". iExists _,_. iFrame. iFrame. auto.
    }
    iDestruct "Hr" as (Mρ') "[Hr #Hforall]". iDestruct "Hforall" as %[Hforall' HdomMρ'].
    iFrame. 
    iExists M,Mρ'. iFrame. iSplit;auto.
    iPureIntro.
    assert (dom (gset Addr) m ⊆ dom (gset Addr) M) as Hmsub.
    { apply elem_of_subseteq. intros x Hx. rewrite -HdomMρ'.
      apply elem_of_gmap_dom. pose proof (Hforall' _ Hx) as Hx'. eauto. }
    apply std_update_multiple_dom_equal_eq;auto. 
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* -------------------------- Revoke a static region ------------------------------- *)

  Lemma region_static_to_revoked_states W (m m' : gmap Addr Word) :
    sts_full_world W
    ∗ sts_state_std_many m (Static m')
    ==∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Revoked)
    ∗ sts_state_std_many m Revoked.
  Proof.
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind.
    - rewrite /sts_state_std_many dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH".
      iMod (sts_update_std _ _ _ Revoked with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      erewrite (std_update_multiple_permutation _ (elements (_ ∪ _))).
      2: { rewrite elements_union_singleton // not_elem_of_dom //. }
      iFrame.
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

  Lemma region_map_get_φ_and_save_pred a γp M Mρ W :
    M !! a = Some γp →
    region_map_def M Mρ W -∗
    (∃ γpred p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ⌜γp = (γpred,p)⌝ ∗
              ⌜∀ Wv, Persistent (φ Wv)⌝ ∗ saved_pred_own γpred φ).
  Proof.
    iIntros (?) "Hr".
    iDestruct (big_sepM_lookup with "Hr") as (? ?) "(? & HH)"; eauto.
    iDestruct "HH" as (? ? ? ? ?) "(? & _)". iExists _,_,_.
    iFrame. eauto.
  Qed.

  Lemma region_map_get_φ_and_save_pred_m {V} (m: gmap Addr V) M Mρ W :
    dom (gset Addr) m ⊆ dom (gset Addr) M →
    region_map_def M Mρ W -∗
    ([∗ map] a↦_ ∈ m, ∃ γp γpred p φ,
        ⌜M !! a = Some γp⌝ ∗ ⌜γp = (γpred, p)⌝ ∗
        ⌜forall Wv, Persistent (φ Wv)⌝ ∗ saved_pred_own γpred φ)%I.
  Proof.
    pattern m. revert m. eapply map_ind.
    - rewrite big_sepM_empty. eauto.
    - iIntros (a x m Hmx Hind Hdom) "Hr".
      rewrite big_sepM_insert //.
      rewrite ->dom_insert in Hdom.
      assert (a ∈ dom (gset Addr) M) as [? ?]%elem_of_gmap_dom by set_solver.
      iDestruct (region_map_get_φ_and_save_pred a with "Hr")
        as "#Hpred"; eauto. iDestruct "Hpred" as (? ? ? ? ? ?) "?".
      iSplitR.
      { iExists _,_,_,_. eauto. }
      iApply (Hind with "Hr"). set_solver.
  Qed.

  (* this is fairly similar to [region_revoked_to_static_close_mid] *)
  Lemma region_map_close_to_revoked W M Mρ (m: gmap Addr Word) :
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ →
    (forall a, is_Some (m !! a) → is_Some (M !! a)) →
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ sts_state_std_many m Revoked
    ∗ ([∗ map] a↦_ ∈ m, ∃ γp γpred p φ,
          ⌜M !! a = Some γp⌝ ∗ ⌜γp = (γpred, p)⌝ ∗
          ⌜forall Wv, Persistent (φ Wv)⌝ ∗ saved_pred_own γpred φ)
    -∗
    ∃ Mρ', region_map_def M Mρ' W
    ∗ ⌜∀ a:Addr, a ∈ dom (gset Addr) m → Mρ' !! a = Some Revoked⌝
    ∗ ⌜dom (gset Addr) Mρ' = dom (gset Addr) Mρ⌝.
  Proof.
    revert M Mρ. pattern m. revert m. eapply map_ind.
    - intros. rewrite !difference_het_empty.
      iIntros "[? ?]". iExists _. iFrame. iPureIntro. split; eauto.
      intro. rewrite dom_empty elem_of_empty. done.
    - iIntros (a pw m Hma Hind M Mρ Hdom HmM) "(Hr & Hsts & #Hper)".
      rewrite !difference_het_insert_r !difference_het_delete_assoc.

      rewrite /sts_state_std_many !(big_sepM_insert _ m) //.
      iDestruct "Hper" as "(Hper_a & Hper)".
      iDestruct "Hsts" as "(Hst_a & Hsts)".

      iDestruct (Hind with "[$Hsts $Hr]") as (Mρ') "(Hr & #Hforall)".
      { rewrite !dom_delete. set_solver. }
      { intros x [? ?]. rewrite lookup_delete_is_Some.
        assert (a ≠ x) by congruence. split; auto.
        apply HmM. rewrite lookup_insert_is_Some'. eauto. }
      { iApply (big_sepM_mono with "Hper").
        iIntros (? ? ?) "HH". iDestruct "HH" as (? ? ? ? ? ? ?) "#?".
        iExists _,_,_,_. iSplitL. iPureIntro.
        rewrite lookup_delete_ne //. congruence. eauto. }

      iDestruct "Hforall" as %[HMρ' Hdom'].

      iAssert (region_map_def (delete a M) (<[a:=Revoked]> Mρ') W)
        with "[Hr]" as "Hr".
      { iApply (big_sepM_mono with "Hr").
        iIntros (a' y Ha') "Hr".
        iDestruct "Hr" as (ρ Ha'') "[Hstate Hρ]".
        assert (a' ≠ a).
        { intros ->. rewrite lookup_delete in Ha'. done. }
        iExists ρ. iFrame. iSplitR. by rewrite lookup_insert_ne //.
        destruct ρ; iFrame;[].
        iDestruct "Hρ" as (? ? ? ? ?) "(? & HH)".
        iDestruct "HH" as (? ?) "(? & ? & Hstatic)". iDestruct "Hstatic" as %Hstatic.
        iExists _,_,_. iFrame. repeat iSplitR; eauto. iExists _.
        iFrame. repeat iSplitR; eauto. iPureIntro.
        intros x Hx%Hstatic.
        assert (a ≠ x).
        { intros ->.
          assert (x ∈ dom (gset Addr) Mρ') as Hx' by (apply elem_of_gmap_dom; eauto).
          rewrite -> Hdom', dom_delete in Hx'. set_solver. }
        rewrite lookup_insert_ne //. }

      assert (is_Some (M !! a)) as [γp HMa].
      { apply HmM. rewrite lookup_insert. eauto. }

      iAssert (region_map_def (<[a:=γp]> (delete a M)) _ W) with "[Hr Hst_a]" as "Hr".
      { iApply big_sepM_insert. by rewrite lookup_delete. iFrame.
        iExists Revoked. iSplitR. by rewrite lookup_insert.
        iDestruct "Hper_a" as (? ? ? ? ? ? ?) "?".
        iFrame. destruct γp as [γ p]. iExists _,_,_. repeat iSplit; eauto.
        simplify_eq. eauto. }
      rewrite insert_delete insert_id //. iExists _.
      iFrame. iPureIntro; split.
      { intro x. rewrite dom_insert. rewrite elem_of_union elem_of_singleton.
        destruct (decide (x = a)) as [->|?]. by simplify_map_eq.
        intros [->|?]; [by exfalso|]. rewrite lookup_insert_ne//. eauto. }

      rewrite dom_insert_L Hdom' dom_delete_L.
      assert (a ∈ dom (gset Addr) Mρ).
      { rewrite elem_of_subseteq in Hdom |- * => Hdom. apply Hdom.
        rewrite -elem_of_gmap_dom. eauto. }
      rewrite singleton_union_difference_L. (* TODO: add to set_solver? *)
      set_solver.
  Qed.

  Lemma related_sts_priv_world_revoked W l (m: gmap Addr Word) :
    Forall (λ a:Addr, (std W) !! a = Some (Static m)) l →
    related_sts_priv_world W (std_update_multiple W l Revoked).
  Proof.
    intros Hforall.
    induction l.
    - apply related_sts_priv_refl_world.
    - apply Forall_cons_1 in Hforall as [Ha Hforall].
      eapply related_sts_priv_trans_world;[by apply IHl|].
      split.
      2: { rewrite std_update_multiple_loc_rel. apply related_sts_priv_refl. }
      split; try by (rewrite dom_insert_L; set_solver).
      intros j x0 y Hx0 Hy. cbn in *.
      destruct (decide (a = j)).
      { subst j. 
        rewrite lookup_insert in Hy. simplify_eq.
        destruct (decide (a ∈ l)).
        { rewrite std_sta_update_multiple_lookup_in_i in Hx0; eauto.
          simplify_eq. left. }
        rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
        rewrite /revoke /std /= in Ha. rewrite Ha in Hx0.
        simplify_eq. right with Temporary.
        { left. constructor. }
        right with Revoked;[|left].
        right. constructor. }
      { rewrite lookup_insert_ne in Hy; auto. rewrite Hx0 in Hy. simplify_eq.
        left. }
  Qed.

  Lemma region_static_to_revoked W (a: Addr) (m: gmap Addr Word) :
    let W' := std_update_multiple (revoke W) (elements (dom (gset Addr) m)) Revoked in
    std W !! a = Some (Static m) →
    sts_full_world (revoke W)
    ∗ region (revoke W)
    ==∗
    sts_full_world W'
    ∗ region W'
    ∗ static_resources m
    ∗ ⌜a ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (W' Ha) "(Hsts & Hr)".
    iMod (region_map_has_static_rels_all _ m a with "[$Hr $Hsts]") as "(Hr & Hsts & Hrels)";eauto.
    { apply revoke_lookup_Static. auto. }
    
    rewrite region_eq /region_def. iDestruct "Hr" as (M Mρ) "(HM & % & Hdom & Hr)".
    iDestruct "Hdom" as %Hdom.
    assert (std (revoke W) !! a = Some (Static m)) as Hl'.
    { rewrite revoke_monotone_lookup_same' //. rewrite Ha.
      intros ?%Some_eq_inj. congruence. }
    iDestruct (region_map_has_static_addr with "[$Hr $Hsts]") as %[HmM ?]; eauto.

    assert (dom (gset Addr) m ⊆ dom (gset Addr) M).
    { rewrite elem_of_subseteq -Hdom. intros x Hx.
      specialize (HmM x Hx). rewrite -elem_of_gmap_dom. eauto. }
    iDestruct (region_map_get_φ_and_save_pred_m m with "Hr") as "#Hpredφ"; eauto.

    iDestruct (region_map_open_all_static with "[$Hr $Hsts $HM $Hrels]")
      as "(Hr & Hsts & Hst_m & Hres & HM)"; eauto.

    iDestruct (sts_full_state_std_many with "[$Hsts $Hst_m]") as %?.
    iDestruct (monotone_revoke_list_region_def_mono _ _ _ _ W'
                 with "[] [Hsts] [Hr]") as "(Hsts & Hr)"; eauto.
    { iPureIntro. eapply (related_sts_priv_world_revoked _ _ m); auto. }

    iDestruct (region_update_multiple_states _ _ _ Revoked
                 with "[$Hsts $Hst_m]") as ">(Hsts & Hst_m)".
    rewrite -/W'.

    iDestruct (region_map_close_to_revoked with "[$Hr $Hst_m]")
      as (Mρ') "(Hr & % & Hdomρ')"; eauto.
    by rewrite Hdom.
    { intros x [? Hx]. rewrite elem_of_gmap_dom -Hdom -elem_of_gmap_dom.
      specialize (HmM x). rewrite -elem_of_gmap_dom in HmM |- * => HmM.
      eauto. }
    iDestruct "Hdomρ'" as %Hdomρ'.

    iModIntro. iFrame. iSplitL; eauto.
    iExists M,Mρ'. iFrame. iPureIntro. split; eauto.
    { rewrite /W' /=. apply std_update_multiple_dom_equal_eq; eauto. }
    { rewrite Hdomρ' //. }
Qed.

  Lemma region_has_static_addr_Forall (W:WORLD) (a:Addr) (m: gmap Addr Word):
    std W !! a = Some (Static m) →
    region W ∗ sts_full_world W
           -∗ ⌜Forall (λ a':Addr, std W !! a' = Some (Static m))
           (elements (dom (gset Addr) m))⌝.
  Proof.
    iIntros (?) "(Hr & Hsts)". rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(? & % & Hdom & Hr)". iDestruct "Hdom" as %Hdom.
    iDestruct (full_sts_Mρ_agree with "Hsts Hr") as %Hagree; eauto.
    
    iDestruct (region_map_has_static_addr with "[$Hr $Hsts]") as %[HH ?]; eauto.
    iPureIntro. rewrite -set_Forall_elements. intros x Hx. rewrite Hagree. auto.
  Qed.
  
End heap.
