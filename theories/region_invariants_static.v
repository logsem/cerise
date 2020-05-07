From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants multiple_updates region_invariants_revocation sts.
Require Import stdpp.countable.
Import uPred.

Section heap.
  Context `{heapG Σ, memG Σ, regG Σ, STSG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (prodO STS STS).
  Implicit Types W : WORLD.

  (* This file provides three main lemmas:
     - one that opens all of a static region at once
     - one that closes what was a static region and turns it into a temporary one
     - one that turns a revoked region into a static region
   *)

  (* ------------------------------------------------------------------------ *)
  (* Auxiliary definitions on maps and delete_list; should be moved elsewhere *)

  Definition map_difference_het
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1: gmap A B) (m2: gmap A C): gmap A B
  :=
    filter (fun '(k, v) => m2 !! k = None) m1.

  Notation "m1 ∖∖ m2" := (map_difference_het m1 m2) (at level 40, left associativity).

  Lemma map_eq' {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m1 m2: gmap A B):
    m1 = m2 ↔ (forall k v, m1 !! k = Some v ↔ m2 !! k = Some v).
  Proof.
    split. intros ->. done.
    intros Heq. apply map_eq. intro k. destruct (m2 !! k) eqn:HH.
    { by apply Heq. }
    { destruct (m1 !! k) eqn:HHH; auto. apply Heq in HHH. congruence. }
  Qed.

  Lemma difference_het_lookup_Some
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
    (m1 ∖∖ m2) !! k = Some v ↔ m1 !! k = Some v ∧ m2 !! k = None.
  Proof. by rewrite /map_difference_het map_filter_lookup_Some. Qed.

  Lemma difference_het_lookup_None
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
    (m1 ∖∖ m2) !! k = None ↔ m1 !! k = None ∨ is_Some (m2 !! k).
  Proof.
    rewrite /map_difference_het map_filter_lookup_None.
    split; intros [HH1|HH2]; eauto.
    { destruct (m1 !! k) eqn:?; eauto; right.
      destruct (m2 !! k) eqn:?; eauto. exfalso. eapply HH2; eauto. }
    { destruct (m1 !! k) eqn:?; eauto; right.
      destruct (m2 !! k) eqn:?; eauto. destruct HH2 as [? ?]. congruence. }
  Qed.

  Lemma difference_het_empty
    {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m: gmap A B):
    m ∖∖ (∅ : gmap A C) = m.
  Proof.
    rewrite /map_difference_het map_eq'. intros k v.
    rewrite map_filter_lookup_Some. rewrite lookup_empty. set_solver.
  Qed.

   Lemma difference_het_eq_empty
    {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
    (m: gmap A B):
    m ∖∖ m = (∅ : gmap A B).
  Proof.
    rewrite /map_difference_het map_eq'. intros k v.
    rewrite map_filter_lookup_Some. rewrite lookup_empty. set_solver.
  Qed.

  Lemma difference_het_insert_r
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C) (k: A) (v: C):
    m1 ∖∖ (<[ k := v ]> m2) = delete k (m1 ∖∖ m2).
  Proof.
    intros.
    rewrite /map_difference_het map_eq'. intros k' v'.
    rewrite map_filter_lookup_Some lookup_delete_Some.
    rewrite map_filter_lookup_Some lookup_insert_None. set_solver.
  Qed.

  Lemma difference_het_insert_l
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C) (k: A) (v: B):
    m2 !! k = None ->
    <[ k := v ]> m1 ∖∖ m2 = <[ k := v ]> (m1 ∖∖ m2).
  Proof.
    intros.
    rewrite /map_difference_het map_eq'. intros k' v'.
    rewrite map_filter_lookup_Some lookup_insert_Some.
    rewrite -map_filter_insert;auto.
      by rewrite map_filter_lookup_Some lookup_insert_Some.
  Qed.

  Lemma difference_het_delete_assoc
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C) (k: A):
    delete k (m1 ∖∖ m2) = (delete k m1) ∖∖ m2.
  Proof.
    intros.
    rewrite /map_difference_het map_eq'. intros k' v'.
    rewrite map_filter_lookup_Some.
    rewrite -map_filter_delete;auto.
    rewrite map_filter_lookup_Some. set_solver.
  Qed.

  Lemma dom_difference_het
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C):
    dom (gset A) (m1 ∖∖ m2) = dom (gset A) m1 ∖ dom (gset A) m2.
  Proof.
    apply (anti_symm _).
    { rewrite elem_of_subseteq. intro k.
      rewrite -elem_of_gmap_dom. intros [v Hv].
      rewrite difference_het_lookup_Some in Hv * => Hv.
      destruct Hv as [? ?].
      rewrite elem_of_difference -!elem_of_gmap_dom. split; eauto.
      intros [? ?]. congruence. }
    { rewrite elem_of_subseteq. intro k.
      rewrite elem_of_difference -!elem_of_gmap_dom. intros [[v ?] Hcontra].
      exists v. rewrite difference_het_lookup_Some. split; eauto.
      destruct (m2 !! k) eqn:?; eauto. exfalso. apply Hcontra. eauto. }
  Qed.

  Lemma delete_elements_eq_difference_het
      {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
      (m1: gmap A B) (m2: gmap A C):
    delete_list (elements (dom (gset A) m2)) m1 = m1 ∖∖ m2.
  Proof.
    set (l := elements (dom (gset A) m2)).
    assert (l ≡ₚ elements (dom (gset A) m2)) as Hl by reflexivity.
    clearbody l. revert l Hl. revert m1. pattern m2. revert m2.
    apply map_ind.
    - intros m1 l. rewrite dom_empty_L elements_empty difference_het_empty.
      rewrite Permutation_nil. intros ->. reflexivity.
    - intros k v m2 Hm2k HI m1 l Hm1l.
      rewrite difference_het_insert_r.
      rewrite dom_insert in Hm1l * => Hm1l.
      move: Hm1l. rewrite elements_union_singleton.
      2: rewrite -elem_of_gmap_dom; intros [? ?]; congruence.
      intros Hm1l.
      transitivity (delete k (delete_list (elements (dom (gset A) m2)) m1)).
      { erewrite delete_list_permutation. 2: eauto. reflexivity. }
      { rewrite HI//. }
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- Opening a static region ------------------------------- *)

  Lemma region_map_delete_static (M: gmap Addr _) (Mρ: gmap Addr _) W m l p v:
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ →
    is_Some (M !! l) →
    Mρ !! l = Some (Static m) →
    m !! l = Some (p, v) →
    region_map_def M Mρ W -∗
    region_map_def (delete l M) Mρ W ∗
    l ↦ₐ[p] v ∗ sts_state_std (encode l) (Static m).
  Proof.
    intros Hdom HMl HMρ Hm.
    iIntros "Hr". destruct HMl as [? ?].
    iDestruct (big_sepM_delete _ _ l with "Hr") as "(Hl & Hr)"; eauto; [].
    iFrame. iDestruct "Hl" as (ρ' Hρ') "(? & Hst)".
    assert (ρ' = Static m) as -> by congruence.
    iDestruct "Hst" as (? ? ?) "(% & ? & ? & H)".
    iDestruct "H" as (p' v') "(% & ? & ? & _)". 
    assert (p' = p ∧ v' = v) as (-> & ->) by (split; congruence). iFrame.
  Qed.

  Definition sts_state_std_many {V} (m: gmap Addr V) (ρ: region_type) :=
    ([∗ map] a↦_ ∈ m, sts_state_std (encode a) ρ)%I.

  Definition static_resources (m: gmap Addr (Perm * Word)) :=
    ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ a ↦ₐ[p] v)%I.

  Lemma region_map_open_some_static (M: gmap Addr _) Mρ W (m m_all: gmap Addr (Perm * Word)) :
    m ⊆ m_all →
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m_all)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) Mρ W
    ∗ sts_full_world sts_std W
    ∗ static_resources m
    ∗ sts_state_std_many m (Static m_all).
  Proof.
    pattern m. revert m. refine (map_ind _ _ _).
    - intros **. iIntros "(?&?)".
      rewrite !difference_het_empty /static_resources /sts_state_std_many !big_sepM_empty /=.
      iFrame; eauto.
    - intros a [p v] m Hma HI Hsub_all Hm_all Hdom.
      iIntros "(Hr & Hsts)".
      assert (a ∈ dom (gset Addr) Mρ).
      { specialize (Hm_all a).
        feed pose proof Hm_all. rewrite dom_insert; set_solver.
        rewrite -elem_of_gmap_dom. eauto. }
      assert (a ∈ dom (gset Addr) M) by (rewrite -Hdom; auto).
      rewrite difference_het_insert_r //.
      feed specialize HI; eauto.
      { transitivity (<[a:=(p,v)]> m); auto. by apply insert_subseteq. }
      { intros a' Ha'. apply Hm_all. rewrite dom_insert. set_solver. }
      iDestruct (HI with "[Hr Hsts]") as "(Hr & Hfull & ? & Hmap)"; [by iFrame|..].
      iDestruct (region_map_delete_static _ _ _ m_all a with "Hr") as "(? & ? & ?)".
      { rewrite dom_difference_het. rewrite Hdom. set_solver. }
      { rewrite elem_of_gmap_dom. rewrite dom_difference_het.
        assert (a ∉ dom (gset Addr) m) by (by apply not_elem_of_dom).
        set_solver. }
      { apply Hm_all. rewrite dom_insert; set_solver. }
      { eapply lookup_weaken; [| apply Hsub_all]. by rewrite lookup_insert. }
      iFrame. rewrite /static_resources /sts_state_std_many !big_sepM_insert //.
      iFrame. eauto.
  Qed.

  Lemma region_map_open_all_static M Mρ W (m: gmap Addr (Perm * Word)) :
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ sts_full_world sts_std W
    ∗ sts_state_std_many m (Static m)
    ∗ static_resources m.
  Proof.
    iIntros (HH Hdom) "(Hr & Hsts)".
    iDestruct (region_map_open_some_static M Mρ W m m with "[Hr Hsts]")
      as "(Hr & Hsts & ? & ?)"; auto; iFrame.
    iApply (big_sepM_mono with "Hr").
    iIntros (k γp HMk) "H". iDestruct "H" as (ρ HMρ) "(Hst & Hρ)". iExists ρ.
    rewrite difference_het_lookup_Some in HMk * => HMk. destruct HMk as [HMk Hmk].
    iSplitR. iPureIntro. by rewrite difference_het_lookup_Some; eauto.
    iFrame. destruct ρ as [ | | | m']; (try by iFrame); [].
    iDestruct "Hρ" as (γpred p φ Heq Hpers) "[Hsaved Hρ]". 
    iDestruct "Hρ" as (p' v Hm') "(? & ? & Hothers)". iDestruct "Hothers" as %Hothers.
    iExists _,_,_. iFrame. repeat iSplitR;auto. iExists _,_. iFrame. iPureIntro. split; eauto.
    intros a' Ha'. rewrite difference_het_lookup_Some. split; eauto.
    destruct (m !! a') eqn:?; eauto. exfalso.
    specialize (HH a'). feed specialize HH. by rewrite -elem_of_gmap_dom; eauto.
    specialize (Hothers a'). feed specialize Hothers; auto.
    assert (m' = m) by congruence. congruence.
  Qed.

  Lemma region_map_has_static_addr M Mρ W (l: Addr) m :
    (std_sta W) !! (encode l) = Some (encode (Static m)) →
    dom_equal (std_sta W) M →
    region_map_def M Mρ W ∗ sts_full_world sts_std W -∗
    ⌜(forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m))⌝ ∗
    ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl Hdom) "(Hr & Hsts)". unfold dom_equal in Hdom.
    specialize (Hdom (encode l)) as [Hdom _].
    feed destruct Hdom as (a & ?%encode_injective & (? & ?)); eauto.
    subst a.
    iDestruct (big_sepM_lookup _ _ l with "Hr") as "Hl"; eauto.
    iDestruct "Hl" as (ρ Hρ) "(Hst & Hρ)".
    iDestruct (sts_full_state_std with "Hsts Hst") as %HH.
    rewrite HWl in HH. apply Some_eq_inj, encode_injective in HH. subst ρ.
    iDestruct "Hρ" as (? ? ?) "(? & ? & ? & Hρ)". 
    iDestruct "Hρ" as (? ? ?) "(? & ? & %)". intros. iPureIntro. split; eauto.
    rewrite -elem_of_gmap_dom; eauto.
  Qed.

  Lemma region_open_static W (m: gmap Addr (Perm * Word)) (l: Addr) :
    (std_sta W) !! (encode l) = Some (encode (Static m)) →
    region W ∗ sts_full_world sts_std W -∗
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world sts_std W
    ∗ sts_state_std_many m (Static m)
    ∗ static_resources m
    ∗ ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl) "(Hr & Hsts)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(? & % & % & Hr)".
    iDestruct (region_map_has_static_addr with "[Hr Hsts]")
      as %(Hstatic & ?); eauto; [by iFrame|].
    iDestruct (region_map_open_all_static M Mρ W m with "[Hr Hsts]")
      as "(Hr & Hsts & ? & ?)"; eauto; [by iFrame|].
    iFrame. iSplitL; eauto. rewrite open_region_many_eq /open_region_many_def.
    iExists M,Mρ. iFrame. do 2 (iSplitR; eauto).
    rewrite !delete_elements_eq_difference_het. eauto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ---------------------- Turn a static region into a temporary one ---------------- *)

  Lemma related_sts_pub_world_static_to_temporary (l: list Addr) m W:
    rel_is_std W →
    Forall (λ (a:Addr), (std_sta W) !! (encode a) = Some (encode (Static m))) l →
    related_sts_pub_world W (std_update_multiple W l Temporary).
  Proof.
    intros Hstd Hforall.
    induction l.
    - split; apply related_sts_pub_refl.
    - rewrite Forall_cons in Hforall *; move=>[Ha Hforall].
      eapply related_sts_pub_trans_world;[by apply IHl|].
      cbn. set W' := std_update_multiple W l Temporary.
      rewrite /std_update /related_sts_pub_world /=. split.
      2: { apply related_sts_pub_refl. }
      unfold related_sts_pub. rewrite !dom_insert_L.
      repeat split_and; [set_solver ..|].
      intros i r1 r2 r1' r2' Hr Hr'.
      apply std_update_multiple_rel_is_std with (l:=l) (ρ:=Temporary) in Hstd.
      rewrite -/W' in Hstd.
      feed pose proof (Hstd i) as Hstdi; eauto. rewrite /rel_is_std_i /= in Hstdi.
      unfold std_sta, std_rel in *. simplify_eq.
      destruct (decide (i = encode a)).
      { subst i. rewrite lookup_insert in Hr'. simplify_eq. do 2 split; eauto.
        intros x y Hx Hy. simplify_map_eq.
        destruct (decide (a ∈ l)).
        { rewrite std_sta_update_multiple_lookup_in // in Hx. simplify_eq. reflexivity. }
        rewrite std_sta_update_multiple_lookup_same /std_sta // in Hx. simplify_eq.
        eapply rtc_once, convert_rel_of_rel. constructor. }
      { rewrite lookup_insert_ne // in Hr'. rewrite Hr in Hr'. simplify_eq.
        do 2 split; eauto. intros x y Hx Hy. rewrite lookup_insert_ne // in Hy.
        rewrite Hx in Hy; simplify_eq. reflexivity. }
  Qed.

  Lemma open_region_world_static_to_temporary l m W :
    rel_is_std W →
    Forall (λ (a:Addr), (std_sta W) !! (encode a) = Some (encode (Static m))) l →
    open_region_many l W
    -∗
    open_region_many l (std_update_multiple W l Temporary).
  Proof.
    intros. iApply open_region_many_monotone.
    { apply elem_of_equiv_L. intro.
      rewrite -std_update_multiple_dom_equal; auto.
      intros i Hi. apply elem_of_gmap_dom.
      apply elem_of_list_fmap in Hi as [y [Heq Hy] ]. subst. 
      eexists. eapply Forall_forall in H4; eauto. }
    { eapply related_sts_pub_world_static_to_temporary; eauto. }
  Qed.

  Lemma region_close_temporary_many (m: gmap Addr (Perm * Word)) W:
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ ([∗ map] a↦pv ∈ m, ∃ p _v φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
        ⌜pv = (p, _v)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m Temporary
    ∗ sts_full_world sts_std W
    -∗
    region W ∗ sts_full_world sts_std W.
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
      iDestruct "Ha" as (? ? ? ? ?) "(Hatmp&?)".
      iDestruct "Hatmp" as (? ?) "(?&?&?)".
      iApply HInd. iFrame.
      iApply (region_close_next _ _ _ a _ _ Temporary).
      + congruence.
      + intros [? ?]. congruence.
      + intros [? ?]%elem_of_elements%elem_of_gmap_dom. congruence.
      + iFrame. iSplitR; auto. unfold monotonicity_guarantees_region.
        destruct (pwl _); eauto.
  Qed.

  Lemma region_static_to_temporary_states W (m m' : gmap Addr (Perm * Word)) :
    sts_full_world sts_std W
    ∗ sts_state_std_many m (Static m')
    ==∗ sts_full_world sts_std (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
    ∗ sts_state_std_many m Temporary.
  Proof.
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind.
    - rewrite /sts_state_std_many dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH".
      iMod (sts_update_std _ _ _ Temporary with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      erewrite (std_update_multiple_permutation _ (elements (_ ∪ _))).
      2: { rewrite elements_union_singleton // not_elem_of_dom //. }
      iDestruct (sts_full_world_std with "Hfull") as %Hstd.
      iAssert (⌜is_Some ((std_update_multiple W (elements (dom (gset Addr) m)) Temporary).1.2 !! (encode x))⌝%I)
        as %Hsome.
      { rewrite /sts_full_world /sts_full_std /=. iDestruct "Hfull" as "[ [#Hdom _] _]".
        iDestruct "Hdom" as %Hdom. iPureIntro.
        rewrite elem_of_gmap_dom. rewrite dom_insert_L in Hdom. set_solver. }
      pose proof (Hstd _ Hsome) as Hstdx.
      apply insert_id in Hstdx. rewrite /std_rel /= in Hstdx. rewrite -Hstdx. iFrame.
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

  Lemma future_priv_mono_is_future_pub_mono (φ: _ → iProp Σ) v:
    (future_priv_mono φ v -∗ future_pub_mono φ v)%I.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    eauto using related_sts_pub_priv_world.
  Qed.

  Lemma sts_full_state_std_many {V} (m: gmap Addr V) (ρ:region_type) W:
    sts_full_world sts_std W
    ∗ sts_state_std_many m ρ
    -∗
    ⌜Forall (λ (a:Addr), std_sta W !! encode a = Some (encode ρ)) (elements (dom (gset Addr) m))⌝.
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

  Lemma region_close_static_to_temporary (m: gmap Addr (Perm * Word)) W :
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world sts_std W
    ∗ ([∗ map] a↦pv ∈ m, ∃ p _v φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         ⌜pv = (p, _v)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m (Static m)
    ==∗
    sts_full_world sts_std (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
    ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).
  Proof.
    iIntros "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_world_std with "Hsts") as %?.
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_static_to_temporary_states with "[Hsts Hst]") as ">[Hsts Hst]".
      by iFrame.
    iModIntro.
    iDestruct (open_region_world_static_to_temporary with "HR") as "HR"; eauto.
    iDestruct (region_close_temporary_many with "[HR Hres Hst Hsts]") as "(?&?)".
    { iFrame. iApply (big_sepM_mono with "Hres"). iIntros (a pv ?) "H".
      iDestruct "H" as (p _v φ ? ?) "(Htmp & ?)". iExists p, _v, φ. iSplitR;eauto.
      iFrame. unfold temp_resources. iDestruct "Htmp" as (v ?) "(Ha&Hmon&?)".
      iSplit;auto. iExists v. iSplitR; eauto. iFrame "Ha".
      iAssert (future_pub_mono φ v)%I with "[Hmon]" as "#Hφ".
      { destruct (pwl p); eauto. by iApply future_priv_mono_is_future_pub_mono. }
      iFrame. iApply "Hφ"; eauto. iPureIntro.
      eapply related_sts_pub_world_static_to_temporary; eauto. }
    iFrame.
  Qed.

  (* In this version the user is only required to show that the resources are valid in the updated world *)
  Lemma region_close_static_to_temporary_alt (m: gmap Addr (Perm * Word)) W :
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world sts_std W
    ∗ ([∗ map] a↦pv ∈ m, ∃ p _v φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         ⌜pv = (p, _v)⌝ ∗ temp_resources (std_update_multiple W (elements (dom (gset Addr) m)) Temporary) φ a p ∗ rel a p φ)
    ∗ sts_state_std_many m (Static m)
    ==∗
    sts_full_world sts_std (std_update_multiple W (elements (dom (gset Addr) m)) Temporary)
    ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) Temporary).
  Proof.
    iIntros "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_world_std with "Hsts") as %?.
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_static_to_temporary_states with "[Hsts Hst]") as ">[Hsts Hst]".
      by iFrame.
    iModIntro.
    iDestruct (open_region_world_static_to_temporary with "HR") as "HR"; eauto.
    iDestruct (region_close_temporary_many with "[HR Hres Hst Hsts]") as "(?&?)"; iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------ Allocate a Static region from a Revoked one ------------------ *)

  Lemma related_sts_priv_world_static W l (m' : gmap Addr (Perm * Word)) :
    rel_is_std W -> 
    Forall (λ a : Addr, (std_sta W) !! (encode a) = Some (encode Revoked)) l →
    related_sts_priv_world W (std_update_multiple W l (Static m')).
  Proof.
    intros Hstd Hforall.
    induction l. 
    - split;apply related_sts_priv_refl. 
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto. 
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split;[|split].
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j r1 r2 r1' r2' Hr Hr'.
           rewrite /std_update in Hr'. simpl in *.
           apply std_update_multiple_rel_is_std with (l:=l) (ρ:=Static m') in Hstd.
           assert (is_Some (std_rel (std_update_multiple W l (Static m')) !! j)) as Hsome.
           eauto. apply Hstd in Hsome.
           destruct (decide (encode a = j)).
           +++ subst. rewrite lookup_insert in Hr'.
               rewrite Hsome in Hr. inversion Hr'; inversion Hr; subst.
               repeat split;auto.
               intros x0 y Hx0 Hy. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (a ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same in Hx0; auto.
               rewrite /revoke /std_sta /= in Hi. (* apply anti_revoke_lookup_Revoked in Hi as [Hrev | Htemp]. *)
               (* * rewrite Hrev in Hx0. inversion Hx0; subst. *)
               rewrite Hi in Hx0. inversion Hx0; subst. 
               right with (encode Temporary).
               { left. exists Revoked,Temporary. repeat split;auto. constructor. }
               right with (encode (Static m'));[|left]. right. exists Temporary,(Static m'). repeat split;auto.
               constructor. 
               (* * rewrite Htemp in Hx0; inversion Hx0; auto. *)
               (*   right with (encode (Static m'));[|left]. right. exists Temporary,(Static m'). repeat split;auto. *)
               (*   constructor. *)
           +++ rewrite lookup_insert_ne in Hr'; auto. rewrite Hsome in Hr'. rewrite Hsome in Hr.
               inversion Hr'; inversion Hr. subst. repeat split;auto.
               intros x y Hx Hy.
               rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst; left.
  Qed.

  Lemma std_update_multiple_dom_equal_eq W M (m: gmap Addr (Perm * Word)) ρ :
    dom_equal (std_sta W) M -> 
    dom (gset Addr) m ⊆ dom (gset Addr) M ->
    dom_equal (std_sta (std_update_multiple W (elements (dom (gset Addr) m)) ρ)) M.
  Proof.
    intros Hdom Hsub.
    split.
    - intros Hsome.
      destruct Hdom with i as [Hdom1 _].
      apply Hdom1. 
      apply elem_of_gmap_dom.
      rewrite (std_update_multiple_dom_equal _ (elements (dom (gset Addr) m)) ρ).
      + apply elem_of_gmap_dom. eauto.
      + intros i0 Hi0.
        apply elem_of_list_fmap in Hi0 as [y [Hy Hin] ]. subst.
        apply elem_of_gmap_dom.
        destruct Hdom with (encode y) as [_ Hdom2].
        apply Hdom2. exists y. split;auto.
        apply elem_of_gmap_dom. apply elem_of_subseteq in Hsub. apply Hsub.
        by apply elem_of_elements. 
    - intros [a [Heq Ha] ].
      apply elem_of_gmap_dom.
      rewrite -(std_update_multiple_dom_equal _ (elements (dom (gset Addr) m)) ρ).
      + apply elem_of_gmap_dom.
        destruct Hdom with i as [_ Hdom2].
        apply Hdom2. exists a. auto. 
      + intros i0 Hi0.
        apply elem_of_list_fmap in Hi0 as [y [Hy Hin] ]. subst.
        apply elem_of_gmap_dom.
        destruct Hdom with (encode y) as [_ Hdom2].
        apply Hdom2. exists y. split;auto.
        apply elem_of_gmap_dom. apply elem_of_subseteq in Hsub. apply Hsub.
        by apply elem_of_elements. 
  Qed. 
     
  (* The difficulty with static regions is that if one of the addresses is in its static state, all others must be. 
     We can therefore not update them one by one (since invariants will break in the middle of the state change). 
     Instead, we need to: 
              (1) assert that the states are all curently Revoked + delete them from the region map
              (2) update the full sts for all addresses in the static region 
              (3) insert the updated states back into the region map
   *)

  (* (1) assert that the states are all curently Revoked + delete them from the region map *)
  Lemma region_revoked_to_static_preamble W M Mρ (m: gmap Addr (Perm * Word)) :
    region_map_def M Mρ W -∗
    ([∗ map] a↦pv ∈ m, ∃ p v φ, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ) -∗
    RELS M -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ RELS M
    ∗ ([∗ map] a↦pv ∈ m, ∃ p v φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗
                              a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) Revoked).
  Proof.
    iIntros "Hr Hmap HM".
    iInduction (m) as [|x l] "IH" using map_ind. 
    - rewrite difference_het_empty difference_het_empty /= big_sepM_empty big_sepM_empty.
      iFrame. 
    - rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct ("IH" with "Hr Hmap HM") as "(Hr & HM & Hmap)". iClear "IH".
      iDestruct "Hx" as (p v φ Heq Hne) "[Hx Hrel]".
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
          iDestruct "Hinv" as (p2 v') "(% & % & Hinv & _)"; simplify_eq. 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
      }
      subst ρ. iDestruct "Hinv" as (γpred' p' φ' Heq' Hpers) "[#Hsaved _]". 
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros;by rewrite Hρ|]. 
      iFrame. iSplitL "Hr". 
      { rewrite delete_insert;[|by rewrite lookup_delete]. iFrame. }
      iApply big_sepM_insert;auto. iFrame. iExists p,v,φ'. simplify_eq. repeat iSplit;auto.
  Qed.

  (* (2) update the full sts for all addresses in the static region *)
  (* in order to show this lemma we need to generalize the statement to all maps m', such that we can update 
     to the final step of the map in the induction *)
  Lemma region_revoked_to_static_states W (m m' : gmap Addr (Perm * Word)) :
    sts_full_world sts_std W
    ∗ sts_state_std_many m Revoked
    ==∗ sts_full_world sts_std (std_update_multiple W (elements (dom (gset Addr) m)) (Static m'))
    ∗ sts_state_std_many m (Static m').
  Proof. 
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind. 
    - rewrite /sts_state_std_many dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH". 
      iMod (sts_update_std _ _ _ (Static m') with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      assert (elements ({[x]} ∪ dom (gset Addr) m) ≡ₚ x :: elements (dom (gset Addr) m)) as Hperm.
      { apply elements_union_singleton. intros Hcontr. apply elem_of_gmap_dom in Hcontr as [y Hy].
        rewrite H3 in Hy. inversion Hy. }
      apply std_update_multiple_permutation with (W:=W) (ρ:=Static m') in Hperm. rewrite Hperm /=.
      iDestruct (sts_full_world_std with "Hfull") as %Hstd.
      iAssert (⌜is_Some ((std_update_multiple W (elements (dom (gset Addr) m)) (Static m')).1.2 !! (encode x))⌝%I)
        as %Hsome.
      { rewrite /sts_full_world /sts_full_std /=. iDestruct "Hfull" as "[ [#Hdom _] _]".
        iDestruct "Hdom" as %Hdom. iPureIntro. apply elem_of_gmap_dom. rewrite dom_insert_L in Hdom. set_solver. }
      pose proof (Hstd _ Hsome) as Hstdx.
      apply insert_id in Hstdx. rewrite /std_rel /= in Hstdx. rewrite -Hstdx. iFrame. 
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

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
    -∗ ([∗ map] a↦pv ∈ m, ∃ p v φ (* γpred *), ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ (* ∗ saved_pred_own γpred φ *) ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) (Static m'))
    -∗ ∃ Mρ', region_map_def M Mρ' W
            ∗ RELS M'
            ∗ ⌜dom (gset Addr) Mρ' = dom (gset Addr) Mρ⌝
            ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m' → Mρ' !! a' = Some (Static m')⌝.
  Proof.
    iIntros (HsubM Hsub Hsame HmM Hmid Hdom) "Hr HM Hmap".
    iRevert (HsubM HmM Hmid Hdom). iInduction (m) as [|x l] "IH" using map_ind forall (M Mρ) . 
    - iIntros (HsubM HmM Hmid Hdom). rewrite difference_het_empty difference_het_empty /=. iExists Mρ. iFrame.
      repeat rewrite difference_het_empty in Hmid. auto. 
    - iIntros (HsubM HmM Hmid Hdom).
      rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct "Hx" as (p v φ (* γpred *) Hpers Heq Hne) "(Hx & #Hrel & Hstate)".
      repeat rewrite difference_het_delete_assoc.
      iAssert (region_map_def (delete x M ∖∖ m) (<[x:=Static m']> Mρ ∖∖ m) W) with "[Hr]" as "Hr".
      { iApply (big_sepM_mono with "Hr").
        iIntros (a y Ha) "Hr".
        iDestruct "Hr" as (ρ Ha') "[Hstate Hρ]".
        assert (a ≠ x) as Hne'.
        { intros Hcontr; subst a. rewrite -difference_het_delete_assoc lookup_delete in Ha. done. }
        iExists ρ. iFrame. iSplitR.
        { rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          rewrite -difference_het_delete_assoc lookup_delete_ne in Ha';auto. }
        destruct ρ; iFrame. iDestruct "Hρ" as (? Hg Hp' Heq' Hpers') "[Hsaved Hρ]".
        iDestruct "Hρ" as (p' v' ? ?) "[Ha #Hforall]".
        iExists _,_,_. repeat iSplit;auto. iExists p',v'. repeat iSplit;auto. iDestruct "Hforall" as %Hforall.
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
        - subst. rewrite Ha in H3. done.
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
          iExists p,v. iFrame. repeat iSplit;auto. iPureIntro. apply Hsame. subst. apply lookup_insert. 
      }
      apply insert_id in HMx. rewrite insert_delete HMx. 
      iExists Mρ'. iFrame. repeat iSplit;auto. iPureIntro.
      rewrite Hdom' dom_insert_L.
      assert (x ∈ dom (gset Addr) Mρ) as Hin;[|set_solver].
      apply elem_of_subseteq in Hdom. apply Hdom. apply elem_of_gmap_dom. apply HmM. rewrite lookup_insert; eauto. 
  Qed.

  Lemma RELS_sub M (m : gmap Addr (Perm * Word)) :
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
    -∗ ([∗ map] a↦pv ∈ m, ∃ p v φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) (Static m))
    -∗ RELS M ∗ ∃ Mρ, region_map_def M Mρ W
                   ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)⌝
                   ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝.
  Proof.
    iIntros (Hdom) "HM Hr Hmap".
    iDestruct (RELS_sub with "HM [Hmap]") as %Hsub.
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Ha".
      iDestruct "Ha" as (p v φ Heq Hpers Hne) "(_ & Hrel & _)". eauto.
    }
    iDestruct (region_revoked_to_static_close_mid _ _ _ _ m with "Hr HM [Hmap]") as "HH"; auto.
    { rewrite difference_het_eq_empty dom_empty_L. intros a' Hin. set_solver. }
    { rewrite Hdom. set_solver. }
    iDestruct "HH" as (Mρ') "(? & ? & % & ?)". iFrame. iExists _. iFrame. iPureIntro. congruence. 
  Qed.

  Lemma region_revoked_to_static W (m: gmap Addr (Perm * Word)) :
    (sts_full_world sts_std (revoke W)
    ∗ region (revoke W)
    ∗ ([∗ map] a↦pv ∈ m, ∃ p v φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
    ==∗ (sts_full_world sts_std (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Static m))
      ∗ region (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Static m))))%I.
  Proof.
    iIntros "(Hfull & Hr & Hmap)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    iDestruct (region_revoked_to_static_preamble with "Hr [Hmap] HM") as "(Hr & HM & Hmap)".
    { iApply (big_sepM_mono with "Hmap"). iIntros (k x Hk) "Hr". iDestruct "Hr" as (? ? ? ? ? ?) "[? ?]".
      iExists _,_,_. iFrame. auto. }
    iAssert ([∗ map] a↦pv ∈ m, (∃ (p : Perm) (v : Word) φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
                                 ∗ sts_state_std (encode a) Revoked)%I with "[Hmap]" as "Hmap".
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Hx".
      iDestruct "Hx" as (p v φ Hpers Heq Hne) "(Ha & Hrel & Hstate)".
      iFrame. iExists _,_,_. iFrame. auto. }
    iDestruct (sts_full_world_std with "Hfull") as %Hstd.
    iAssert (⌜Forall (λ a : Addr, std_sta (revoke W) !! encode a = Some (encode Revoked)) (elements (dom (gset Addr) m))⌝%I)
      as %Hforall.
    { rewrite Forall_forall. iIntros (x Hx).
      apply elem_of_elements in Hx.
      apply elem_of_gmap_dom in Hx as [pw Hpw]. 
      iDestruct (big_sepM_delete with "Hmap") as "[[Hx Hstate] Hmap]";[apply Hpw|].
      iDestruct "Hx" as (p v φ Hpers Heq Hne) "(Hx & #Hrel)". destruct pw;inversion Heq; subst.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup. auto. 
    }
    iDestruct (monotone_revoke_list_region_def_mono with "[] Hfull Hr") as "[Hfull Hr]".
    { iPureIntro. apply related_sts_priv_world_static with (m':=m); [auto|]. apply Hforall. }
    iDestruct (big_sepM_sep with "Hmap") as "[Hmap Hstates]". 
    iMod (region_revoked_to_static_states _ _ m with "[$Hfull $Hstates]") as "[Hfull Hstates]". 
    iModIntro.
    iDestruct (region_revoked_to_static_close with "HM Hr [Hmap Hstates]") as "[HM Hr]";auto.
    { iDestruct (big_sepM_sep with "[$Hmap $Hstates]") as "Hmap".
      iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "[Hx Hstate]".
      iDestruct "Hx" as (p v φ Heq Hne) "(Ha & Hrel)". iExists _,_. iFrame. iFrame. auto.
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

End heap.
