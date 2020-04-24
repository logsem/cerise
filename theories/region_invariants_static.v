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

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- Opening and closing static regions -------------------- *)

  (* cf region_invariants_revocation?

     three main lemmas:
     - one that opens all of a static region at once
     - one that closes what was a static region and turns it into a temporary one
     - one that turns a revoked region into a static region
   *)

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

  Lemma delete_list_permutation {A B} `{Countable A, EqDecision A}
        (l1 l2: list A) (m: gmap A B):
    l1 ≡ₚ l2 →
    delete_list l1 m = delete_list l2 m.
  Proof.
    induction 1.
    { reflexivity. }
    { cbn. rewrite IHPermutation //. }
    { cbn. rewrite delete_commute //. }
    { rewrite IHPermutation1 //. }
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
    iIntros "Hr".
    destruct HMl as [? ?].
    SearchAbout "sepM" delete.
    iDestruct (big_sepM_delete _ _ l with "Hr") as "(Hl & Hr)"; eauto; [].
    iFrame. iDestruct "Hl" as (ρ' Hρ') "(? & Hst)".
    assert (ρ' = Static m) as -> by congruence.
    iDestruct "Hst" as (p' v' ?) "(? & ? & ?)".
    assert (p' = p ∧ v' = v) as (-> & ->) by (split; congruence). iFrame.
  Qed.

  Definition static_resources_aux (m m_all: gmap Addr (Perm * Word)) :=
    ([∗ map] a↦pv ∈ m, ∃ p v,
       ⌜pv = (p, v)⌝ ∗ a↦ₐ[p] v ∗ sts_state_std (encode a) (Static m_all))%I.

  Definition static_resources (m: gmap Addr (Perm * Word)) :=
    static_resources_aux m m.

  Lemma region_map_open_some_static (M: gmap Addr _) Mρ W (m m_all: gmap Addr (Perm * Word)) :
    m ⊆ m_all →
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m_all)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) Mρ W
    ∗ sts_full_world sts_std W
    ∗ static_resources_aux m m_all.
  Proof.
    pattern m. revert m. refine (map_ind _ _ _).
    - intros **. iIntros "(?&?)".
      rewrite !difference_het_empty /static_resources_aux big_sepM_empty /=.
      iFrame.
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
      iDestruct (HI with "[Hr Hsts]") as "(Hr & Hfull & Hmap)"; [by iFrame|..].
      iDestruct (region_map_delete_static _ _ _ m_all a with "Hr") as "(? & ?)".
      { rewrite dom_difference_het. rewrite Hdom. set_solver. }
      { rewrite elem_of_gmap_dom. rewrite dom_difference_het.
        assert (a ∉ dom (gset Addr) m) by (by apply not_elem_of_dom).
        set_solver. }
      { apply Hm_all. rewrite dom_insert; set_solver. }
      { eapply lookup_weaken; [| apply Hsub_all]. by rewrite lookup_insert. }
      iFrame. rewrite /static_resources_aux big_sepM_insert//. iFrame. eauto.
  Qed.

  Lemma region_map_open_all_static M Mρ W (m: gmap Addr (Perm * Word)) :
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W ∗ sts_full_world sts_std W
    ∗ static_resources m.
  Proof.
    iIntros (HH Hdom) "(Hr & Hsts)".
    iDestruct (region_map_open_some_static M Mρ W m m with "[Hr Hsts]")
      as "(Hr & Hsts & Hmap)"; auto; iFrame.
    iApply (big_sepM_mono with "Hr").
    iIntros (k γp HMk) "H". iDestruct "H" as (ρ HMρ) "(Hst & Hρ)". iExists ρ.
    rewrite difference_het_lookup_Some in HMk * => HMk. destruct HMk as [HMk Hmk].
    iSplitR. iPureIntro. by rewrite difference_het_lookup_Some; eauto.
    iFrame. destruct ρ as [ | | | m']; (try by iFrame); [].
    iDestruct "Hρ" as (p v Hm') "(? & ? & Hothers)". iDestruct "Hothers" as %Hothers.
    iExists _,_. iFrame. iPureIntro. split; eauto.
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
    iDestruct "Hρ" as (? ? ?) "(? & ? & %)". intros. iPureIntro. split; eauto.
    rewrite -elem_of_gmap_dom; eauto.
  Qed.

  Lemma region_open_static W (m: gmap Addr (Perm * Word)) (l: Addr) :
    (std_sta W) !! (encode l) = Some (encode (Static m)) →
    region W ∗ sts_full_world sts_std W -∗
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world sts_std W
    ∗ static_resources m
    ∗ ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl) "(Hr & Hsts)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(? & % & % & Hr)".
    iDestruct (region_map_has_static_addr with "[Hr Hsts]")
      as %(Hstatic & ?); eauto; [by iFrame|].
    iDestruct (region_map_open_all_static M Mρ W m with "[Hr Hsts]")
      as "(Hr & Hsts & Hmap)"; eauto; [by iFrame|].
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

  (* TODO: unify with temp_resources from region_invariants_revocation.v? *)
  Definition temporary_resources (mt: gmap Addr (gname * Perm)) W :=
    ([∗ map] a↦γp ∈ mt, ∃ γpred v p φ,
         ⌜γp = (γpred,p)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v
         ∗ (if pwl p then future_pub_mono φ v else future_priv_mono φ v)
         ∗ saved_pred_own γpred φ
         ∗ ▷ φ (W, v)
         ∗ sts_state_std (encode a) Temporary)%I.

  Lemma open_region_world_static_to_temporary l m W :
    rel_is_std W →
    Forall (λ (a:Addr), (std_sta W) !! (encode a) = Some (encode (Static m))) l →
    open_region_many l W
    -∗
    open_region_many l (std_update_multiple W l Temporary).
  Proof.
    intros. iApply open_region_many_monotone.
    { admit. }
    { eapply related_sts_pub_world_static_to_temporary; eauto. }
  Admitted.

  Lemma region_close_static_to_temporary (mt: gmap Addr (gname * Perm)) W:
    open_region_many (elements (dom (gset Addr) mt)) W
    ∗ temporary_resources mt W
    ==∗
    region W
    ∗ ⌜∀ (a:Addr), a ∈ dom (gset Addr) mt →
         (std_sta W) !! (encode a) = Some (encode Temporary)⌝.
  Admitted.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------ Allocate a Static region from a Revoked one ------------------ *)

  Lemma related_sts_priv_world_static W l (m' : gmap Addr (Perm * Word)) :
    rel_is_std W -> 
    Forall (λ a : Addr, (std_sta (revoke W)) !! (encode a) = Some (encode Revoked)) l →
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
               rewrite /revoke /std_sta /= in Hi. apply anti_revoke_lookup_Revoked in Hi as [Hrev | Htemp].
               * rewrite Hrev in Hx0. inversion Hx0; subst.
                 right with (encode Temporary).
                 { left. exists Revoked,Temporary. repeat split;auto. constructor. }
                 right with (encode (Static m'));[|left]. right. exists Temporary,(Static m'). repeat split;auto.
                 constructor. 
               * rewrite Htemp in Hx0; inversion Hx0; auto.
                 right with (encode (Static m'));[|left]. right. exists Temporary,(Static m'). repeat split;auto.
                 constructor.
           +++ rewrite lookup_insert_ne in Hr'; auto. rewrite Hsome in Hr'. rewrite Hsome in Hr.
               inversion Hr'; inversion Hr. subst. repeat split;auto.
               intros x y Hx Hy.
               rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst; left.
  Qed. 

  (* The difficulty with static regions is that if one of the addresses is in its static state, all others must be. 
     We can therefore not update them one by one (since invariants will break in the middle of the state change). 
     Instead, we need to: 
              (1) assert that the states are all curently Revoked + delete them from the region map
              (2) update the full sts for all addresses in the static region 
              (3) insert the updated states back into the region map
   *)

  (* (1) assert that the states are all curently Revoked + delete them from the region map *)
  Lemma region_revoked_to_static_preamble W M Mρ (m: gmap Addr (Perm * Word)) φ :
    region_map_def M Mρ W -∗
    ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ) -∗
    RELS M -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ RELS M
    ∗ ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) Revoked).
  Proof.
    iIntros "Hr Hmap HM".
    iInduction (m) as [|x l] "IH" using map_ind. 
    - rewrite difference_het_empty difference_het_empty /= big_sepM_empty big_sepM_empty.
      iFrame. 
    - rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct ("IH" with "Hr Hmap HM") as "(Hr & HM & Hmap)". iClear "IH".
      iDestruct "Hx" as (p v Heq Hne) "[Hx Hrel]".
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
          iDestruct "Hinv" as (γpred' v' p' φ' Heqpred Hne') "[Hinv _]"; simplify_eq. 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (γpred' v' p' φ' Heqpred Hne') "[Hinv _]"; simplify_eq. 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (p' v') "(% & % & Hinv & _)"; simplify_eq. 
          iDestruct (cap_duplicate_false with "[$Hx $Hinv]") as "Hf"; auto.
      }
      subst ρ. iClear "Hinv".
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros;by rewrite Hρ|]. 
      iFrame. iSplitL "Hr". 
      { rewrite delete_insert;[|by rewrite lookup_delete]. iFrame. }
      iApply big_sepM_insert;auto. iFrame. iExists p,v. repeat iSplit;auto.
  Qed.

  (* (2) update the full sts for all addresses in the static region *)
  (* in order to show this lemma we need to generalize the statement to all maps m', such that we can update 
     to the final step of the map in the induction *)
  Lemma region_revoked_to_static_states W (m m' : gmap Addr (Perm * Word)) :
    sts_full_world sts_std W
    ∗ ([∗ map] a↦_ ∈ m, sts_state_std (encode a) Revoked)
    ==∗ sts_full_world sts_std (std_update_multiple W (elements (dom (gset Addr) m)) (Static m'))
    ∗ ([∗ map] a↦_ ∈ m, sts_state_std (encode a) (Static m')).
  Proof. 
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind. 
    - rewrite dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=. iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH". 
      iMod (sts_update_std _ _ _ (Static m') with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      assert (elements ({[x]} ∪ dom (gset Addr) m) ≡ₚ x :: elements (dom (gset Addr) m)) as Hperm.
      { apply elements_union_singleton. intros Hcontr. apply elem_of_gmap_dom in Hcontr as [y Hy].
        rewrite H3 in Hy. inversion Hy. }
      apply std_update_multiple_permutation with (W:=W) (ρ:=Static m') in Hperm. rewrite Hperm /=.
      iDestruct (sts_full_world_std with "[] Hfull") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
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
  Lemma region_revoked_to_static_close_mid W M Mρ m m' φ :
    dom (gset Addr) m ⊆ dom (gset Addr) m' ->
    (forall a ρ, m !! a = Some ρ -> m' !! a = Some ρ) ->
    (∀ a, is_Some(m !! a) -> is_Some(M !! a)) ->
    (∀ a' : Addr, a' ∈ dom (gset Addr) (m' ∖∖ m) → ((Mρ ∖∖ m) !! a' = Some (Static m'))) ->
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) (Static m'))
    -∗ ∃ Mρ, region_map_def M Mρ W ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m' → Mρ !! a' = Some (Static m')⌝.
  Proof.
    iIntros (Hsub Hsame HmM Hmid) "Hr Hmap".
    iRevert (HmM Hmid). iInduction (m) as [|x l] "IH" using map_ind forall (M Mρ) . 
    - iIntros (HmM Hmid). rewrite difference_het_empty difference_het_empty /=. iExists Mρ. iFrame.
      repeat rewrite difference_het_empty in Hmid. auto. 
    - iIntros (HmM Hmid). rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct "Hx" as (p v Heq Hne) "(Hx & #Hrel & Hstate)".
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
        destruct ρ; iFrame. iDestruct "Hρ" as (p' v' Hg Hp') "[Ha #Hforall]".
        iExists p',v'. repeat iSplit;auto. iDestruct "Hforall" as %Hforall.
        iPureIntro. intros a' Hag. destruct (decide (x = a')).
        - subst. apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete in Hag. done.
        - rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete_ne in Hag;auto.
      }
      iDestruct ("IH" with "[] [] Hr Hmap [] []") as (Mρ') "[Hr #Hforall]".
      { rewrite dom_insert_L in Hsub. iPureIntro. set_solver. }
      { iPureIntro. intros a ρ Ha. apply Hsame. by simplify_map_eq. }
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
      iDestruct "Hforall" as %Hforall. 
      assert (is_Some (M !! x)) as [γp HMx].
      { apply HmM. rewrite lookup_insert. eauto. }
      iDestruct (big_sepM_insert _ _ x γp with "[$Hr Hx Hstate]") as "Hr";[by rewrite lookup_delete|..].
      { iExists (Static m').
        iSplitR.
        - iPureIntro. apply Hforall. rewrite dom_insert_L in Hsub. set_solver. 
        - iFrame. iExists p,v. iFrame. repeat iSplit;auto. iPureIntro. apply Hsame. subst. apply lookup_insert. 
      }
      apply insert_id in HMx. rewrite insert_delete HMx. 
      iExists Mρ'. iSplit;auto. 
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
  
  Lemma region_revoked_to_static_close W M Mρ m φ :
    RELS M
    -∗ region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ ∗ sts_state_std (encode a) (Static m))
    -∗ RELS M ∗ ∃ Mρ, region_map_def M Mρ W ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)⌝.
  Proof.
    iIntros "HM Hr Hmap".
    iDestruct (RELS_sub with "HM [Hmap]") as %Hsub.
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Ha".
      iDestruct "Ha" as (p v Heq Hne) "(_ & Hrel & _)". eauto. 
    }
    iDestruct (region_revoked_to_static_close_mid _ _ _ _ m with "Hr Hmap") as "HH"; auto.
    rewrite difference_het_eq_empty dom_empty_L. intros a' Hin. set_solver. iFrame. 
  Qed.    
  
  Lemma region_revoked_to_static φ W (m: gmap Addr (Perm * Word)) : 
    (sts_full_world sts_std (revoke W)
    ∗ region (revoke W)
    ∗ ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
    ==∗ (sts_full_world sts_std (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Static m))
      ∗ region (revoke (std_update_multiple W (elements (dom (gset Addr) m)) (Static m)))))%I.
  Proof.
    iIntros "(Hfull & Hr & Hmap)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    iDestruct (region_revoked_to_static_preamble with "Hr Hmap HM") as "(Hr & HM & Hmap)".
    iAssert ([∗ map] a↦pv ∈ m, (∃ (p : Perm) (v : Word), ⌜pv = (p, v)⌝ ∗ ⌜p ≠ O⌝ ∗ a ↦ₐ[p] v ∗ rel a p φ)
                                 ∗ sts_state_std (encode a) Revoked)%I with "[Hmap]" as "Hmap".
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Hx". iDestruct "Hx" as (p v Heq Hne) "(Ha & Hrel & Hstate)".
      iFrame. iExists _,_. iFrame. auto. }
    iDestruct (sts_full_world_std with "[] Hfull") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
    iAssert (⌜Forall (λ a : Addr, std_sta (revoke W) !! encode a = Some (encode Revoked)) (elements (dom (gset Addr) m))⌝%I)
      as %Hforall.
    { admit. }
    iDestruct (monotone_revoke_list_region_def_mono with "[] [] Hfull Hr") as "[Hfull Hr]". 
    { iPureIntro. apply related_sts_priv_world_static; [auto|]. eauto. }
    { admit. }
    Unshelve. 2: { exact m. }
    iDestruct (big_sepM_sep with "Hmap") as "[Hmap Hstates]". 
    iMod (region_revoked_to_static_states _ _ m with "[$Hfull $Hstates]") as "[Hfull Hstates]". 
    iModIntro.
    iFrame.
    iDestruct (region_revoked_to_static_close with "HM Hr [Hmap Hstates]") as "[HM Hr]". 
    { iDestruct (big_sepM_sep with "[$Hmap $Hstates]") as "Hmap".
      iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "[Hx Hstate]".
      iDestruct "Hx" as (p v Heq Hne) "(Ha & Hrel)". iExists _,_. iFrame. auto. 
    }
    iDestruct "Hr" as (Mρ') "[Hr #Hforall]". iDestruct "Hforall" as %Hforall'. 
    iExists M,Mρ'. iFrame. admit. 
  Admitted. 
    
End heap.
