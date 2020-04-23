From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants region_invariants_revocation.
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
    l ↦ₐ[p] v.
  Proof.
    intros Hdom HMl HMρ Hm.
    iIntros "Hr".
    destruct HMl as [? ?].
    SearchAbout "sepM" delete.
    iDestruct (big_sepM_delete _ _ l with "Hr") as "(Hl & Hr)"; eauto; [].
    iFrame. iDestruct "Hl" as (ρ' Hρ') "(? & Hst)".
    assert (ρ' = Static m) as -> by congruence.
    iDestruct "Hst" as (p' v' ?) "(? & ? & ?)".
    assert (p' = p ∧ v' = v) as (-> & ->) by (split; congruence). eauto.
  Qed.

  Lemma region_map_open_some_static (M: gmap Addr _) Mρ W (m m_all: gmap Addr (Perm * Word)) :
    m ⊆ m_all →
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m_all)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) Mρ W
    ∗ sts_full_world sts_std W
    ∗ [∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ a ↦ₐ[p] v.
  Proof.
    pattern m. revert m. refine (map_ind _ _ _).
    - intros **. iIntros "(?&?)".
      rewrite !difference_het_empty big_sepM_empty /=.
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
      iFrame. rewrite big_sepM_insert//. iFrame. eauto.
  Qed.

  Lemma region_map_open_all_static M Mρ W (m: gmap Addr (Perm * Word)) :
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Static m)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W ∗ sts_full_world sts_std W
    -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W ∗ sts_full_world sts_std W
    ∗ [∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ a↦ₐ[p] v.
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
    ∗ ([∗ map] a↦pv ∈ m, ∃ p v, ⌜pv = (p, v)⌝ ∗ a ↦ₐ[p] v)
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
  (* ------------------ Allocate a Static region from a Revoked one ------------------ *)


  
  
  
End heap.
