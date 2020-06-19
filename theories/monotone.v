From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.
  
  Lemma region_state_nwl_monotone W W' a l :
    related_sts_pub_world W W' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl /std. 
    intros Hrelated Hstate.
    destruct l.
    - destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
      specialize (Hrelated a Permanent y Hstate Hy).
      apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto. 
    - destruct Hrelated as [ [Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. }
      destruct Hstate as [HTemp | HPerm].
      + left. 
        specialize (Hrelated _ Temporary y HTemp Hy).
        apply std_rel_pub_rtc_Temporary in Hrelated; subst;auto. 
      + right.
        specialize (Hrelated _ Permanent y HPerm Hy).
        apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto. 
  Qed.

  Lemma region_state_nwl_monotone_nl W W' a :
    related_sts_priv_world W W' →
    region_state_nwl W a Global -> region_state_nwl W' a Global.
  Proof.
    rewrite /region_state_nwl /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _].
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Permanent y Hstate Hy).
    apply std_rel_rtc_Permanent in Hrelated; subst; auto. 
  Qed.

  Lemma region_state_pwl_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_pwl W a -> region_state_pwl W' a.
  Proof.
    rewrite /region_state_pwl /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Temporary y Hstate Hy).
    apply std_rel_pub_rtc_Temporary in Hrelated; subst; auto. 
  Qed.

  Lemma region_state_Revoked_monotone (W W' : WORLD) (a : Addr) :
    related_sts_pub_world W W' →
    (std W) !! a = Some Revoked ->
    (std W') !! a = Some Revoked ∨
    (std W') !! a = Some Temporary.
  Proof.
    rewrite /region_state_pwl /std. 
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Revoked y Hstate Hy).
    apply std_rel_pub_rtc_Revoked in Hrelated; auto.
    destruct Hrelated as [Htemp | Hrev]; subst; auto. 
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
      iIntros (n y Hsome) "#[Hrw Hrel]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto. 
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw Hrel]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto. 
    - destruct l; auto. 
      iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw Hrel]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_pwl_monotone with W;auto. 
    - iDestruct "Hw" as (p Hfl) "Hbe".
      iExists _. iSplitR;[eauto|].
      iApply (big_sepL_mono with "Hbe").
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto. 
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
    - iDestruct "Hw" as (p Hfl) "Hbe".
      iExists p. iSplit;[auto|].
      iApply (big_sepL_mono with "Hbe").
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - destruct l;auto. 
      iDestruct "Hw" as (p Hfl) "Hbe".
      iExists p. iSplit;[auto|].
      iApply (big_sepL_mono with "Hbe").
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_pwl_monotone with W;auto.
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
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto. 
    - iDestruct "Hw" as (p Hfl) "Hw".
      iExists _; iSplit;eauto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto. 
    - destruct l; auto. discriminate. 
    - iDestruct "Hw" as (p Hfl) "Hbe".
      iExists _. iSplitR;[eauto|].
      iApply (big_sepL_mono with "Hbe").
      iIntros (n y Hsome) "#[Hrw Hrel]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nl with W;auto.
    - iAlways. iIntros (r W'').
      destruct l; simpl; try discriminate.
      iIntros (Hrelated').
      iAssert (future_world Global W W'')%I as "Hrelated".
      { iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
      iSpecialize ("Hw" $! r W'' with "Hrelated").
      iFrame.
    - iDestruct "Hw" as (p Hfl) "Hbe".
      iExists p. iSplit;[auto|].
      iApply (big_sepL_mono with "Hbe").
      iIntros (n y Hsome) "#[Hrw Hrel ]". iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto.
    - destruct l; try discriminate. done. 
  Qed.

  (*Lemma that allows switching between the two different formulations of monotonicity, to alleviate the effects of inconsistencies*)
  Lemma switch_monotonicity_formulation ρ w p φ:
      ρ ≠ Revoked → (∀ m, ρ ≠ Static m) ->
      monotonicity_guarantees_region ρ w p φ ≡ monotonicity_guarantees_decide (Σ := Σ) ρ w p φ.
  Proof.
    intros Hrev Hsta. unfold monotonicity_guarantees_region, monotonicity_guarantees_decide.
    iSplit; iIntros "HH".
    - destruct ρ.
      * simpl. destruct (pwl p) ; intros.
        destruct (decide (Temporary = Temporary ∧ true = true)). auto. assert (Temporary = Temporary ∧ true = true); auto. by congruence.
        destruct (decide (Temporary = Temporary ∧ false = true)). destruct a; by exfalso. auto.
      *  destruct (decide (Permanent = Temporary ∧ pwl p = true)). destruct a; by exfalso. auto.
      * by intros.
      * specialize (Hsta g). done. 
    - intros. destruct ρ.
      * destruct (pwl p).
        destruct (decide (Temporary = Temporary ∧ true = true)). auto.
        assert (Temporary = Temporary ∧ true = true); auto. by congruence.
        destruct (decide (Temporary = Temporary ∧ false = true)). destruct a; by exfalso. auto.
      *  destruct (decide (Permanent = Temporary ∧ pwl p = true)). destruct a; by exfalso. auto.
      * by iPureIntro.
      * specialize (Hsta g); done. 
  Qed.


Global Instance interp_ne n :
  Proper (dist n ==> dist n) (λ Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
Proof.
  solve_proper.
Qed.

(*The general monotonicity statement that interp gives you when writing a word into a pointer (p0, l, a2, a1, a0) ; simply a bundling of all individual monotonicity statements*)
Lemma interp_monotone_generalW (W : WORLD)  (ρ : region_type) (p p0 p1 : Perm) (l g : Locality)(b e a a2 a1 a0 : Addr):
  std W !! a0 = Some ρ →
  withinBounds (p0, l, a2, a1, a0) = true →
  PermFlows p0 p1 →
  (negb (isLocal g) || match p0 with
                       | RWL | RWLX => true
                       | _ => false
                       end = true)→
  ((fixpoint interp1) W) (inr (p0, l, a2, a1, a0)) -∗
  monotonicity_guarantees_region ρ  (inr (p, g, b, e, a)) p1  (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl' Hconds) "#Hvdst".
  destruct ρ.
  - destruct (pwl p1) eqn: HpwlP1 ; iAlways; simpl.
    * iIntros (W0 W1) "% HIW0".
        by iApply interp_monotone.
    * iIntros (W0 W1) "% HIW0".
      destruct g.
    + by iApply interp_monotone_nl.
    (*The below case is a contradiction, since if g is local,p0 must be WL and p0 flows into the non-WL p1*)
    + destruct p0 ; try (simpl in Hconds; by exfalso).
      all:destruct p1 eqn:Hp1v ; (by exfalso).
  - iAlways. simpl. iIntros (W0 W1) "% HIW0".
    destruct g.
    + by iApply interp_monotone_nl.
    + (*Trick here: value relation leads to a contradiction if p0 is WL, since then its region cannot be permanent*)
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as "%"; eauto.
      rewrite Hstd in H. inversion H.
  - auto.
  - auto. 
Qed.

(* Analogous, but now we have the general monotonicity statement in case an integer z is written *)
Lemma interp_monotone_generalZ (W : WORLD)  (ρ : region_type) (p0 p1 : Perm) (l : Locality)(a2 a1 a0 : Addr) z:
  std W !! a0 = Some ρ →
  withinBounds (p0, l, a2, a1, a0) = true →
  PermFlows p0 p1 →
  ((fixpoint interp1) W) (inr (p0, l, a2, a1, a0)) -∗
  monotonicity_guarantees_region ρ  (inl z) p1  (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst".
  destruct ρ.
  - destruct (pwl p1) eqn: HpwlP1 ; iAlways; simpl.
    * iIntros (W0 W1) "% HIW0".
        by iApply interp_monotone.
    * iIntros (W0 W1) "% HIW0".
        by iApply interp_monotone_nl.
  - iAlways. simpl. iIntros (W0 W1) "% HIW0".
      by iApply interp_monotone_nl.
  - auto.
  - auto. 
Qed.


End monotone.
