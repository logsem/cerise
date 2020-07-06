From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

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

  Lemma region_state_U_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_U W a -> region_state_U W' a.
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [Hstate | [Hstate | [w Hstate] ] ];eauto. 
    }
    destruct Hstate as [Hstate|[Hstate|[w Hstate] ] ].
    - specialize (Hrelated _ Temporary y Hstate Hy).
      destruct (decide (y = Temporary)); subst; auto.
      apply std_rel_pub_rtc_Temporary in Hrelated; auto. contradiction. 
    - specialize (Hrelated _ Permanent y Hstate Hy).
      apply std_rel_pub_rtc_Permanent in Hrelated; auto. subst y; auto.
    - specialize (Hrelated _ (Static {[a:=w]}) y Hstate Hy).
      eapply std_rel_pub_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; eauto.
  Qed.

  Lemma region_state_U_pwl_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_U_pwl W a -> region_state_U_pwl W' a.
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [? | [? ?] ]; eauto. }
    destruct Hstate as [Hstate|[? Hstate] ].
    - specialize (Hrelated _ Temporary y Hstate Hy).
      destruct (decide (y = Temporary)); subst; left; auto.
      apply std_rel_pub_rtc_Temporary in Hrelated; auto. contradiction. 
    - specialize (Hrelated _ (Static {[a:=x]}) y Hstate Hy).
      eapply std_rel_pub_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; [left | right]; eauto.
  Qed.

  (* The following lemma is not required for monotonicity, but is interesting for use in examples *)
  Lemma region_state_U_pwl_monotone_same W W' a w :
    related_sts_pub_world W W' →
    (std W) !! a = Some (Static {[a:=w]}) -> (std W') !! a = Some Temporary ∨ (std W') !! a = Some (Static {[a:=w]}).
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ (Static {[a:=w]}) y Hstate Hy).
    eapply std_rel_pub_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; [left | right]; eauto.
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
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto. 
    - destruct l; auto. 
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_pwl_monotone with W;auto. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
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
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - destruct l; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#". 
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. apply region_state_pwl_monotone with W;auto.
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst]".
        iExists _. iSplit;eauto. iFrame "#". 
        iDestruct "Hst" as %Hst. 
        iPureIntro. eapply (region_state_nwl_monotone W W' _ Global); auto. 
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd. 
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Local); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst. 
          iPureIntro. 
          eapply region_state_U_monotone; eauto.
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel. 
        iPureIntro. apply region_state_pwl_monotone with W;auto. }        
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel. 
        iPureIntro. apply region_state_U_pwl_monotone with W;auto. }
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst. 
        iPureIntro. eapply (region_state_nwl_monotone W W' _ Global); auto. 
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd. 
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Local); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst. 
          iPureIntro. 
          eapply region_state_U_monotone; eauto.
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel. 
        iPureIntro. apply region_state_pwl_monotone with W;auto. }        
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel. 
        iPureIntro. apply region_state_U_pwl_monotone with W;auto. }
  Qed.

  Lemma interp_monotone_nl W W' w :
    (⌜related_sts_priv_world W W'⌝ → ⌜isLocalWord w = false⌝ →
    interp W w -∗ interp W' w)%I. 
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto. 
    - destruct l; auto. discriminate. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
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
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel. 
      iPureIntro. destruct l; try discriminate. 
      apply region_state_nwl_monotone_nl with W;auto.
    - destruct l; try discriminate. done.
    - destruct l; simpl in Hnl; try discriminate.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hst" as %Hst. 
      iPureIntro.
      apply region_state_nwl_monotone_nl with W; auto.
    - destruct l; auto. discriminate.
    - destruct l; simpl in Hnl; try discriminate.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hst" as %Hst. 
      iPureIntro. 
      apply region_state_nwl_monotone_nl with W; auto.
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
      * by iPureIntro. 
  Qed.

  (* The validity of regions are monotone wrt private/public future worlds *)
  Lemma adv_monotone W W' b e :
    related_sts_priv_world W W' →
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W !! a = Some Permanent⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W' !! a = Some Permanent⌝))%I.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply (big_sepL_mono with "Hr").
    iIntros (k y Hsome) "(Hy & Hperm)". 
    iFrame.
    iDestruct "Hperm" as %Hperm.
    iPureIntro. 
    apply (region_state_nwl_monotone_nl _ W') in Hperm; auto.
  Qed.

  Lemma adv_stack_monotone W W' b e :
    related_sts_pub_world W W' ->
    (([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                     ∧ ⌜region_state_pwl W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                       ∧ ⌜region_state_pwl W' a⌝))%I.
  Proof.
    iIntros (Hrelated) "Hstack_adv". 
    iApply (big_sepL_mono with "Hstack_adv").
    iIntros (k y Hsome) "(Hr & Htemp)".
    iDestruct "Htemp" as %Htemp. 
    iFrame. iPureIntro. 
    apply (region_state_pwl_monotone _ W') in Htemp; auto.
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
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      rewrite Hstd in Ha. inversion Ha.
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
  - trivial.
  - auto.
Qed.



End monotone.
