From cap_machine Require Import rules logrel. 
From iris.proofmode Require Import tactics.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Implicit Types w : (leibnizC Word).
  Notation STS := (prodC (leibnizC STS_states) (leibnizC STS_rels)).
  Implicit Types stsf : (STS).

  Lemma subseteq_trans (E1 E2 E3 : coPset) :
     E1 ⊆ E2 → E2 ⊆ E3 → E1 ⊆ E3.
   Proof.
     intros He1 He2.
     apply elem_of_subseteq. intros x Hx.
     assert (∀ x, x ∈ E1 → x ∈ E2) as He1'; first by rewrite -elem_of_subseteq.
     assert (∀ x, x ∈ E2 → x ∈ E3) as He2'; first by rewrite -elem_of_subseteq.
     specialize He1' with x.
     specialize He2' with x. 
     apply He2'. apply He1'. done.
   Qed. 

  (* 
     Value relation is monotone wrt public future world.
   *)

   Lemma na_abstract_inv_implies_2 {A : Type} {B : Type} (P : iProp Σ) (Q : A → B → iProp Σ) N p (a1 a2 : A) (b1 b2 : B) `{!∀ x y, Persistent (Q x y)} :
     □ (Q a1 b1 -∗ Q a2 b2) -∗
       na_abstract_inv p N (P ∗ Q a1 b1) -∗
       na_abstract_inv p N (P ∗ Q a2 b2). 
  Proof.
    iIntros "#HQimpl #Hinv".
    iAlways. iIntros (E F HsubE HsubF) "Hna". 
    iMod ("Hinv" $! E F HsubE HsubF with "Hna") as "[[[HP #HQ] Hna] Hcls]".
    iModIntro. iSplitL "HQ HP Hna".
    - iFrame. iNext. iApply "HQimpl". iFrame "#".
    - iIntros "[[HP HQb] Hna]". iApply "Hcls". iFrame. iFrame "#".  
  Qed.

  Lemma interp_monotone_list ws E E' stsf stsf' :
          (□ ∀ a, (((fixpoint interp1) E) stsf a
                -∗ (((fixpoint interp1) E') stsf' a)))
         -∗ ([∗ list] w ∈ ws, (((fixpoint interp1) E) stsf w))
         -∗ ([∗ list] w ∈ ws, (((fixpoint interp1) E') stsf' w)). 
  Proof.
    iIntros "#Hmono Hws".
    iInduction ws as [_ | w ] "IH".
    - done.
    - iDestruct "Hws" as "[Hw Hws] /=".
      iSplitL "Hw".
      + iApply "Hmono". iFrame.
      + iApply "IH". iFrame.
  Qed. 
     
 Lemma interp_monotone_public w stsf1 E stsf2 E' (* E'' *) :
    (⌜related_sts_pub stsf1.1 stsf2.1 stsf1.2 stsf2.2⌝ -∗
      ⌜E ⊆ E'⌝ -∗
      ⟦ w ⟧ E stsf1 -∗ ⟦ w ⟧ E' stsf2)%I. 
  Proof.
    iIntros (Hrelated).
    destruct stsf1 as [s fr],stsf2 as [s' fr']; simpl.  
    iLöb as "IH" forall (w).
    iIntros (Hsub).
    iIntros "Hinterp".  
    destruct w. 
    { iDestruct (fixpoint_interp1_eq with "Hinterp") as %[z' Hinterp].   
      iApply fixpoint_interp1_eq. iSimpl. iPureIntro. eauto. }
    destruct c,p,p,p,p.
    - iApply fixpoint_interp1_eq. done. 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 a5 ws Heq) "[% #[Hv Hexec]] /=".
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      iFrame "#". 
      iIntros (E'' r).
      iAlways.
      iIntros (a stsf'' Ha) "Hrelated".
      rewrite /related_sts_l. destruct b.
      + rewrite /exec_cond /=. 
        iSpecialize ("Hexec" $! E'' r a stsf'' Ha).
        iApply "Hexec".
        iDestruct "Hrelated" as %Hrelated''.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        iPureIntro.
        apply related_sts_pub_priv_trans with s' fr'; auto. 
      + rewrite /exec_cond /=. 
        iSpecialize ("Hexec" $! E'' r a stsf'' Ha). 
        iApply "Hexec".
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        apply related_sts_pub_trans with s' fr'; auto.           
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (p g b e a2 Heq) "#Hexec /=".
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,_. iSplit;[auto|].
      iIntros (E0 r). iAlways.
      iIntros (stsf'').
      rewrite /related_sts_l. destruct g.
      + iIntros (Hrelated'').
        iApply "Hexec". 
        iPureIntro.
        destruct stsf'' as [s'' fr'']. 
        simpl in *.
        apply related_sts_pub_priv_trans with s' fr'; auto. 
      + iIntros (Hrelated'').
        iApply "Hexec". 
        iPureIntro.
        destruct stsf'' as [s'' fr'']. 
        simpl in *.
        apply related_sts_pub_trans with s' fr'; auto. 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (p g b e a2 Heq Hsub')
                                                          "#(Hinv & Hexec) /=".
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,_. iSplit;[auto|]. iFrame "#".
      iSplit.
      { iPureIntro. apply subseteq_trans with E;auto. }
      iIntros (E0 r). iAlways.
      iIntros (a stsf'' Ha) "Hrelated".
      rewrite /related_sts_l. destruct g.
      + rewrite /exec_cond /=. 
        iApply "Hexec"; auto.
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        apply related_sts_pub_priv_trans with s' fr'; auto. 
      + iApply "Hexec"; auto.
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        apply related_sts_pub_trans with s' fr'; auto. 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (p g b e a2 Heq Hsub')
                                                          "#(Hinv & Hexec) /=".
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,_. iSplit;[auto|]. iFrame "#".
      iSplit.
      { iPureIntro. apply subseteq_trans with E;auto. }
      iIntros (E0 r). iAlways.
      iIntros (a stsf'' Ha) "Hrelated".
      rewrite /related_sts_l. destruct g.
      + rewrite /exec_cond /=. 
        iApply "Hexec"; auto.
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        apply related_sts_pub_priv_trans with s' fr'; auto. 
      + iApply "Hexec"; auto.
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' fr'']; simpl in *.  
        apply related_sts_pub_trans with s' fr'; auto. 
  Qed. 

  Lemma interp_reg_monotone_public r stsf1 E stsf2 E' :
     (⌜related_sts_pub stsf1.1 stsf2.1 stsf1.2 stsf2.2⌝ -∗
       ⌜E ⊆ E'⌝ -∗
       ⟦ r ⟧ᵣ E stsf1 -∗ ⟦ r ⟧ᵣ E' stsf2)%I.
  Proof.
    iIntros (Hrelated Hsub) "[$ #Hreg]".
    iIntros (r0 Hnpc).
    iSpecialize ("Hreg" $! r0 Hnpc).
    iApply interp_monotone_public; eauto. 
  Qed.

  Lemma interp_conf_weak_public w stsf1 E stsf2 E' :
    (⌜related_sts_pub stsf1.1 stsf2.1 stsf1.2 stsf2.2⌝ -∗
      ⌜E ⊆ E'⌝ -∗
      (∃ (p : Perm) (g : Locality) (b e a0 : Addr),
          ⌜w = inr (p, g, b, e, a0)⌝ ∧ ⟦ [stsf2.1, stsf2.2, E'] ⟧ₒ) -∗
     ∃ (p : Perm) (g : Locality) (b e a0 : Addr),
       ⌜w = inr (p, g, b, e, a0)⌝ ∧ ⟦ [stsf1.1, stsf1.2, E] ⟧ₒ)%I.
  Proof.
    iIntros (Hrelated Hsub) "Hconf".
    iDestruct "Hconf" as (p g b e a Heq) "Hconf".
    destruct stsf1 as [s fr],stsf2 as [s' fr']; simpl in *.
    destruct w; inversion Heq.
    iExists _,_,_,_,_. iSplit; [eauto|].
    rewrite /interp_conf.
    iApply (wp_wand_r with "[Hconf]"). iFrame. 
    iIntros (v) "Hφ".
    iIntros (Hv).
    iSpecialize ("Hφ" $! Hv).
    iDestruct "Hφ" as (r fs'' fr'') "(Hr & Hrv & Hrelated & Hna & Hsts)". 
    iExists _,_,_. iFrame. 
    iDestruct "Hrelated" as %Hrelated'.
    iSplit.
    - iPureIntro.
      apply related_sts_pub_priv_trans with s' fr'; auto. 
    - apply subseteq_disjoint_union_L in Hsub as [Z [HeqZ Hdisj] ].
      rewrite HeqZ. 
      iDestruct (na_own_union with "Hna") as "[HnaE HnaZ]"; auto. 
  Qed.     
                        
End monotone. 
         

