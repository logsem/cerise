From cap_machine Require Import rules logrel. 
From iris.proofmode Require Import tactics.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Implicit Types w : (leibnizO Word).

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

  Lemma interp_monotone_list ws E E' :
          (□ ∀ a, (((fixpoint interp1) E) a
                -∗ (((fixpoint interp1) E') a)))
         -∗ ([∗ list] w ∈ ws, (((fixpoint interp1) E) w))
         -∗ ([∗ list] w ∈ ws, (((fixpoint interp1) E') w)). 
  Proof.
    iIntros "#Hmono Hws".
    iInduction ws as [_ | w ] "IH".
    - done.
    - iDestruct "Hws" as "[Hw Hws] /=".
      iSplitL "Hw".
      + iApply "Hmono". iFrame.
      + iApply "IH". iFrame.
  Qed. 

  (* Lemma read_write_cond_monotone_public s s' fr fr' a p E : *)
  (*   ⌜related_sts_pub s s' fr fr'⌝ -∗ *)
  (*    ⌜↑(logN.@a) ⊆ E⌝ -∗ *)
  (*    na_own logrel_nais E -∗ *)
  (*    read_write_cond a p (fixpoint interp1) ={⊤}=∗ *)
  (*    na_own logrel_nais E ∗ *)
  (*    read_write_cond a p (fixpoint interp1). *)
  (* Proof. *)
  (*   iIntros (Hrelated Hsub) "Hna Hrw_cond".  *)
  (*   iDestruct "Hrw_cond" as (γ) "[Hγ Hinv]". *)
  (*   iMod (na_inv_open with "Hinv Hna") as "[Hcond [Hna Hcls]]"; auto.  *)
  (*   iDestruct (bi.later_exist with "Hcond") as (w) "Hcond". *)
  (*   iDestruct (bi.later_exist with "Hcond") as (W) "(>Ha & >Hex & Hval)". *)
  (*   iDestruct (MonRef_related with "Hex Hγ") as %Hrelated'. *)
  (*   destruct W as [s'' fr''].  *)
  (*   rewrite /PrivRelW /= in Hrelated'.  *)
  (*   rewrite /read_write_cond. *)
  (*   iApply fupd_frame_r. *)
  (*   iApply bi.sep_exist_l. *)
  (*   iExists γ.  *)
  (*   iMod (MonRef_update with "Hex").  *)
  (*   iFrame "Hinv". *)
    
    
 Lemma interp_monotone_public w E E' (* E'' *) :
      (⌜E ⊆ E'⌝ -∗
      ⟦ w ⟧ E -∗ ⟦ w ⟧ E')%I. 
  Proof.
    (* destruct stsf1 as [s fr],stsf2 as [s' fr']; simpl.   *)
    iLöb as "IH" forall (w).
    iIntros (Hsub).
    iIntros "Hinterp".  
    destruct w. 
    { iDestruct (fixpoint_interp1_eq with "Hinterp") as %[z' Hinterp].   
      iApply fixpoint_interp1_eq. iSimpl. iPureIntro. eauto. }
    destruct c,p,p,p,p.
    - iApply fixpoint_interp1_eq. done. 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (H3 a' Ha').
        apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (H3 a' Ha').
        apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (H3 a' Ha').
        apply subseteq_trans with E; auto. }
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (b e a4 a5 Heq) "[% #Hv]".
      iDestruct "Hv" as (γ) "[#Hleast [Hv Hexec]]". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (H3 a' Ha').
        apply subseteq_trans with E; auto. }
      iExists γ. iFrame "#".
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a2 Heq) "#Hexec /=".
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_. iSplit;auto. 
      - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a2 Heq Hsub')
                                                          "#Hinv /=".
      iDestruct "Hinv" as (γ) "#[Hleast [Hinv Hexec]]". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_. iSplit;[auto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (Hsub' a' Ha').
        apply subseteq_trans with E;auto. }
      iExists γ. 
      iFrame "#". 
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a2 Heq Hsub')
                                                          "#Hinv /=".
      iDestruct "Hinv" as (γ) "(#Hleast & Hinv & Hexec)". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_. iSplit;[auto|].
      iSplit.
      { iPureIntro. intros a' Ha'. specialize (Hsub' a' Ha').
        apply subseteq_trans with E;auto. }
      iExists γ. iFrame "#". 
  Qed. 

  Lemma interp_reg_monotone_public r E E' :
       (⌜E ⊆ E'⌝ -∗
       ⟦ r ⟧ᵣ E -∗ ⟦ r ⟧ᵣ E')%I.
  Proof.
    iIntros (Hsub) "[$ #Hreg]".
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
         

