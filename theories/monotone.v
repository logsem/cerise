From cap_machine Require Import rules logrel. 
From iris.proofmode Require Import tactics.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Implicit Types w : (leibnizC Word).
  Notation STS := (prodC (leibnizC STS_states) (prodC (leibnizC STS_rels)
                                                      (leibnizC STS_rels))).
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
    (⌜related_sts stsf1.1 stsf2.1 stsf1.2.1 stsf2.2.1⌝ -∗
      ⌜E ⊆ E'⌝ -∗
      (* ⌜∀ ns, get_namespace w = Some ns → ↑ns ⊆ E''⌝ -∗ *)
      (* na_own logrel_nais E'' -∗ *)
      ⟦ w ⟧ E stsf1 -∗ ⟦ w ⟧ E' stsf2)%I. 
  Proof.
    iIntros (Hrelated).
    destruct stsf1 as [s [fr_pub fr_priv] ],stsf2 as [s' [fr_pub' fr_priv'] ]; simpl.  
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
      (* read_condition monotone wrt public future world *)
      iFrame "#". 
      (* rewrite /read_only_cond /=. *)
      (* iIntros (stsf'' E'' Hrelated' Hsub').  *)
      (* iSpecialize ("Hv" $! stsf'' E'').  *)
      (* destruct stsf'' as [s'' [fr_pub'' fr_priv''] ]; simpl in *.   *)
      (* assert (related_sts s s'' fr_pub fr_pub'') as Hrelated''. *)
      (* { apply related_sts_trans with s' fr_pub'; auto. } *)
      (* iApply "Hv"; auto. *)
      (* iPureIntro. apply subseteq_trans with E'; auto.     *)
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      (* read_condition monotone wrt public future world *)
      iFrame "#". 
      (* iIntros (stsf'' E'' Hrelated' Hsub').  *)
      (* iSpecialize ("Hv" $! stsf'' E'').  *)
      (* destruct stsf'' as [s'' [fr_pub'' fr_priv''] ]; simpl in *.   *)
      (* assert (related_sts s s'' fr_pub fr_pub'') as Hrelated''. *)
      (* { apply related_sts_trans with s' fr_pub'; auto. } *)
      (* iApply "Hv"; auto. *)
      (* iPureIntro. apply subseteq_trans with E'; auto.     *)
    - iDestruct (fixpoint_interp1_eq with "Hinterp") as (g b e a4 ws Heq) "[% #Hv] /=". 
      inversion Heq; subst.
      iApply fixpoint_interp1_eq.
      iExists _,_,_,_,ws.
      iSplit; [eauto|].
      iSplit.
      { iPureIntro. apply subseteq_trans with E; auto. }
      (* read_condition monotone wrt public future world *)
      iFrame "#". 
      (* iIntros (stsf'' E'' Hrelated' Hsub').  *)
      (* iSpecialize ("Hv" $! stsf'' E'').  *)
      (* destruct stsf'' as [s'' [fr_pub'' fr_priv''] ]; simpl in *.   *)
      (* assert (related_sts s s'' fr_pub fr_pub'') as Hrelated''. *)
      (* { apply related_sts_trans with s' fr_pub'; auto. } *)
      (* iApply "Hv"; auto. *)
      (* iPureIntro. apply subseteq_trans with E'; auto. *)
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
        iPureIntro.
        destruct stsf'' as [s'' [fr_pub'' fr_priv''] ]; simpl in *.  
        admit.
      + rewrite /exec_cond /=. 
        iSpecialize ("Hexec" $! E'' r a stsf'' Ha). 
        iApply "Hexec".
        iDestruct "Hrelated" as %Hrelated''.
        iPureIntro.
        destruct stsf'' as [s'' [fr_pub'' fr_priv''] ]; simpl in *.  
        apply related_sts_trans with s' fr_pub'; auto.           
    - admit.
    - admit.
    - admit.
  Admitted. 


  
   Lemma interp_expr_monotone_public w r stsf1 E stsf2 E' :
     (⌜related_sts stsf1.1 stsf2.1 stsf1.2.1 stsf2.2.1⌝ -∗
       ⌜E ⊆ E'⌝ -∗
      (* ⌜∀ ns, get_namespace w = Some ns → ↑ns ⊆ E''⌝ -∗ *)
      (* na_own logrel_nais E'' -∗ *)
      ⟦ w ⟧ₑ stsf1 E r -∗ ⟦ w ⟧ₑ stsf2 E' r)%I. 
   Proof.
     destruct stsf1 as [fs [fr_pub fr_priv] ].
     destruct stsf2 as [fs' [fr_pub' fr_priv'] ].
     iIntros "#Hrelated % He /=".
     iDestruct "He" as (fs0 fr_pub0 fr_priv0) "(<- & <- & <- & Hexpr)". 
     iExists fs',fr_pub',fr_priv'.
     do 3 (iSplit; [auto|]). 
     rewrite /interp_conf.
     Admitted. 
                        
End monotone. 
         

