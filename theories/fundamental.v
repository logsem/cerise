From cap_machine Require Export logrel monotone Jmp Jnz Get Get2 AddSubLt AddSubLt2 IsPtr Lea Load Mov Store Restrict Subseg.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Lemma extract_r_ex reg (r : RegName) :
    (∃ w, reg !! r = Some w) →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) → ∃ w, r ↦ᵣ w)%I. 
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ r i, r ↦ᵣ i)%I reg r w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma PermPairFlows_interp_preserved E fs fr p p' l l' a2 a1 a0:
    PermPairFlowsTo (p', l') (p, l) = true ->
    na_own logrel_nais E -∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a0)) ={⊤}=∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p', l', a2, a1, a0)).
  Proof.
    intros. iIntros "Hown HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in H3; exact H3)).
    simpl in H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H4; try congruence; simpl; match goal with | H: PermPairFlowsTo (O, _) (_, _) = _ |- _ => auto | _ => idtac end.
    - iDestruct "HA" as (g b e a ws) "[% [HB HC]]".
      inv H6. iExists l', b, e, a, ws. iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iExists ws. iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_only_cond b e ws (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_only_cond.
        iDestruct "Hregion" as "(Hbe & Hstsf)".
        iFrame. iIntros. iDestruct ("Hstsf" $! stsf E0) as "Hstsf".
        iDestruct (big_sepL_later with "Hstsf") as "Hstsf".
        iApply big_sepL_later. iNext.
        iDestruct (big_sepL_sepL with "Hstsf") as "[Hstsf1 Hstsf2]".
        iFrame. }
      iMod "HA" as "HA". iModIntro. iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [HB HC]]".
      inv H6. iExists RW,l',b,e,a.
      iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iExists ws. iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_only_cond b e ws (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_only_cond.
        iDestruct "Hregion" as "(Hbe & Hstsf)".
        iFrame. }
      iMod "HA" as "HA". iModIntro. iFrame. auto.
    - (* PermPairFlowsTo (RW, l') (RWL, l) = true *)
      iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists RW, l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_write_cond b e (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_write_cond.
        iExists ws. iDestruct "Hregion" as "(Hbe & Hstsf)". iFrame.
        iIntros. iDestruct ("Hstsf" $! stsf E0) as "Hstsf".
        iDestruct (big_sepL_later with "Hstsf") as "Hstsf".
        iApply big_sepL_later.
        iNext. iApply big_sepL_sepL. iSplitL "Hstsf"; auto.
        
        (* Not proveable *) admit. }
      admit.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists RWL, l', b, e, a. auto.
    - iDestruct "HA" as (p g b e a ws) "[% [% [#Hinv Hexec]]]".
      inv H6. iExists l', b, e, a, ws.
      iModIntro. iSplitR; auto.
    - iDestruct "HA" as (p g b e a ws) "[% [HA [Hinv HB]]]".
      inv H6. iExists RX,l',b,e,a,ws.
      iModIntro. iFrame.
  Admitted.
  
  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl).

  Lemma fundamental_RX stsf E r b e g (a : Addr) ws :
    (na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws interp) →
     ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e interp) →
     ⟦ inr ((RWX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWLX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e interp) →
     ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I. 
  Proof.
  { clear fundamental_RX.
    destruct stsf as [fs fr].
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hsts [Hown #Hreach]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv Hreach". iLöb as "IH" forall (r a g fs fr b e ws).
    iIntros "#Hinv %". rename a0 into Hreach. 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as %Hbe.
      { iPureIntro. by apply Hreach. }
      (* iMod ("Hinv" $! ⊤ E _ Hbe with "Hown") as "[[Hregion Hown] Hcls]".  *)
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto. 
      (* iDestruct (extract_from_region _ _ a with "Hregion") *)
      (*   as (al w ah) "(Hal & Hah & Hregionl & Hvalidl & >Ha & #Hva & Hregionh & Hvalidh)"; *)
      (*   auto. *)
(* ======= *)
      (*       iInv (logN.@(b, e)) as "Hregion" "Hcls".       *)
      rewrite /read_only_cond.
      iDestruct "Hregion" as "[Hbe #Hval]".
      iDestruct ("Hval" $! (fs,fr) E) as "Hval'".
      iCombine "Hbe Hval'" as "Hregion". 
      iDestruct (extract_from_region' _ _ a with "Hregion") as (w) "(Heqws & Hregionl & _ & >Ha & #Hva & Hh)"; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (RX_Jmp_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Jnz *)
        iApply (RX_Jnz_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Mov *)
        iApply (RX_Mov_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Load *)
        iApply (RX_Load_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Store *)
        iApply (RX_Store_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Lt *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Add *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Sub *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Lea *)
        iApply (RX_Lea_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Restrict *)
        iApply (RX_Restrict_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Subseg *)
        iApply (RX_Subseg_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* IsPtr *)
        iApply (RX_IsPtr_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetL *)
        iApply (RX_GetL_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetP *)
        iApply (RX_GetP_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetB *)
        iApply (RX_GetB_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetE *)
        iApply (RX_GetE_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetA *)
        iApply (RX_GetA_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
        { iNext.
          iDestruct (extract_from_region' _ _ a _
                     (((fixpoint interp1) E) (fs, fr)) with 
                         "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
          { iExists w. iFrame "∗ #". }
          iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }            
        iFrame.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  }
  { clear fundamental_RWX.
    destruct stsf as [fs fr].
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hsts [Hown #Hreach]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv Hreach". iLöb as "IH" forall (r a g fs fr b e).
    iIntros "#Hinv %". rename a0 into Hreach. 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RWX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as %Hbe.
      { iPureIntro. by apply Hreach. }
      (* iMod ("Hinv" $! ⊤ E _ Hbe with "Hown") as "[[Hregion Hown] Hcls]".  *)
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto. 
      (* iDestruct (extract_from_region _ _ a with "Hregion") *)
      (*   as (al w ah) "(Hal & Hah & Hregionl & Hvalidl & >Ha & #Hva & Hregionh & Hvalidh)"; *)
      (*   auto. *)
(* ======= *)
      (*       iInv (logN.@(b, e)) as "Hregion" "Hcls".       *)
      rewrite /read_write_cond.
      iDestruct "Hregion" as (ws) "[Hbe #Hval]".
      iDestruct ("Hval" $! (fs,fr) E) as "Hval'".
      iCombine "Hbe Hval'" as "Hregion".
      iAssert ((▷ ▷ (([∗ list] w ∈ ws, (((interp E) (fs, fr)) w)) ∗ ([∗ list] w ∈ ws, ⌜isLocalWord w = false⌝)))%I) as "[#Hval1 #Hval2]".
      { iNext. iNext. iApply (big_sepL_sepL with "Hval'"). }
      iDestruct (extract_from_region' _ _ a with "Hregion") as (w) "(Heqws & Hregionl & _ & >Ha & #[Hva1 Hva2] & Hh)"; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (RWX_Jmp_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Jnz *) admit.
      + (* Mov *) admit.
      + (* Load *) admit.
      + (* Store *) admit.
      + (* Lt *)
        iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Add *)
        iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Sub *)
        iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Lea *)
        iApply (RWX_Lea_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Restrict *) admit.
      + (* Subseg *) admit.
      + (* IsPtr *)
        iApply (RWX_IsPtr_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetL *) 
        iApply (RWX_GetL_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetP *)
        iApply (RWX_GetP_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetB *)
        iApply (RWX_GetB_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetE *)
        iApply (RWX_GetE_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* GetA *)
        iApply (RWX_GetA_case with "[] [] [] [] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Fail *) 
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value. 
        iNext. iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
        { iNext. iExists ws.
          iDestruct (extract_from_region' _ _ a _
                     (((fixpoint interp1) E) (fs, fr)) with 
                         "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
          { iExists w. iFrame "∗ #". }
          iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RWX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RWX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iFrame.
    - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr. }
  { admit. }
  Admitted.

  Theorem fundamental (perm : Perm) b e g (a : Addr) stsf E r :
    (⌜perm = RX⌝ ∧ ∃ ws, (na_inv logrel_nais (logN .@ (b,e))
                                 (read_only_cond b e ws interp)%I)) ∨
    (⌜perm = RWX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_cond b e interp)%I)) ∨
    (⌜perm = RWLX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_local_cond b e interp)%I)) -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ stsf E r.
  Proof. 
    iIntros "[#[-> Hinv] | [#[-> Hinv] | #[-> Hinv]]]".
    - iDestruct "Hinv" as (ws) "Hinv". by iApply fundamental_RX. 
    - by iApply fundamental_RWX. 
    - by iApply fundamental_RWLX.
  Qed.  

    
      
End fundamental. 