From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ,
            logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : D.

  Lemma RX_jmp_case:
    ∀ r a g M fs fr b e p' w r0
      (* RWX case *)
      (fundamental_RWX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ M r)%I)
      (* (* RWLX case *) *)
      (fundamental_RWLX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ M r)%I)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = Jmp r0)
      (Heq : fs = M.1.1 ∧ fr = M.1.2),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
            full_map a0
         -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r0))
         -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
         -∗ Exact_w wγ a7
         -∗ sts_full a3 a4
         -∗ na_own logrel_nais ⊤
         -∗ ⌜a7.1.1 = a3⌝
         → ⌜a7.1.2 = a4⌝
         → □ (∃ p : Perm, ⌜PermFlows RX p⌝
                           ∧ ([∗ list] a8 ∈ region_addrs a5 a6, 
                              na_inv logrel_nais (logN.@a8)
                                     (∃ w0 : leibnizO Word, a8 ↦ₐ[p] w0 ∗ ▷ interp w0)))
         -∗ ⟦ [a3, a4] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ ▷ interp w0))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
        -∗ □ ▷ ▷ interp w
        -∗ Exact_w wγ M
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
              ∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais ⊤)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais ⊤
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros r a g M fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval". 
    iIntros "HM Hsts Ha Hown Hcls HPC Hmap".
    destruct Heq as [Heq1 Heq2].
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext. 
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* reestablish invariant *)
      iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto. 
      (* apply IH *)
      iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hown]"); auto.
    * specialize H3 with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r PC r0); eauto.
      iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; iFrame.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto. 
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto. 
      destruct (updatePcPerm wsrc) eqn:Heq.
      { iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct c,p,p,p.
        destruct p.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p,p,p,p; try congruence.
          + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
            simpl. rewrite /read_write_cond.
            iDestruct "Hwsrc" as (g' b' e' a') "[% H]". inv H4.
            iDestruct "H" as (p) "[% [H1 H2]]".
            iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto.
            iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hown]"); eauto.
          + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
            simpl. rewrite /enter_cond.
            iDestruct "Hwsrc" as (g' b' e' a') "[% H]". inv H4.
            rewrite /interp_expr /=.
            iDestruct "H" as "#H".
            iDestruct ("H" $! M.1 r) as "H'".
            iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto.
            iDestruct "H'" as (fs fr) "[% [% HH]]".
            iDestruct ("HH" with "[HM Hsts Hmap Hown]") as "Hx"; iFrame; eauto.
            { inv H4. destruct M. simpl.
              destruct g'; simpl.
              - iFrame. iSplitR; auto.
                destruct b0; auto.
                iDestruct (RelW_public_to_private with "HM") as "HM".
                (* Need to remove the basic update modality :( *) admit.
              - iFrame. iSplitR; auto.
                (* That part with Exact_w and possibly different locality *)
                admit. }
            iDestruct "Hx" as (px gx bx ex ax) "[% Hx]".
            inv H6; auto. (* Hmmmmm *) admit.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p,p,p,p; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq (inr _)).
          simpl. iDestruct "Hwsrc" as (g' b' e' a') "[% H]". inv H4.
          iDestruct "H" as (p) "[% [H1 H2]]".
          iDestruct (fundamental_RWX with "[H1]") as "Hind"; eauto.
          rewrite /interp_expression /=.
          instantiate (H9:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
          inv H5. iDestruct ("Hind" with "[HM Hsts Hown Hmap]") as "Hind"; iFrame; eauto.
          iDestruct "Hind" as (px gx bx ex ax) "[% H]".
          iApply "H".
        - iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p,p,p,p; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq (inr _)).
          simpl. iDestruct "Hwsrc" as (g' b' e' a') "[% H]". inv H4.
          iDestruct "H" as (p) "[% [H1 H2]]".
          iDestruct (fundamental_RWLX with "[H1]") as "Hind"; eauto.
          rewrite /interp_expression /=.
          instantiate (H9:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
          inv H5. iDestruct ("Hind" with "[HM Hsts Hown Hmap]") as "Hind"; iFrame; eauto.
          iDestruct "Hind" as (px gx bx ex ax) "[% H]".
          iApply "H". }
  Admitted. 
      
  (*    
  Lemma RWX_jmp_case:
    ∀ E0 r a g fs fr b e p' w r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = Jmp r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
                      ∧ ([∗ list] a7 ∈ region_addrs a5 a6, 
                         na_inv logrel_nais (logN.@a7)
                                (∃ w0 : leibnizO Word,
                                    a7 ↦ₐ[p] w0
                                  ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))))
           -∗ □ ⌜∀ a' : Addr, (a5 ≤ a')%Z ∧ (a' ≤ a6)%Z → ↑logN.@a' ⊆ E0⌝
           -∗ ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0)))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ stsf E1, ▷ ((interp E1) stsf) w)
        -∗ □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (E0 ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))
              ∗ na_own logrel_nais (E0 ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais E0)
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais E0
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E0 r a g fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval #Hval'".
    iIntros "Hsts Ha Hown Hcls HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext. 
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* reestablish invariant *)
      iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto. 
      (* apply IH *)
      iApply ("IH" $! _ _ _ _ _ _ _ with "[] Hreg Hmap Hsts Hown");
        [iPureIntro;eauto|
         iAlways;iExists _;iSplit;[eauto|iFrame "#"]|
         iAlways;iPureIntro;eauto].
    * specialize H3 with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r PC r0); eauto.
      iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; iFrame.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto. iNext. 
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      iMod ("Hcls" with "[Ha $Hown]") as "Hown"; auto. 
      destruct (updatePcPerm wsrc) eqn:Heq.
      { iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct c,p,p,p.
        destruct p.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hown]"); eauto; admit.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          (* use fundamental_RX in some way ? *) admit.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          (* use fundamental_RWLX in some way ? *) admit. }
  Admitted. *)

  
End fundamental.