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

  Lemma PermPairFlows_interp_preserved p p' l l' b e a:
    PermPairFlowsTo (p', l') (p, l) = true →
    (fixpoint interp1) (inr (p, l, b, e, a)) -∗
    (fixpoint interp1) (inr (p', l', b, e, a)).
  Proof.
    intros Hp. iIntros "HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)).
    simpl in H3, H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H3; try congruence; simpl; auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iDestruct "HA" as "[HA #HB]".
      iFrame. iModIntro. rewrite /exec_cond /=.
      (* either l' = g, or l' = Local and g = Global *)
      (* provable i think but annoying *) admit.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      inv H5. iDestruct "HA" as "[HA #HB]".
      iModIntro. rewrite /exec_cond /enter_cond.
      iIntros. destruct (decide (in_range a' b' e')).
      + iSpecialize ("HB" $! a' W r i). iNext.
        rewrite /interp_expr /=. iExists _, _.
        do 2 (iSplitR; eauto). iIntros "HA".
        iExists _, _, _, _, _. iSplitR; auto.
        rewrite /interp_conf. iDestruct "HB" as (fs fr) "[% [% HB]]".
        iDestruct "HA" as "[A [B C]]".
        assert ((W_toM l' W).1.1 = fs).
        { rewrite H5. destruct l'; destruct g; reflexivity. }
        assert ((W_toM l' W).1.2 = fr).
        { rewrite H7. destruct l'; destruct g; reflexivity. }
        rewrite H8; rewrite H9. assert ({l' = g} + {l' <> g}).
        { destruct l', g; auto. } destruct H10.
        * subst l'. iDestruct ("HB" with "[A B C]") as "HC"; iFrame.
          iDestruct "HC" as (p' g' b e a) "[HC HD]". iFrame.
        * destruct l', g; simpl in H4; try congruence.
          simpl. iDestruct "C" as "[C1 [C2 C3]]".
          iMod (RelW_public_to_private with "C1") as "[C1 C1']"; eauto.
          apply (W, false). rewrite /registers_mapsto.
          iDestruct ((big_sepM_delete _ _ PC) with "B") as "[HPC Hmap]".
          rewrite lookup_insert. reflexivity.
          rewrite delete_insert_delete.
          (* need to update the PC mapsto, but don't see how to do that ? *)
          admit.
      + iNext. rewrite /interp_expr /=. iExists _, _.
        do 2 (iSplitR; eauto). iIntros "HA". iClear "HB".
        iExists _, _, _, _, _. iSplitR; auto.
        iDestruct "HA" as "[A [B C]]".
        rewrite /registers_mapsto. rewrite /interp_conf.
        iDestruct ((big_sepM_delete _ _ PC) with "B") as "[HPC Hmap]".
        rewrite lookup_insert. reflexivity.
        rewrite delete_insert_delete.
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC").
        red; intros. apply n. inv H5. apply H9.
        iNext. iIntros "HPC".
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iIntros "%". inv a.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as "#HA". iModIntro.
      rewrite /enter_cond. (* same stuff again *) admit.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA #HB]". iFrame.
      iModIntro. rewrite /exec_cond.
      iIntros. iSpecialize ("HB" $! a W r a0).
      iNext. rewrite /interp_expr /=.
      iDestruct "HB" as (fs fr) "[% [% HA]]".
      (* somewhat same thing *)
      admit.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% [HA #HB]]".
      inv H5. iModIntro. rewrite /exec_cond /enter_cond.
      iIntros. admit. (* Same as the case before *)
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iDestruct "HA" as "[HA #HB]". iFrame.
      iModIntro. (* still the same *) admit.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA HB]". auto.
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA #HB]". auto.
      iFrame. iModIntro.
      rewrite /exec_cond. iIntros. iSpecialize ("HB" $! a W r a0).
      iNext. admit. (* Same as the case before *)
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iDestruct "HA" as "[HA #HB]". iModIntro.
      rewrite /exec_cond /enter_cond.
      inv H5. iIntros. admit. (* Same as the case before *)
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[HA #HB]". iFrame.
      iModIntro. rewrite /exec_cond. iIntros. iSpecialize ("HB" $! a W r a0).
      iNext. admit. (* Same as the case before *)
    - iDestruct "HA" as (g b' e' a') "[% HA]".
      iExists l', b, e, a. iSplitR; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; inv H5; auto.
      iDestruct "HA" as "[HA #HB]".
      iFrame. iModIntro.
      (* same *) admit.
  Admitted.

  Lemma RX_Restrict_case:
    ∀ r a g M fs fr b e p' w dst (r0: Z + RegName)
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
      (Hi : cap_lang.decode w = cap_lang.Restrict dst r0)
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
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
        * case_eq (a + 1)%a; intros.
          { iApply (wp_restrict_success_z_PC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
            { iFrame. iNext. iExists _. iFrame. auto. }
            iApply wp_pure_step_later; auto.
            case_eq (decodePermPair z); intros. rewrite H6 in H4.
            destruct (andb_true_eq _ _ ltac:(symmetry in H4; exact H4)).
            simpl in H7. destruct p; simpl in H7; try congruence.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
          { iApply (wp_restrict_failPC1' with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
        * iApply (wp_restrict_failPC1 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (H3 r0) as [wr0 Hsomer0].
        destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          repeat rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
                { iFrame. iNext. iExists _. iFrame. auto. }
                iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                case_eq (decodePermPair z); intros.
                destruct (andb_true_eq _ _ ltac:(symmetry in H4; exact H4)).
                rewrite H6 in H7; simpl in H7. destruct p; simpl in H7; try congruence.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate. }
              { iApply (wp_restrict_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros.  iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_restrict_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
      rewrite lookup_delete_ne; eauto.
      destruct wdst.
      { iApply (wp_restrict_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c, p, p, p.
        - destruct r0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hdst)".
                iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                { iFrame. iNext. iExists _. iFrame. auto. }
                iApply wp_pure_step_later; auto.
                iAssert ((interp_registers (<[dst:=inr (decodePermPair z, a2, a1, a0)]> r)))%I
                  as "[Hfull' Hreg']".
                { iSplitL.
                  - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                  - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                    + subst r2. rewrite /RegLocate lookup_insert.
                      iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                      simpl. destruct (decodePermPair z). iApply (PermPairFlows_interp_preserved _ _ _ _ _ _ _ H4); auto.
                    + rewrite /RegLocate lookup_insert_ne; auto.
                      iApply "Hreg"; auto. }
                iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); auto. }
              { iApply (wp_restrict_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (H3 r0) as [wr0 Hsomer0].
            destruct (reg_eq_dec PC r0).
            * subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (reg_eq_dec dst r0).
              { subst r0. iApply (wp_restrict_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wr0.
                - case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
                  * case_eq (a + 1)%a; intros.
                    { revert H4; intro H4.
                      iApply (wp_restrict_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                      { iFrame. iNext. iExists _. iFrame. auto. }
                      iApply wp_pure_step_later; auto.
                      iAssert ((interp_registers (<[dst:=inr (decodePermPair z, a2, a1, a0)]> (<[r0:=inl z]> r))))%I
                        as "[Hfull' Hreg']".
                      { iSplitL.
                        - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                          destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                        - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                          + subst r2. rewrite /RegLocate lookup_insert.
                            iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                            simpl. destruct (decodePermPair z).
                            iApply (PermPairFlows_interp_preserved _ _ _ _ _ _ _ H4); auto.
                          + rewrite /RegLocate lookup_insert_ne; auto.
                            destruct (reg_eq_dec r0 r2).
                            * subst r2; rewrite lookup_insert. simpl.
                              repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                            * rewrite lookup_insert_ne; auto.
                              iApply "Hreg"; auto. }
                      iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); auto. }
                    { iApply (wp_restrict_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  * iApply (wp_restrict_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_restrict_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Qed.

End fundamental.