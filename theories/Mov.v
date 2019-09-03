From cap_machine Require Export logrel monotone.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ,
            logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : D.

  Lemma RX_Mov_case:
    ∀ E0 r a g fs fr b e p' w dst src
      (* RWX case *)
      (fundamental_RWX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = cap_lang.Mov dst src),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RX p⌝
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
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
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
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct src.
      { iApply (wp_move_fail_reg_toPC2 with "[HPC Ha]"); eauto; iFrame; auto.
        iNext. iIntros "(HPC & Ha & _)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_samePC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            (* iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with *)
            (*                "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. *)
            (* { iExists w. rewrite H4. iFrame. auto. } *)
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; auto.
          + iApply (wp_move_fail_reg_samePC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          { rewrite lookup_delete_ne; eauto. }
          destruct wr0.
          + iApply (wp_move_fail_reg_toPC2 with "[HPC Ha Hr0]"); eauto; iFrame; auto.
            simpl. iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate. 
          + destruct c, p, p, p. case_eq (a0 + 1)%a; intros.
            * iApply (wp_move_success_reg_toPC with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*              "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
              iApply wp_pure_step_later; auto.
              destruct p.
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. (* use fundamental_RWX in some way ? *) admit. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. (* use fundamental_RWLX in some way ? *) admit. }
            * iApply (wp_move_fail_reg_toPC with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      destruct src.
      { case_eq (a+1)%a; intros.
        - iApply (wp_move_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          (* iDestruct (extract_from_region' _ _ a _ ((interp E) (fs, fr)) with *)
          (*            "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. *)
          (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
          iApply wp_pure_step_later; auto.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
          { iIntros (r2). iPureIntro.
            destruct (reg_eq_dec dst r2).
            - subst r2. exists (inl z). eapply lookup_insert.
            - destruct (H3 r2) as [wr2 Hsomer2].
              exists wr2. rewrite -Hsomer2. eapply lookup_insert_ne; eauto. }
          { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
            - subst r2. rewrite /RegLocate lookup_insert.
              repeat rewrite (fixpoint_interp1_eq); simpl; eauto.
            - rewrite /RegLocate lookup_insert_ne.
              iApply "Hreg"; auto. auto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        - iApply (wp_move_fail_z with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_fromPC with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hdst)".
            (* iDestruct (extract_from_region _ _ a with *)
            (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
            (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
            { iIntros (r2). iPureIntro.
              destruct (reg_eq_dec dst r2).
              - subst r2. exists (inr (RX, g, b, e, a)). eapply lookup_insert.
              - destruct (H3 r2) as [wr2 Hsomer2].
                exists wr2. rewrite -Hsomer2. eapply lookup_insert_ne; eauto. }
            { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
              - subst r2. rewrite /RegLocate lookup_insert.
                rewrite (fixpoint_interp1_eq _ _ (inr (RX, g, b, e, a))) /=.
                iExists g,b,e,a. do 2 (iSplitR; auto).
                (* PC is in the logical relation *) admit.
              - rewrite /RegLocate lookup_insert_ne.
                iApply "Hreg"; auto. auto. }
            { eauto. }
            { eauto. }
            { eauto. }
            { eauto. }
            { eauto. }
          + iApply (wp_move_fail_reg_fromPC with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hdst)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - case_eq (a+1)%a; intros.
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_success_reg_same with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
              { iIntros (r2). iPureIntro.
              destruct (reg_eq_dec dst r2).
                - subst r2. exists (wdst). eapply lookup_insert.
                - destruct (H3 r2) as [wr2 Hsomer2].
                  exists wr2. rewrite -Hsomer2. eapply lookup_insert_ne; eauto. }
              { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
                - subst r2. rewrite /RegLocate lookup_insert.
                  iSpecialize ("Hreg" $! dst). rewrite Hsomedst.
                  iApply "Hreg"; auto.
                - rewrite /RegLocate lookup_insert_ne.
                  iApply "Hreg"; auto. auto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_success_reg with "[Hdst Hr0 HPC Ha]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
              { iIntros (r2). iPureIntro.
                destruct (reg_eq_dec dst r2).
                - subst r2. exists wr0. eapply lookup_insert.
                - destruct (reg_eq_dec r0 r2).
                  + subst r0. exists wr0. rewrite lookup_insert_ne; auto.
                    eapply lookup_insert.
                  + destruct (H3 r2) as [wr2 Hsomer2].
                    exists wr2. rewrite -Hsomer2. repeat rewrite lookup_insert_ne; eauto. }
              { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
                - subst r2. rewrite /RegLocate lookup_insert.
                  iDestruct ("Hreg" $! r0) as "Hr0".
                  rewrite Hsomer0. iApply "Hr0"; auto.
                - rewrite /RegLocate lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 r2).
                  + subst r2. rewrite lookup_insert.
                    iDestruct ("Hreg" $! r0) as "Hr0".
                    rewrite Hsomer0. iApply "Hr0"; auto.
                  + rewrite lookup_insert_ne; auto. iApply "Hreg"; auto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_fail_reg_same with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_fail_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
  Admitted.

End fundamental.  