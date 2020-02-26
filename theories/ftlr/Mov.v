From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine.rules Require Import rules_Mov.

(* TODO: Move into logrel.v *)
Instance future_world_persistent (Σ: gFunctors) g W W': Persistent (@future_world Σ g W W').
Proof.
  unfold future_world. destruct g; apply bi.pure_persistent.
Qed.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma mov_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName):
    ftlr_instr W r p p' g b e a w (Mov dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct src.
      { iApply (wp_move_fail_reg_toPC2 with "[$HPC $Ha]"); eauto.
        iNext. iIntros "(HPC & Ha & _)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_samePC with "[$HPC $Ha]"); eauto.
            iNext. iIntros "(HPC & Ha)".
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iApply wp_pure_step_later; auto.
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            iApply ("IH" with "[%] [$Hreg] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          + iApply (wp_move_fail_reg_samePC with "[$HPC $Ha]"); eauto. 
            iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          { rewrite lookup_delete_ne; eauto. }
          destruct wr0.
          + iApply (wp_move_fail_reg_toPC2 with "[$HPC $Ha Hr0]"); eauto.
            simpl. iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate. 
          + destruct c, p0, p0, p0. case_eq (a0 + 1)%a; intros.
            * iApply (wp_move_success_reg_toPC with "[$HPC $Ha $Hr0]"); eauto.
              iNext. iIntros "(HPC & Ha & Hr0)".
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iApply wp_pure_step_later; auto.
              iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
              destruct p0.
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
                iApply ("IH" with "[%] [$Hreg] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                iNext. iModIntro.
                iDestruct ("Hreg" $! r0 ltac:(auto)) as "HH".
                rewrite /RegLocate Hsomer0.
                repeat (rewrite fixpoint_interp1_eq). simpl.
                rewrite /read_write_cond. iDestruct "HH" as (p'') "[% [H2 H3]]".
                iExists p''. iSplitR; auto. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hvalid".
                rewrite /RegLocate Hsomer0.
                rewrite (fixpoint_interp1_eq _ (inr _)).
                simpl. iApply ("IH" with "[%] [$Hreg] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                iDestruct "Hvalid" as (p'') "[% [H1 H2]]".
                iExists p''. iSplitR; auto. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hvalid".
                rewrite /RegLocate Hsomer0.
                rewrite (fixpoint_interp1_eq _ (inr _)).
                simpl. iApply ("IH" with "[%] [$Hreg] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                destruct l; auto. destruct l; auto.
                iDestruct "Hvalid" as (p'') "[% [H1 H2]]".
                iExists p''. iSplitR; auto. }
            * iApply (wp_move_fail_reg_toPC with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
    * destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      destruct src.
      { case_eq (a+1)%a; intros.
        - iApply (wp_move_success_z with "[$HPC $Ha $Hdst]"); eauto.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iApply wp_pure_step_later; auto.
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          iNext. iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          { iIntros (r2). iPureIntro.
            destruct (reg_eq_dec dst r2).
            - subst r2. exists (inl z). eapply lookup_insert.
            - destruct (Hsome r2) as [wr2 Hsomer2].
              exists wr2. rewrite -Hsomer2. rewrite lookup_insert_ne; eauto. }
          { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
            - subst r2. rewrite /RegLocate lookup_insert.
              repeat rewrite (fixpoint_interp1_eq); simpl; eauto.
            - rewrite /RegLocate lookup_insert_ne.
              iApply "Hreg"; auto. auto. }
        - iApply (wp_move_fail_z with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_fromPC with "[$HPC $Ha $Hdst]"); eauto.
            iNext. iIntros "(HPC & Ha & Hdst)".
            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iApply wp_pure_step_later; auto.
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]").
            { iIntros (r2). iPureIntro.
              destruct (reg_eq_dec dst r2).
              - subst r2. exists (inr (p, g, b, e, a)). eapply lookup_insert.
              - destruct (Hsome r2) as [wr2 Hsomer2].
                exists wr2. rewrite -Hsomer2. rewrite lookup_insert_ne; eauto. }
            { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
              - subst r2. rewrite /RegLocate lookup_insert.
                rewrite (fixpoint_interp1_eq _ (inr (_, g, b, e, a))) /=.
                iAssert (□ exec_cond W b e g p (fixpoint interp1))%I as "#Hexec".
                { iAlways.
                  rewrite /exec_cond. iIntros (a' r' W' Hin) "#Hfuture".
                  iNext. rewrite /interp_expr /=.
                  iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                  iSplitR; eauto.
                  iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                  iAlways. iExists p'. iSplitR; auto.
                  unfold future_world; destruct g; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                  - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                    iPureIntro; split.
                    + assert (pwl p = false) by (destruct p; destruct Hp as [Hp | [Hp | [Hp Hcontr] ] ]; try congruence; auto).
                      rewrite H7 in H5. rewrite H7.
                      eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H5). auto.
                    + eapply related_sts_rel_std; eauto.
                  - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                    iPureIntro; split.
                    + destruct (pwl p).
                      * eapply region_state_pwl_monotone; eauto.
                      * eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H5); eauto.
                    + eapply rel_is_std_i_monotone; eauto.
                }
                destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p; try subst g;
                  (iExists p'; iSplitR;[auto|]; iFrame "Hinv Hexec").
              - rewrite /RegLocate lookup_insert_ne.
                iApply "Hreg"; auto. auto. }
            iFrame. auto. auto.
          + iApply (wp_move_fail_reg_fromPC with "[$HPC $Ha $Hdst]"); eauto.
            iNext. iIntros "(HPC & Ha & Hdst)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - case_eq (a+1)%a; intros.
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_success_reg_same with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iApply wp_pure_step_later; auto.
              iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]").
              { iIntros (r2). iPureIntro.
                destruct (reg_eq_dec dst r2).
                - subst r2. exists (wdst). eapply lookup_insert.
                - destruct (Hsome r2) as [wr2 Hsomer2].
                  exists wr2. rewrite -Hsomer2. rewrite lookup_insert_ne; eauto. }
              { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
                - subst r2. rewrite /RegLocate lookup_insert.
                  iSpecialize ("Hreg" $! dst). rewrite Hsomedst.
                  iApply "Hreg"; auto.
                - rewrite /RegLocate lookup_insert_ne.
                  iApply "Hreg"; auto. auto. }
              { eauto. }
              { eauto. }
            * destruct (Hsome r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_success_reg with "[$Hdst $Hr0 $HPC $Ha]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iApply wp_pure_step_later; auto.
              iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]").
              { iIntros (r2). iPureIntro.
                destruct (reg_eq_dec dst r2).
                - subst r2. exists wr0. eapply lookup_insert.
                - destruct (reg_eq_dec r0 r2).
                  + subst r0. exists wr0. rewrite lookup_insert_ne; auto.
                    eapply lookup_insert.
                  + destruct (Hsome r2) as [wr2 Hsomer2].
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
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_fail_reg_same with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate.
            * destruct (Hsome r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_fail_reg with "[$HPC $Ha $Hdst $Hr0]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
      Unshelve. auto. auto. auto. auto. auto.
  Qed.

End fundamental.
