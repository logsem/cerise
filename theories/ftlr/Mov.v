From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base.

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

   (*Lemma mov_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
         (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (src: Z + RegName) :
     ftlr_instr fs fr r p p' g b e a w (Mov dst src).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
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
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
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
              iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
              iApply wp_pure_step_later; auto.
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
                iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
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
                simpl. 
                iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
                iDestruct "Hvalid" as (p'') "[% [H1 H2]]".
                iExists p''. iSplitR; auto. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hvalid".
                rewrite /RegLocate Hsomer0.
                rewrite (fixpoint_interp1_eq _ (inr _)).
                simpl. iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
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
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
          iApply wp_pure_step_later; auto.
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"). 
          (* iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"). *)
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
          { eauto. }
          { eauto. }
          { eauto. }
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
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"). 
            { iIntros (r2). iPureIntro.
              destruct (reg_eq_dec dst r2).
              - subst r2. exists (inr (p, g, b, e, a)). eapply lookup_insert.
              - destruct (Hsome r2) as [wr2 Hsomer2].
                exists wr2. rewrite -Hsomer2. rewrite lookup_insert_ne; eauto. }
            { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
              - subst r2. rewrite /RegLocate lookup_insert.
                rewrite (fixpoint_interp1_eq _ (inr (_, g, b, e, a))) /=.
                iAssert (□ exec_cond (fs, fr) b e g p (fixpoint interp1))%I as "#Hexec".
                { iAlways. 
                  rewrite /exec_cond. iIntros (a' W' r' Hin) "Hfuture".
                  iNext. rewrite /interp_expr /=. iExists _,_.
                  iSplitR; eauto. iSplitR; eauto.
                  iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                  iSplitR; eauto. destruct r'; simpl.
                  iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto. }
                destruct p; 
                  destruct Hp as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr;
                  (iExists p'; iSplitR;[auto|]; iFrame "Hbe Hexec").
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
              iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"). 
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
              iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"). 
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
      Unshelve. auto. auto. auto.
  Qed. *)

End fundamental.