From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Lemma jmp_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (r0 : RegName) (P : D):
    ftlr_instr r p b e a w (Jmp r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame. 
      iNext. iIntros "[HPC Ha] /=". 
      (* reconstruct invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|]. 
      iModIntro. 
      iApply wp_pure_step_later; auto.
      (* reconstruct registers *)
      iNext. 
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* apply IH *)
      iApply ("IH" $! _ _ b e a with "[] [] [Hmap] [$Hown]"); eauto.
      { iPureIntro. apply Hsome. }
      destruct Hp as [-> | ->]; iFrame.
      rewrite fixpoint_interp1_eq /=. 
    * specialize Hsome with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r PC r0); eauto.
      iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto.
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
      { destruct c,p0,p0,p0. 
        destruct p0.
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
          destruct c,p0,p0,p0,p0; try congruence.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _)).
            simpl. rewrite /read_write_cond.
            (* iDestruct "Hwsrc" as (q) "[% H1]". *)
            iNext.
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[..|specialize (Hnotstatic g0)];contradiction. }
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _)).
            simpl. rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world l W W) as "Hfuture".
            { destruct l; iPureIntro.
              - destruct W. apply related_sts_priv_refl_world.
              - destruct W. apply related_sts_pub_refl_world. }
            iSpecialize ("H" $! _ _ with "Hfuture").
            iNext.
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[..|specialize (Hnotstatic g0)];contradiction. }
            iDestruct ("H" with "[$Hmap $Hr $Hsts $Hown]") as "[_ H]"; auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iNext.
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[..|specialize (Hnotstatic g0)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl.
          (* iDestruct "Hwsrc" as (p'') "[% H1]". *)
          iClear "Hinv". 
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
        - iNext.
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[..|specialize (Hnotstatic g0)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl. destruct l; auto. (* iDestruct "Hwsrc" as (p'') "[% H1]". *) iClear "Hinv". 
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
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
      }
      Unshelve. all: auto.
  Qed.
  
End fundamental.
