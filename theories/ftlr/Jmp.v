From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
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

  (*
  Lemma jmp_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
        (g : Locality) (b e a : Addr) (w : Word) (r0 : RegName) :
    ftlr_instr fs fr r p p' g b e a w (Jmp r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap". 
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame. 
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext. 
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* close region *)
      iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
      (* apply IH *)
      iApply ("IH" $! _ _ _ _ g _ _ a
                       with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); eauto; iFrame "#".
      { iPureIntro. apply Hsome. }
      destruct p; iFrame. 
      destruct Hp as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. 
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
            iDestruct "Hwsrc" as (q) "[% [H1 H2]]".
            iNext.
            (* close region *)
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            (* apply IH *)
            iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _)).
            simpl. rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world l (fs,fr) (fs,fr)) as "Hfuture".
            { destruct l; iPureIntro;
                [apply related_sts_priv_refl|apply related_sts_pub_refl]. }
            iSpecialize ("H" $! _ (fs,fr) with "Hfuture").
            iNext. 
            iDestruct "H" as (fs' fr' Heq1 Heq2) "HH". inversion Heq1. inversion Heq2.
            subst.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
            iDestruct ("HH" with "[Hr Hfull Hmap Hna]") as "Hx"; iFrame; eauto.
            iDestruct "Hx" as "[_ Hx] /=". auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl. 
          iDestruct "Hwsrc" as (p'') "[% [H1 H2]]".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
        - iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          rewrite (fixpoint_interp1_eq _ (inr _)).
          simpl. iDestruct "Hwsrc" as (p'') "[% [H1 H2]]".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
          Unshelve. auto. auto. auto.
      }
  Qed.*)
  
End fundamental.