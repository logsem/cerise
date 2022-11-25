From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Lemma jmp_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (r0 : RegName) (i : CoreN) (P : D):
    ftlr_instr r p b e a w (Jmp r0) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    apply forall_and_distr in Hsome ; destruct Hsome as [Hsome Hnone].
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Ha HP Hcls HPC Hmap".
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
      iIntros "_".
      iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* apply IH *)
      iApply ("IH" $! i _ _ b e a with "[] [] [Hmap]"); eauto.
      { iPureIntro. intros. cbn. split ; [apply Hsome | apply Hnone]. }
      destruct Hp as [-> | ->]; iFrame.
    * specialize Hsome with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ (i, r0)) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r (i, PC) (i, r0)) ; eauto ; simplify_pair_eq.
      iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ (i, r0)) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      destruct (updatePcPerm wsrc) eqn:Heq.
      {
        iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
        iModIntro ; iNext ; iIntros "_".
        iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (WInt _) |- _ => inv H end|].
        iModIntro.
        iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value.
        iIntros. discriminate.
    }
      { destruct p0.
        1,2,3: iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|] ;
        iModIntro ; iNext ; iIntros "_".
        - iApply (wp_bind (fill [SeqCtx]) _ _ (_,_) _).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext ; iIntros "_".
          iApply wp_value.
          iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx]) _ _ (_,_) _).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext ; iIntros "_".
          iApply wp_value.
          iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx]) _ _ (_,_) _).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext ; iIntros "_".
          iApply wp_value.
          iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r (i, r0)); auto.
          iDestruct ("Hreg" $! r0 _ _ Hsomesrc) as "Hwsrc".
          destruct wsrc; simpl in Heq; try congruence.
          destruct p0; try congruence.
          + iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
            iModIntro.
            inv Heq.
            iNext ; iIntros "_".
            iApply ("IH" with "[] [] [$Hmap]"); eauto.
            iIntros (?); cbn ; iPureIntro. split ; [apply Hsome | apply Hnone].
          + inv Heq.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
            iModIntro.
            rewrite !fixpoint_interp1_eq /=. iDestruct ("H" with "[$Hmap]") as
              "Hcont"; auto.
            iNext. iSplit.
            iIntros (?); cbn ; iPureIntro. split ; [apply Hsome | apply Hnone].
            auto.
        - iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro ; iNext ; iIntros "_".
          iApply (wp_bind (fill [SeqCtx]) _ _ (_,_) _).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext; iIntros "_".
          iApply wp_value.
          iIntros. discriminate.
        - iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro.
          iNext ; iIntros "_".
          iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r (i, r0)); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 _ _ Hsomesrc) as "Hwsrc".
          iClear "Hinv".
          iApply ("IH" with "[] [] [Hmap]"); iFrame "#"; eauto.
          iIntros (?); cbn ; iPureIntro. split ; [apply Hsome | apply Hnone].
      }
      Unshelve. all: auto ; simplify_pair_eq.
  Qed.
  
End fundamental.
