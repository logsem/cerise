From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Lemma jmp_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (r0 : RegName) (P : D):
    ftlr_instr r p b e a w (Jmp r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
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
        iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
        iModIntro. 
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct c,p0,p0,p0.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro. 
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro. 
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro. 
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
          destruct c,p0,p0,p0; try congruence.
          + iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
            iModIntro. 
            inv Heq.
            iNext.
            iApply ("IH" with "[] [] [$Hmap] [$Hown]"); eauto.
          + inv Heq.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
            iModIntro.
            rewrite !fixpoint_interp1_eq /=. iDestruct ("H" with "[$Hmap $Hown]") as "[_ Hcont]"; auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro.
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|].
          iModIntro.
          iNext.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          iClear "Hinv". 
          iApply ("IH" with "[] [] [Hmap] [$Hown]"); iFrame "#"; eauto.
      }
      Unshelve. all: auto.
  Qed.
  
End fundamental.
