From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
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
      rewrite -delete_insert_ne // insert_id; auto.

      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].

     (* Needed because IH disallows non-capability values *)
      destruct wsrc as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        (* Special case for E-values*)
        destruct (decide (p' = E)) as [-> | HneE].
        -
          unshelve iDestruct ("Hreg" $! r0 _ _ Hsomesrc) as "HPCv"; auto.
          iClear "Hinv".
          rewrite fixpoint_interp1_eq; simpl.

          iDestruct (big_sepM_insert _ _ PC with "[$Hmap $HPC]") as "Hmap"; [apply lookup_delete|]. rewrite insert_delete_insert; auto.
          iDestruct ("HPCv" with "[$Hmap $Hown]") as "Hcont"; auto.
        - iAssert (PC ↦ᵣ WCap p' b' e' a')%I  with "[HPC]" as "HPC".
          { destruct p'; auto. congruence. }

          iDestruct (big_sepM_insert _ _ PC with "[$Hmap $HPC]") as "Hmap"; [apply lookup_delete|]. rewrite insert_delete_insert; auto.
          iApply ("IH" $! (<[PC:=WCap p' b' e' a']> r) with "[%] [] [Hmap] [$Hown]").
          { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (ri v Hri Hvs).
            rewrite lookup_insert_ne in Hvs; auto.
            destruct (decide (ri = r0)).
            { subst ri.
              rewrite Hsomesrc in Hvs; inversion Hvs; subst; clear Hvs.
              unshelve iSpecialize ("Hreg" $! r0 _ _ Hsomesrc); eauto. }
            { repeat (rewrite lookup_insert_ne in Hvs); auto.
              iApply "Hreg"; auto. } }
          { rewrite insert_insert. iApply "Hmap". }
          iModIntro.
          unshelve iSpecialize ("Hreg" $! r0 _ _ Hsomesrc); eauto.
      }

     (* Non-capability cases *)
     all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
     all: repeat iNext; iIntros "HPC /=".
     all: iApply wp_pure_step_later; auto.
     all: iApply wp_value.
     all:   iNext; iIntros; discriminate.
  Qed.

End fundamental.
