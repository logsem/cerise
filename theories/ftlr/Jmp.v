From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
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
        (b e a : Addr) (widc w : Word) (src : RegName) (P : D):
    ftlr_instr r p b e a widc w (Jmp src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #Hread Hown Ha HP Hcls HPC HIDC Hmap".
    iInsert "Hmap" idc.

    destruct (decide (src = PC)); simplify_map_eq.
    - iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      (* reconstruct invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|].
      iModIntro.
      iApply wp_pure_step_later; auto.
      (* reconstruct registers *)
      iNext. iIntros "_".
      iInsert "Hmap" PC.
      iApply ("IH" $! _ _ b e a with "[] [] [Hmap] [$Hown]"); eauto.
      { iPureIntro. apply Hsome. }
      destruct Hp as [-> | ->]; iFrame; by rewrite insert_commute.

    - destruct (decide (src = idc)); simplify_map_eq.
      + admit. (* TODO need the wp_rule.... *)
      + specialize Hsome with src as Hsrc.
        destruct Hsrc as [wsrc Hsomesrc].
        iExtractList "Hmap" [src;idc] as ["Hsrc";"Hidc"].
        iAssert (fixpoint interp1 wsrc) as "#Hinv_src"; first (iApply "Hreg"; eauto).
        destruct (decide (is_ie_cap wsrc = true)) as [Hie|Hie].
        * (* EI cap *)
          destruct wsrc as [ | [ [] b' e' a' | ] | ]; cbn in Hie ; try done; clear Hie.
          (* open the invariants *)
          rewrite (fixpoint_interp1_eq (WCap IE _ _ _)) //=.
          destruct (decide (withinBounds b' e' a' ∧ withinBounds b' e' (a' ^+ 1)%a)) as
            [Hdec_wb|Hdec_wb].
          {
            iDestruct ("Hinv_src" $! Hdec_wb)
              as (P1 P2) "(%Hcond_Pa1 & %Hcond_Pa2 & Hinv_a1 & Hinv_a2 & Hexec)";
              iClear "Hinv_src".
            (* TODO we can probably encode the disjunction in a better way *)
            destruct Hdec_wb as [ Hwb%Is_true_true_1 Hwb'%Is_true_true_1].
            assert (a' ≠ (a' ^+1)%a) by (rewrite withinBounds_true_iff in Hwb'; solve_addr).
            destruct (decide (a = a')) as [Haeq|Haeq];
              destruct (decide (a = (a' ^+1)%a)) as [Haeq'|Haeq'].
            ** (* a' = a , a = a ^+ 1*) solve_addr.
            ** (* a' = a , a ≠ a ^+ 1*) admit.
            ** (* a' ≠ a , a = a ^+ 1*) admit.
            ** (* a' ≠ a , a ≠ a ^+ 1*)
              iInv "Hinv_a1" as (w1) "[>Ha1 #HPa1]" "Hcls_a1".
              iInv "Hinv_a2" as (w2) "[>Ha2 #HPa2]" "Hcls_a2".

              iApply (wp_jmp_success_IE with "[$HPC $Hsrc $Hidc $Ha $Ha1 $Ha2]"); eauto.
              iNext. iIntros "(HPC & Hsrc & Hidc & Ha & Ha1 & Ha2) /=".
              iApply wp_pure_step_later; auto.

              iMod ("Hcls_a2" with "[Ha2 HPa2]") as "_";[iExists w2; iFrame; iFrame "#"|iModIntro].
              iMod ("Hcls_a1" with "[Ha1 HPa1]") as "_";[iExists w1; iFrame; iFrame "#"|iModIntro].
              iMod ("Hcls" with "[Ha HP]") as "_";[iExists w; iFrame|iModIntro].
              iNext ; iIntros "_".

              (* Needed because IH disallows non-capability values *)
              destruct w1 as [ | [p0 b0 e0 a0 | ] | ]; cycle 1.
              {
                iApply "Hexec"; iFrame "#"; iFrame.
              (* iApply ("IH" with "[] [] [Hmap] [Hown]"). *)
                iInsertList "Hmap" [idc;PC].
                iDestruct (big_sepM_insert _ _ src with "[$Hmap $Hsrc]") as "Hmap".
                rewrite lookup_insert_ne //= lookup_insert_ne //=.
                apply lookup_delete; auto.
                rewrite
                  (insert_commute _ src) //=
                    (insert_commute _ src) //=
                    insert_delete //=
                    insert_commute //=.
                iFrame.
                iIntros (r'). iPureIntro ; apply Hsome.
              }

              (* Non-capability cases *)
              all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
                iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
              all: repeat iNext; iIntros "HPC /=".
              all: iApply wp_pure_step_later; auto.
              all: iNext; iIntros "_".
              all: iApply wp_value.
              all: iIntros; discriminate.
          }
          { (* fail case *)
            admit.
          }
        * (* TODO not EI-cap, works as before *) admit.
  Admitted.

End fundamental.
