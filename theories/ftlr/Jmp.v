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

  Lemma jmp_case (regs : leibnizO Reg) (p : Perm)
    (b e a : Addr) (widc w : Word) (src : RegName) (P : D):
    ftlr_instr regs p b e a widc w (Jmp src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread _] Hown Ha HP Hcls HPC Hidc Hmap".

    destruct (decide (src = PC)); simplify_map_eq.
    { iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      (* reconstruct invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|].
      iModIntro.
      iApply wp_pure_step_later; auto.
      (* reconstruct registers *)
      iNext.
      iIntros "_".
      iInsertList "Hmap" [PC;idc].
      iApply ("IH" $! _ _ b e a widc with "[] [] [Hmap] [Hown]"); eauto.
      { iPureIntro. apply Hsome. }
      destruct Hp as [-> | ->]; iFrame.
    }

    destruct (decide (src = idc)); simplify_map_eq.
    {
      iApply (wp_jmp_success with "[HPC Ha Hidc]"); eauto; first iFrame.
      iNext. iIntros "(HPC & Ha & Hidc) /=".
      (* reconstruct invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|].
      iModIntro.
      iApply wp_pure_step_later; auto.
      destruct widc as [ | [p' b' e' a' | ] | ]; cycle 1.
      {
        rewrite /updatePcPerm.
        (* Special case for E-values*)
        destruct (decide (p' = E)) as [-> | HneE].
        - iAssert (fixpoint interp1 (WCap E b' e' a')) as "Hinterp"; first iFrame "#".
          iEval (rewrite fixpoint_interp1_eq; simpl) in "Hinv_idc".
          iInsertList "Hmap" [PC;idc].

          iDestruct ("Hinv_idc" with "[$Hinterp] [$Hmap $Hown]") as "Hcont"; auto.
        - iAssert (PC ↦ᵣ WCap p' b' e' a')%I  with "[HPC]" as "HPC".
          { destruct p'; auto. congruence. }

          iNext; iIntros "_".
          iInsertList "Hmap" [PC;idc].
          iApply ("IH" $! regs p' b' e' a' (WCap p' b' e' a') with "[%] [] [Hmap] [Hown]"); eauto.
      }

      (* Non-capability cases *)
      all: iNext ; iIntros "_".
      all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value.
      all: iIntros; discriminate.
    }

    specialize Hsome with src as Hsrc.
    destruct Hsrc as [wsrc Hsomesrc].
    iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
    by simplify_map_eq.
    iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; first iFrame.
    iNext. iIntros "(HPC & Ha & Hsrc) /=".
    (* reconstruct invariant *)
    iMod ("Hcls" with "[Ha HP]") as "_";[iExists w;iFrame|].
    iModIntro.
    iApply wp_pure_step_later; auto.
    destruct wsrc as [ | [p' b' e' a' | ] | ]; cycle 1.
    {
      rewrite /updatePcPerm.
      (* Special case for E-values*)
      iDestruct ("Hreg" $! src _ n n0 Hsomesrc) as "HPCv"; auto.
      destruct (decide (p' = E)) as [-> | HneE].
      - iAssert (fixpoint interp1 (WCap E b' e' a')) as "Hinterp"; first iFrame "#".
        iEval (rewrite fixpoint_interp1_eq; simpl) in "HPCv".
        iInsertList "Hmap" [PC;idc].
        iDestruct (big_sepM_insert _ _ src with "[$Hmap $Hsrc]") as "Hmap"; first by simplify_map_eq.
        rewrite (insert_commute _ src _) //=.
        rewrite (insert_commute _ src _) //=.
        rewrite (insert_delete_insert _ src _) //=.

        iDestruct ("HPCv" with "[$Hinv_idc] [$Hmap $Hown]") as "Hcont"; auto.
        iNext.
        iSplit.
        { rewrite /full_map. iIntros (r) ; iPureIntro.
          by repeat (rewrite lookup_insert_is_Some'; right).
        }
        { iIntros (r wr Hr_pc Hr_idc Hr).
          destruct (decide (r = src)) ; simplify_map_eq.
          iFrame "#".
          iApply "Hreg"; eauto.
        }
      - iAssert (PC ↦ᵣ WCap p' b' e' a')%I  with "[HPC]" as "HPC".
        { destruct p'; auto. congruence. }

        iNext; iIntros "_".
        iInsertList "Hmap" [PC;idc].
        iDestruct (big_sepM_insert _ _ src with "[$Hmap $Hsrc]") as "Hmap"; first by simplify_map_eq.
        rewrite (insert_commute _ src _) //=.
        rewrite (insert_commute _ src _) //=.
        rewrite (insert_delete_insert _ src _) //=.
        iApply ("IH" $! (<[_ := _]> regs) p' b' e' a' widc with "[%] [] [Hmap] [Hown]"); eauto.
        { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
        {
          iIntros (ri v Hri Hri' Hvs).
          destruct (decide (ri = src)); simplify_map_eq; first done.
          iApply "Hreg"; auto.
        }
    }
    (* Non-capability cases *)
    all: iNext; iIntros "_".
    all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx]));
      iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse| ].
    all: repeat iNext; iIntros "HPC /=".
    all: iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_".
    all: iApply wp_value.
    all: iIntros; discriminate.
  Qed.

End fundamental.
