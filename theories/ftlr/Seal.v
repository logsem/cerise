From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Seal.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* Proving the meaning of sealing in the LR sane *)
  Lemma sealing_preserves_interp sb p0 b0 e0 a0:
        permit_seal p0 = true →
        withinBounds b0 e0 a0 = true →
        fixpoint interp1 (WSealable sb) -∗
        fixpoint interp1 (WSealRange p0 b0 e0 a0) -∗
        fixpoint interp1 (WSealed a0 sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsb #HVsr".
    rewrite (fixpoint_interp1_eq (WSealRange _ _ _ _)) (fixpoint_interp1_eq (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[% [HsealP HWcond]]".
    iExists P.
    repeat iSplitR; auto.
    by iApply "HWcond".
  Qed.

  Lemma seal_case (regs : leibnizO Reg)
    (p : Perm) (b e a : Addr)
    (widc w : Word) (dst r1 r2 : RegName) (P:D):
    ftlr_instr regs p b e a widc w (Seal dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hseal Hwb HincrPC | ].
    - (* Success *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (p'' = p ∧ a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }
      assert (r1 ≠ PC) as Hne.
      { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
      rewrite lookup_insert_ne in Hr1; auto.

      iAssert (fixpoint interp1 (WSealRange p0 b0 e0 a0)) as "HVsr".
      { destruct (decide (r1 = idc)) ; simplify_map_eq; auto.
        by iApply ("Hreg" $! r1).
      }

      iAssert (fixpoint interp1 (WSealable sb)) as "HVsb". {
        destruct (decide (r2 = PC)); simplify_map_eq; auto.
        destruct (decide (r2 = idc)); simplify_map_eq; auto.
        by iApply ("Hreg" $! r2).
      }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".

      set (widc' := if (decide (dst = idc)) then WSealed a0 sb else widc).
      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intro; cbn; by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        destruct (decide (ri = dst)); simplify_map_eq; auto.
        * iApply (sealing_preserves_interp with "HVsb HVsr"); auto.
        * by iApply "Hreg".
      }
      { iClear "Hwrite".
        subst widc'; case_decide as Heq; simplify_map_eq.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              !insert_insert
              (insert_commute _ idc _) //=
              !insert_insert
              ; iFrame.
        + rewrite
            !insert_insert
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
            !insert_insert ; iFrame.
      }
      { rewrite !fixpoint_interp1_eq //=; destruct Hp as [-> | ->] ;iFrame "Hinv_pc". }
      { subst widc'.
        destruct (decide (dst = idc)) ; simplify_map_eq; auto.
        iModIntro; iApply (sealing_preserves_interp with "HVsb HVsr"); auto.
      }

    - (* Failure *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
  Qed.

End fundamental.
