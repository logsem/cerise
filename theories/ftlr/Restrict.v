From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma restrict_case (regs : leibnizO Reg) (p_pc : Perm)
    (b_pc e_pc a_pc : Addr) (widc wpc : Word) (dst : RegName) (r : Z + RegName) (P:D):
    ftlr_instr regs p_pc b_pc e_pc a_pc widc wpc (Restrict dst r) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Hpc_a HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Hpc_a Hmap]".
    destruct HSpec as [ * Hdst HnE HnIEpair HnIEpcc Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    - (* Case success regular capability *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a_pc ∧ b'' = b_pc ∧ e'' = e_pc) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
      iNext; iIntros "_".

      set (widc' := if (decide (idc = dst))
                    then WCap (decodePerm n) b e a
                    else widc).
      iApply ("IH" $! regs' _ b_pc e_pc _ widc'  with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        * unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          iApply (interp_weakening with "IH Hreg"); auto; solve_addr.
        * iApply "Hreg"; auto.
      }
      { iClear "Hwrite".
        subst widc'; case_decide as Heq; simplify_map_eq.
        + rewrite insert_insert
            (insert_commute _ idc _) //=
            !insert_insert
            (insert_commute _ idc _) //=
            insert_insert; iFrame.
        + rewrite insert_insert
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            insert_insert; iFrame.
      }
      iModIntro.
      iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
      1,2,3: destruct Hp; by subst p_pc.
      { destruct (decide (PC = dst)) as [Heq | Hne]; simplify_map_eq;auto.
        by rewrite PermFlowsToReflexive. }
      subst widc'.
      destruct (decide (idc = dst)) ; simplify_map_eq; auto.
      iApply (interp_weakening with "IH Hinv_pc Hinv_idc"); auto; try solve_addr.

    - (* SealRange case *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

      assert (p'' = p_pc ∧ a'' = a_pc ∧ b'' = b_pc ∧ e'' = e_pc) as (-> & -> & -> & ->)
      by (by simplify_map_eq).

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
      iNext; iIntros "_".

      set (widc' := if (decide (idc = dst))
                    then WSealRange (decodeSealPerms n) b e a
                    else widc).

      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        * unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; solve_addr.
        * iApply "Hreg"; auto.
      }
      { iClear "Hwrite".
        subst widc'; case_decide as Heq; simplify_map_eq.
        + rewrite insert_insert
            (insert_commute _ idc _) //=
            !insert_insert
            (insert_commute _ idc _) //=
            insert_insert; iFrame.
        + rewrite insert_insert
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            insert_insert; iFrame.
      }
      iModIntro.
      iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
      1,2,3: destruct Hp; by subst p_pc.
      { destruct (decide (PC = dst)) as [Heq | Hne']; simplify_map_eq;auto.
        by rewrite PermFlowsToReflexive. }
      simplify_map_eq.
      subst widc'.
      destruct (decide (idc = dst)) ; simplify_map_eq; auto.
      iApply (interp_weakening_ot with "Hinv_idc"); auto; try solve_addr.

    - (* Fail *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
  Qed.

End fundamental.
