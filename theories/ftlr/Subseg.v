From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export addr_reg region logrel register_tactics.
From cap_machine.rules Require Import rules_base rules_Subseg.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma within_in_range:
    forall a b b' e e',
      (b <= b')%a ->
      (e' <= e)%a ->
      in_range a b' e' ->
      in_range a b e.
  Proof.
    intros * ? ? [? ?]. split; solve_addr.
  Qed.

  Lemma subseg_case (regs : leibnizO Reg)
    (p : Perm) (b e a : Addr)
    (widc w : Word) (dst : RegName) (r1 r2 : Z + RegName) (P:D):
    ftlr_instr regs p b e a widc w (Subseg dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros
      "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right.
      destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst HnE HnIE Hao1 Hao2 Hwi HincrPC | * Hdst Hoo1 Hoo2 Hwi HincrPC | ].
    - (* Subseg_spec_success_cap *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& x & HPC & Z & Hregs') .

      assert (a'' = a ∧ p'' = p) as (-> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq ; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].

      set (widc' := if (decide (dst = idc)) then WCap p0 a1 a2 a0 else widc).
      iNext ; iIntros "_".
      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn; intros; by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        destruct (decide (ri = dst)); simplify_map_eq.
        * unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          rewrite /isWithin in Hwi.
          iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
          by rewrite PermFlowsToReflexive.
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
      {
        iModIntro.
        iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
        1,2: destruct Hp; by subst p.
        { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
          1,2: rewrite /isWithin in Hwi; solve_addr. }
        { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
          1,2: rewrite /isWithin in Hwi; solve_addr. }
        { by rewrite PermFlowsToReflexive. }
      }
      {
        subst widc'.
        iClear "Hwrite".
        case_decide as Heq ; simplify_map_eq; auto.
        iApply (interp_weakening with "IH Hinv_pc Hinv_idc"); auto; try solve_addr.
        1,2: rewrite /isWithin in Hwi; solve_addr.
        by rewrite PermFlowsToReflexive.
      }
    - (* Subseg_spec_success_sr *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .
      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ a'' = a) as (-> & -> & -> & ->).
      { simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext ; iIntros "_".

      set (widc' := if (decide (dst = idc)) then WSealRange p0 a1 a2 a0 else widc).
      iApply ("IH" $! regs' _ _ _ _ widc' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn; intros; by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        rewrite /isWithin in Hwi.
        destruct (decide (ri = dst)); simplify_map_eq.
        * unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
          by apply SealPermFlowsToReflexive.
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
      {
        iModIntro.
        iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
        1,2: destruct Hp; by subst p.
        by rewrite PermFlowsToReflexive.
      }
      { iClear "Hwrite".
        rewrite /isWithin in Hwi.
        subst widc'; case_decide as Heq; simplify_map_eq; auto.
        iApply (interp_weakening_ot with "Hinv_idc"); auto; try solve_addr.
        by apply SealPermFlowsToReflexive.
      }
      - (* Failure *)
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iNext ; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
  Qed.

End fundamental.
