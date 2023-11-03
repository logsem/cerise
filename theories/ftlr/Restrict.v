From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.
From cap_machine Require Export logrel register_tactics.
From cap_machine Require Export stdpp_extra.

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
    destruct HSpec as [ * Hdst HnE HnIE Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    - (* Case success regular capability *)
      apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a_pc ∧ b'' = b_pc ∧ e'' = e_pc) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
      iNext; iIntros "_".

      (* TODO is there a way to destruct even later ? After applying the IH.. *)
      destruct (decide (idc = dst)) as [Hdec | Hdec].

      { (* Cases idc = dst *)
        iApply ("IH" $! regs' _ b_pc e_pc  with "[%] [] [Hmap] [$Hown]"); subst regs'.
        { intros. by repeat (apply lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hri' Hvs).
          rewrite lookup_insert_ne in Hvs; auto.
          destruct (decide (ri = idc)); simplify_map_eq.
          iApply "Hreg"; auto.
        }
        { iClear "Hwrite".
          simplify_map_eq.
          rewrite insert_insert
            (insert_commute _ idc _) //=
            !insert_insert
            (insert_commute _ idc _) //=
            insert_insert.
          iFrame.
        }
        iModIntro.
        iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
        1,2: destruct Hp; by subst p_pc.
        { destruct (reg_eq_dec PC idc) as [Heq | Hne]; simplify_map_eq;auto.
          by rewrite PermFlowsToReflexive. }
        simplify_map_eq.
        iApply (interp_weakening with "IH Hinv_pc Hinv_idc"); auto; try solve_addr.
      }
      { (* Cases idc ≠ dst *)
        iApply ("IH" $! regs' _ b_pc e_pc  with "[%] [] [Hmap] [$Hown]"); subst regs'.
        { intros. by repeat (apply lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hri' Hvs).
          rewrite lookup_insert_ne in Hvs; auto.
          destruct (decide (ri = dst)).
          { subst ri.
            rewrite lookup_insert_ne in Hdst; auto.
            rewrite lookup_insert in Hvs; inversion Hvs. simplify_map_eq.
            unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
            iApply (interp_weakening with "IH Hreg"); auto; solve_addr. }
          { repeat (rewrite lookup_insert_ne in Hvs); auto.
            iApply "Hreg"; auto. } }
        { iClear "Hwrite".
          rewrite insert_insert
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            (insert_commute _ idc _) //=
            insert_insert.
          iFrame.
        }
        iModIntro.
        iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
        1,2: destruct Hp; by subst p_pc.
        { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq; auto.
          by rewrite PermFlowsToReflexive. }
        iFrame "#".
      }


      - (* SealRange case *)
        apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

        assert (dst ≠ PC) as Hne.
        { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

        assert (p'' = p_pc ∧ a'' = a_pc ∧ b'' = b_pc ∧ e'' = e_pc) as (-> & -> & -> & ->).
        { by simplify_map_eq. }

        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
        iNext; iIntros "_".

        (* TODO is there a way to destruct even later ? After applying the IH.. *)
        destruct (decide (idc = dst)) as [Hdec | Hdec].
        { (* case idc = dst *)
          iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
          { intros. by repeat (apply lookup_insert_is_Some'; right). }
          { iIntros (ri v Hri Hri' Hvs).
            rewrite lookup_insert_ne in Hvs; auto.
            destruct (decide (ri = idc)); simplify_map_eq.
            iApply "Hreg"; auto.
          }
          { iClear "Hwrite".
            simplify_map_eq.
            rewrite
              insert_insert
                (insert_commute _ idc _) //=
                !insert_insert
                (insert_commute _ idc _) //=
                insert_insert.
            iFrame.
          }
          iModIntro.
          iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
          1,2: destruct Hp; by subst p_pc.
          { destruct (reg_eq_dec PC idc) as [Heq | Hne']; simplify_map_eq.
            by rewrite PermFlowsToReflexive. }
          simplify_map_eq.
          iApply (interp_weakening_ot with "Hinv_idc"); auto; try solve_addr.
        }

        { (* case idc ≠ dst *)
         iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
          { intros. by repeat (apply lookup_insert_is_Some'; right). }
          { iIntros (ri v Hri Hri' Hvs).
            rewrite lookup_insert_ne in Hvs; auto.
            destruct (decide (ri = dst)).
            { subst ri.
              rewrite lookup_insert_ne in Hdst; auto.
              rewrite lookup_insert in Hvs; inversion Hvs. simplify_map_eq.
              unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
              iApply (interp_weakening_ot with "Hreg"); auto; solve_addr. }
            { repeat (rewrite lookup_insert_ne in Hvs); auto.
              iApply "Hreg"; auto. } }
          { iClear "Hwrite".
            rewrite insert_insert
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
              (insert_commute _ idc _) //=
              insert_insert.
            simplify_map_eq.
            iFrame.
          }
          iModIntro.
          iApply (interp_weakening with "IH Hinv_pc"); auto; try solve_addr.
          1,2: destruct Hp; by subst p_pc.
          { destruct (reg_eq_dec PC dst) as [Heq | Hne']; simplify_map_eq.
            by rewrite PermFlowsToReflexive. }
          iFrame "#".
      }


      - (* Fail *)
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Hpc_a]");[iExists wpc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
  Qed.

End fundamental.
