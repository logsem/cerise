From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_UnSeal.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result. *)
  Lemma unsealing_preserves_interp sb p0 b0 e0 a0:
        permit_unseal p0 = true →
        withinBounds b0 e0 a0 = true →
        fixpoint interp1 (WSealed a0 sb) -∗
        fixpoint interp1 (WSealRange p0 b0 e0 a0) -∗
        ▷ fixpoint interp1 (WSealable sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsd #HVsr".
    rewrite (fixpoint_interp1_eq (WSealRange _ _ _ _)) (fixpoint_interp1_eq (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[_ [Hss Hjmp]]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[HsealP HWcond]".
    (* destruct (decide (a0 = otype_sentry)) as [?|Hot] ; subst. *)
    iDestruct "HVsd" as (P') "[% [HsealP' [HP' Hjmp']]]".
    iDestruct (seal_pred_agree with "HsealP HsealP'") as "Hequiv". iSpecialize ("Hequiv" $! (WSealable sb)).
    iAssert (▷ P (WSealable sb))%I as "HP". { iNext. by iRewrite "Hequiv". }
    by iApply "HWcond".
  Qed.

  Lemma unseal_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst r1 r2 : RegName) (P:D):
    ftlr_instr r p b e a w (UnSeal dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_UnSeal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hunseal Hwb HincrPC | ].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (r1 ≠ PC) as Hne1.
      { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
      rewrite lookup_insert_ne in Hr1; auto.
      assert (r2 ≠ PC) as Hne2.
      { destruct (decide (PC = r2)); last auto. simplify_map_eq; auto. }
      rewrite lookup_insert_ne in Hr2; auto.

      unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
      unshelve iDestruct ("Hreg" $! r2 _ _ Hr2) as "HVsd"; eauto.
      (* Generate interp instance before step, so we get rid of the later *)
      iDestruct (unsealing_preserves_interp with "HVsd HVsr") as "HVsb"; auto.

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".

      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert in Hvs; inversion Hvs. auto. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
      - iApply (interp_weakening with "IH HVsb"); auto; try solve_addr. (* HNoError used here *)
        { by rewrite PermFlowsToReflexive. }
      - iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
        { by rewrite PermFlowsToReflexive. }
    }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext ; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    Qed.

End fundamental.
