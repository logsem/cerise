From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Seal.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  (* Proving the meaning of sealing in the LR sane *)
  Lemma sealing_preserves_interp sb p0 b0 e0 a0:
        permit_seal p0 = true →
        withinBounds b0 e0 a0 = true →
        fixpoint interp1 (LWSealable sb) -∗
        fixpoint interp1 (LSealRange p0 b0 e0 a0) -∗
        fixpoint interp1 (LWSealed a0 sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsb #HVsr".
    rewrite (fixpoint_interp1_eq (LSealRange _ _ _ _)) (fixpoint_interp1_eq (LWSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[% [HsealP HWcond]]".
    iExists P.
    repeat iSplitR; auto.
    by iApply "HWcond".
  Qed.

  Lemma seal_case (lregs : LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst r1 r2: RegName) (P : D):
    ftlr_instr lregs p b e a v lw (Seal dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hseal Hwb HincrPC | ].
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs') .

      assert (p'' = p ∧ a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); subst.
        rewrite lookup_insert in HPC; simplify_eq; auto.
        rewrite lookup_insert_ne // lookup_insert in HPC; simplify_eq; auto.
      }
      assert (r1 ≠ PC) as Hne.
      { destruct (decide (PC = r1)); last auto; subst.
        rewrite lookup_insert in Hr1; simplify_eq; auto. }
      rewrite lookup_insert_ne in Hr1; auto.
      iAssert (fixpoint interp1 (LWSealable sb)) as "HVsb". {
        destruct (decide (r2 = PC)) eqn:Heq.
        - subst r2. rewrite lookup_insert in Hr2; simplify_eq; auto.
        - simplify_map_eq.
          rewrite lookup_insert_ne in Hr2;auto;simplify_eq.
          unshelve iSpecialize ("Hreg" $! r2 _ _ Hr2); eauto.
      }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert in Hvs; inversion Hvs. simplify_eq.
          (* Sealrange is valid -> validity implies P *)
          unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
          iApply (sealing_preserves_interp with "HVsb HVsr"); auto. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      replace x with v; cycle -1.
      {
        destruct (decide (dst = PC)); subst.
        + (* dst = PC *)
          rewrite lookup_insert in HPC; simplify_eq.
        + (* dst <> PC *)
          rewrite lookup_insert_ne // lookup_insert in HPC; simplify_eq.
          done.
      }
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. }
    }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
