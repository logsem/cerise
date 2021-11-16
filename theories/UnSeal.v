From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
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

  Lemma finz_0_dist (finz_bound : Z) (f1 f2 : finz finz_bound):
    finz.dist f1 f2 = 0 → (f2 <= f1)%f.
  Proof. rewrite /finz.dist. solve_finz. Qed.
  Lemma finz_empty_seq_between:
    ∀ (finz_bound : Z) (f1 f2 : finz finz_bound),
      finz.seq_between f1 f2 = [] → (f2 <= f1)%f.
  Proof. intros *. rewrite /finz.seq_between /finz.seq.
    destruct (finz.dist f1 f2) eqn:Heq.
    by apply finz_0_dist in Heq.
    intro HFalse; inversion HFalse.
  Qed.
  Lemma finz_cons_hd (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
    a :: l = finz.seq_between a0 e0 → a = a0.
  Proof.
    intros Heql.
    rewrite /finz.seq_between /finz.seq in Heql. destruct (finz.dist a0 e0); inversion Heql; auto. Qed.
  Lemma finz_cons_tl (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
    a :: l = finz.seq_between a0 e0 → ∃ a1, (a0 + 1 = Some a1)%f ∧ l = finz.seq_between a1 e0.
  Proof.
    intros Heql.
    assert (a0 < e0)%f as Hlt. {
      rewrite /finz.seq_between /finz.seq in Heql.
      destruct (decide (a0 < e0)%f) as [Hlt | Hnlt]; first auto.
      assert (finz.dist a0 e0 = 0) as HFalse.
      {  apply finz_dist_0; solve_finz. }
      rewrite HFalse /= in Heql. by exfalso. }
    rewrite finz_seq_between_cons in Heql; auto.
    injection Heql as _ Hl.
    assert (a0 + 1 = Some (a0 ^+ 1))%f as Heq. { solve_finz. }
    eexists ; eauto.
  Qed.

  Lemma seq_between_dist_Some {z : Z} (b0 e0 a0 : finz z):
    withinBounds b0 e0 a0 = true
    → finz.seq_between b0 e0 !! finz.dist b0 a0 = Some a0.
  Proof.
    remember (finz.seq_between b0 e0) as l. revert Heql. generalize b0.
    induction l.
    - intros b1 Heql Hwb.
      symmetry in Heql; apply finz_empty_seq_between in Heql.
      rewrite /withinBounds in Hwb.
      exfalso. solve_finz.
    - intros b1 Heql Hwb.
      destruct (decide (b1 = a0)%f) as [-> | ].
      + apply finz_cons_hd in Heql as ->.
        rewrite /finz.dist. by rewrite -Zminus_diag_reverse /=.
      + assert (b1 < a0)%f as Hlt.
        {rewrite /withinBounds in Hwb. solve_finz. }
        apply finz_cons_tl in Heql as (a1' & Hp1 & Hleq).
        assert (withinBounds a1' e0 a0 = true) as Hwb'. { unfold withinBounds in *; solve_finz. }
        specialize (IHl _ Hleq Hwb') as IHl.
        rewrite lookup_cons_ne_0.
        2 : { rewrite /finz.dist. solve_finz. }
        rewrite -IHl; apply (f_equal (λ a, l !! a)).
        rewrite /finz.dist. solve_finz.
  Qed.


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
    iDestruct "HVsr" as "[_ Hss]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[HsealP HWcond]".
    iDestruct "HVsd" as (P') "[% [HsealP' HP']]".
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
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

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
      iNext.
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
      - iApply (interp_weakening with "IH HVsb"); auto; try solve_addr.
        { admit. }
        { by rewrite PermFlowsToReflexive. }
      - iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
        { destruct Hp; by subst p''. }
        { by rewrite PermFlowsToReflexive. }
    }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iApply wp_value; auto. iNext. iIntros; discriminate. }
    Qed.

End fundamental.
