From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.
From cap_machine Require Export logrel register_tactics.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved p p' b e a widc :
    p <> E ->
    p <> IE ->
    PermFlowsTo p' p = true →
    (□ ▷ (∀ a0 a1 a2 a3 a4 w',
             full_map a0
          -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r1 ≠ idc⌝ → ⌜a0 !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[idc:=w']> (<[PC:=WCap a1 a2 a3 a4]> a0))
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4)
          -∗ □ (fixpoint interp1) w'
          -∗ interp_conf)) -∗
    (fixpoint interp1) widc -∗
    (fixpoint interp1) (WCap p b e a) -∗
    (fixpoint interp1) (WCap p' b e a).
  Proof.
    intros HpnotE HpnotIE Hp. iIntros "#IH HIDC HA".
    iApply (interp_weakening with "[IH]") ; eauto ; try solve_addr.
  Qed.

  Lemma match_perm_with_E_rewrite:
    forall (A: Type) p (a1 a2: A),
      match p with
      | E => a1
      | _ => a2
      end = if (perm_eq_dec p E) then a1 else a2.
  Proof.
    intros. destruct (perm_eq_dec p E); destruct p; auto; congruence.
  Qed.

  Lemma restrict_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr r p b e a widc w (Restrict dst r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv_pc #Hinv_idc #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC HIDC Hmap".
    iInsertList "Hmap" [idc;PC].

    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto.
      right. destruct (decide (rr = idc)); subst; simplify_map_eq; auto.
    }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & ->).
      { destruct (decide (PC = dst)) ; simplify_map_eq; auto;
        [ rewrite lookup_insert in Hdst; rewrite lookup_insert in HPC |
        (rewrite lookup_insert_ne in HPC ; [rewrite lookup_insert in HPC|auto])] ; by simplify_eq.
      }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      (* TODO rewrite regs' to match with the induction hypothesis *)
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hri' Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert_ne in Hdst; auto.
          rewrite lookup_insert_ne in Hdst; auto.
          rewrite lookup_insert in Hvs; inversion Hvs. simplify_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ _ Hdst); eauto.
          iApply (interp_weakening with "IH Hreg"); auto; solve_addr. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
        auto. by rewrite PermFlowsToReflexive. }
    }
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ a'' = a) as (-> & -> & -> & ->).
      { simplify_map_eq; auto. }

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
          rewrite lookup_insert_ne in Hdst; auto.
          rewrite lookup_insert in Hvs; inversion Hvs. simplify_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; solve_addr. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
        { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. }
    }
     { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
