From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import addr_reg region.
From cap_machine.rules Require Import rules_base rules_Subseg.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
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

  Lemma subseg_interp_preserved p b b' e e' a v :
    p <> E ->
    (b <= b')%a ->
    (e' <= e)%a ->
    (□ ▷ (∀ lregs' p' b' e' a' v',
           full_map lregs'
             -∗ (∀ (r1 : RegName) (lv : LWord),
                 ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
             -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
             -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (LCap p' b' e' a' v') -∗ interp_conf)) -∗
      (fixpoint interp1) (LCap p b e a v) -∗
      (fixpoint interp1) (LCap p b' e' a v).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    destruct p; reflexivity.
  Qed.

  Lemma subseg_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (dst : RegName) (r1 r2 : Z + RegName) (P : D):
    ftlr_instr lregs p b e a v lw (Subseg dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }


    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hao1 Hao2 Hwi HincrPC
                      | * v' oo1 oo2 Hdst Hoo1 Hoo2 Hwi HincrPC |].
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''&? & HPC & Z & Hregs') .

      assert (a'' = a ∧ p'' = p ∧ v'' = v) as (-> & -> & ->).
      { destruct (decide (PC = dst)); by simplify_map_eq. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext ; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn. intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          rewrite /isWithin in Hwi.
          iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
          by rewrite PermFlowsToReflexive. }
        { iApply "Hreg"; auto. }
      }
      { rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { destruct (reg_eq_dec PC dst) as [Heq | Hne] ; simplify_map_eq.
        1,2: rewrite /isWithin in Hwi; try solve_addr. }
      { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
        1,2: rewrite /isWithin in Hwi; try solve_addr. }
      { by rewrite PermFlowsToReflexive. }
    }
    {
      apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''& ? & HPC & Z & Hregs') .
      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto; simplify_map_eq; auto. }

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ a'' = a /\ v'' = v) as (-> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); by simplify_map_eq. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext ; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn. intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          rewrite /isWithin in Hwi.
          iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
          by rewrite SealPermFlowsToReflexive. }
        { iApply "Hreg"; auto. }
      }
      { rewrite insert_insert. iApply "Hmap". }
      iModIntro.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { by rewrite PermFlowsToReflexive. }
    }
    { iApply wp_pure_step_later; auto.
    iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
    iNext ; iIntros "_".
    iApply wp_value; auto. iIntros; discriminate. }
Qed.

End fundamental.
