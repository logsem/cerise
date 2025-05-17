From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : CustomEnclavesMap}
  .

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved p p' b e a v :
    p <> E ->
    PermFlowsTo p' p = true →
    (□ ▷ (∀ lregs' p' b' e' a' v',
           full_map lregs'
             -∗ (∀ (r1 : RegName) (lv : LWord),
                 ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
             -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
             -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (LCap p' b' e' a' v') -∗ interp_conf)) -∗
      (fixpoint interp1) (LCap p b e a v) -∗
      (fixpoint interp1) (LCap p' b e a v).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    iApply (interp_weakening with "IH HA"); eauto; try solve_addr.
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

  Lemma restrict_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version) (lw : LWord)
    (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr lregs p b e a v lw (Restrict dst r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#HsysInv #IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hfl HincrPC | * Hdst Hz Hfl HincrPC | ].
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''& v''&? & HPC & Z & Hregs') .

      assert (a'' = a ∧ b'' = b ∧ e'' = e ∧ v'' = v) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn. intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening with "IH Hreg"); auto; solve_addr. }
        { iApply "Hreg"; auto. }
      }
      { rewrite insert_insert. iApply "Hmap". }
      iModIntro; simplify_map_eq.
      iApply (interp_weakening with "IH Hinv"); auto; try solve_addr.
      { destruct Hp; by subst p. }
      { destruct (reg_eq_dec PC dst) as [Heq | Hne]; simplify_map_eq.
        auto. by rewrite PermFlowsToReflexive. }
    }
    { apply incrementLPC_Some_inv in HincrPC as (p''&b''&e''&a''&v''&? & HPC & Z & Hregs') .

      assert (dst ≠ PC) as Hne.
      { destruct (decide (PC = dst)); last auto. simplify_map_eq; auto. }

      assert (p'' = p ∧ b'' = b ∧ e'' = e ∧ a'' = a ∧ v'' = v) as (-> & -> & -> & -> & ->).
      { simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]"); subst regs'.
      { cbn. intros. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri ? Hri Hvs).
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening_ot with "Hreg"); auto; solve_addr. }
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
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
