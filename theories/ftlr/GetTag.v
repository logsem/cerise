From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_GetTag.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma get_tag_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst r0 : RegName) (P:D) :
    ftlr_instr r p b e a w (GetTag dst r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_GetTag with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext; iIntros "_".
      assert (dst <> PC) as HdstPC. { intros ->. simplify_map_eq. }
      simplify_map_eq.
      iApply ("IH" $! (<[dst:= _]> _) with "[%] [] [Hmap] [$Hown]");
        try iClear "IH"; eauto.
      { cbn; intro. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
      { iIntros (ri v Hri Hvs).
        rewrite insert_commute // lookup_insert_ne // in Hvs.
        destruct (decide (ri = dst)); simplify_map_eq.
        * repeat rewrite fixpoint_interp1_eq; auto.
        * by iApply "Hreg". }
      rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
  Qed.

End fundamental.
