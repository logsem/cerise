From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Export ftlr_base.
From cap_machine.rules Require Export rules_Get rules_base.

Section fundamental.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MachineParameters}.
  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma get_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst r0 : RegName) (ins: instr) (i : CoreN) (P:D) :
    is_Get ins dst r0 →
    ftlr_instr r p b e a w ins i P.
  Proof.
    intros Hinstr Hp Hsome i' Hbae Hi.
    apply forall_and_distr in Hsome ; destruct Hsome as [Hsome Hnone].
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    rewrite <- Hi in Hinstr. clear Hi.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto.
      set_solver.
    }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      iIntros "_".
      iApply wp_value; auto. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      iIntros "_".
      simplify_map_eq.
      iApply ("IH" $! i (<[(i, dst) := _]> (<[(i, PC) := _]> r)) with "[%] [] [Hmap]");
        try iClear "IH"; eauto.
      { intro. cbn.
        split.
        by repeat (rewrite lookup_insert_is_Some'; right).
        intros j Hneq. do 2 (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone.
      }
      iIntros (ri v Hri Hsv).
      rewrite insert_commute in Hsv ;[| simplify_pair_eq].
      rewrite lookup_insert_ne in Hsv ;[| simplify_pair_eq].
      destruct (decide ((i, ri) = (i,dst))); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { iApply "Hreg". done. iPureIntro. eauto. }
      by apply pair_neq_inv'; apply not_eq_sym.
      rewrite lookup_insert_ne in H1
      ;[| simplify_pair_eq] ; simplify_map_eq.
      rewrite !fixpoint_interp1_eq /=.
      destruct Hp as [-> | ->]; iFrame "Hinv". }
  Qed.

End fundamental.
