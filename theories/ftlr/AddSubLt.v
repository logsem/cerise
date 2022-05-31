From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_AddSubLt.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import machine_base.
From cap_machine.ftlr Require Export ftlr_base.
From cap_machine.rules Require Import rules_base.

Section fundamental.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma add_sub_lt_case (r : leibnizO Reg) (p : Perm)
    (b e a : Addr) (w : Word) (dst : RegName) (r1 r2: Z + RegName)
    (ins : instr) (i: CoreN) (P : D):
    is_AddSubLt ins dst r1 r2 ->
    ftlr_instr r p b e a w ins i P.
  Proof.
    intros Hinstrs Hp Hsome i' Hbae Hi.
    apply forall_and_distr in Hsome ; destruct Hsome as [Hsome Hnone].
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto.
      set_solver. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
      iNext.
      iApply wp_value; auto. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iApply ("IH" $! i (<[(i, dst):=_]> (<[(i, PC):=_]> r)) with "[%] [] [Hmap]");
        try iClear "IH"; eauto.
      { intro. cbn.
        split.
        repeat (rewrite lookup_insert_is_Some'; right).
        apply Hsome.
        intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone.
      }
      iIntros (ri v Hri Hsv).
      simplify_map_eq by simplify_pair_eq.
      destruct (decide ((i, ri) = (i, dst))); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { (* rewrite lookup_insert_ne in Hsv ; simplify_pair_eq. *)
        by iApply "Hreg". }
      { iModIntro.
        simplify_map_eq by simplify_pair_eq.
        rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
    }
  Qed.

End fundamental.
