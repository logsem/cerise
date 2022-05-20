From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsPtr.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma isptr_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst r0 : RegName) (i: CoreN) (P:D) :
    ftlr_instr r p b e a w (IsPtr dst r0) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_IsPtr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto.
      set_solver. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      iApply wp_value; auto.  }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. iNext.
      assert (dst <> PC) as HdstPC. { intros ->. simplify_map_eq. }
      simplify_map_eq.
      iApply ("IH" $! i (<[(i, dst):= _]> _) with "[%] [] [Hmap]");
        try iClear "IH"; eauto.
      { cbn; intro. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
      { iIntros (j ri v Hri Hvs).
        simplify_map_eq by simplify_pair_eq.
        (* rewrite insert_commute in Hvs ;  *)
        (*   // lookup_insert_ne // in Hvs. *)
        destruct (decide ((j, ri) = (i, dst))); simplify_map_eq by simplify_pair_eq.
        * repeat rewrite fixpoint_interp1_eq; auto.
        * repeat rewrite lookup_insert_ne in Hvs ; simplify_pair_eq.
          iApply "Hreg"; auto. all: by apply pair_neq_inv'.
      }
      simplify_map_eq by simplify_pair_eq.
      rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
  Qed.

End fundamental.
