From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Lea.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.
  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma lea_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r0 : Z + RegName) (i: CoreN)(P:D):
    ftlr_instr r p b e a w (Lea dst r0) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. set_solver. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hoffset HincrPC |].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ b'' = b ∧ e'' = e) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq by simplify_pair_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iNext.
      iApply ("IH" $! _ regs' with "[%] [] [Hmap]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (j ri v Hri Hvs).
        subst regs'.
        rewrite lookup_insert_ne in Hvs; auto.
        destruct (decide ((j, ri) = (i, dst))).
        { simplify_pair_eq.
          rewrite lookup_insert_ne in Hdst; simplify_pair_eq ; auto.
          rewrite lookup_insert in Hvs; inversion Hvs. simplify_eq.
          unshelve iSpecialize ("Hreg" $! i dst _ _ Hdst); eauto.
          iApply interp_weakening; eauto; try solve_addr.
          destruct p0; simpl; auto.
          by apply pair_neq_inv'; apply not_eq_sym.
        }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iApply wp_value; auto. }
  Qed.

End fundamental.
