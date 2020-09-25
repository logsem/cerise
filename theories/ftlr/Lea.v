From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base.
From cap_machine Require Import rules_base interp_weakening.
From cap_machine.rules Require Import rules_Lea.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma lea_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr r p b e a w (Lea dst r0) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hoffset HincrPC |].
    { apply incrementPC_Some_inv in HincrPC as (p''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ b'' = b ∧ e'' = e) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iNext.
      iApply ("IH" $! regs' with "[%] [] [Hmap] [$Hown]").
      { cbn. intros. subst regs'. by repeat (apply lookup_insert_is_Some'; right). }
      { iIntros (ri Hri). subst regs'.
        erewrite locate_ne_reg; [ | | reflexivity]; auto.
        destruct (decide (ri = dst)).
        { subst ri. unshelve iSpecialize ("Hreg" $! dst _); eauto.
          erewrite locate_eq_reg; [ | reflexivity]; auto. simplify_map_eq.
          rewrite /RegLocate Hdst. iApply interp_weakening; eauto; try solve_addr.
          destruct p0; simpl; auto. } 
        { repeat (erewrite locate_ne_reg; [ | | reflexivity]; auto).
          iApply "Hreg"; auto. } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      { iPureIntro. tauto. }
      iAlways. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iApply wp_value; auto. iNext. iIntros; discriminate. }
  Qed.

End fundamental.
