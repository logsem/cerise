From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  
  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as (((p & b) & e) & a).

  Lemma jnz_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (r1 r2 : RegName) (P : D):
    ftlr_instr r p b e a w (Jnz r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq. rewrite insert_insert.
      iApply wp_pure_step_later; auto. iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. iNext.
      iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto. iModIntro.
      rewrite !fixpoint_interp1_eq /=.
      destruct Hp as [-> | ->];iFrame "Hinv". }
    { simplify_map_eq. iApply wp_pure_step_later; auto.
      rewrite !insert_insert.
      destruct (updatePcPerm w') as [n0|c0] eqn:Hw.
      { iApply (wp_bind (fill [SeqCtx])).
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct_cap c0. destruct (PermFlowsTo RX p0) eqn:Hpft.
        { destruct w'; simpl in Hw; try discriminate.
          destruct_cap c. assert (Heq: (if perm_eq_dec p0 p1 then True else p0 = RX /\ p1 = E) /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) by (destruct (perm_eq_dec p0 p1); destruct p1; inv Hw; simpl in Hpft; try congruence; auto; repeat split; auto).
          clear Hw. destruct (perm_eq_dec p0 p1); [subst p1; destruct Heq as (_ & -> & -> & ->)| destruct Heq as ((-> & ->) & -> & -> & ->)].
          { iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. 
            iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
            - destruct (reg_eq_dec r1 PC).
              + subst r1. simplify_map_eq. auto.
              + simplify_map_eq.
                iDestruct ("Hreg" $! r1 n) as "Hr1".
                rewrite /RegLocate H1. rewrite !fixpoint_interp1_eq.
                destruct p0; simpl in *; try discriminate; eauto. }
          { assert (r1 <> PC) as HPCnr1.
            { intro; subst r1; simplify_map_eq. naive_solver. }
            simplify_map_eq. iDestruct ("Hreg" $! r1 HPCnr1) as "Hr1".
            rewrite /RegLocate H1. rewrite !fixpoint_interp1_eq /=.
            iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro]. 
            rewrite /interp_expr /=.
            iDestruct "Hr1" as "#H".
            iNext. iDestruct ("H" with "[$Hmap $Hown]") as "Hcont"; auto. } }
        iApply (wp_bind (fill [SeqCtx])).
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
        iApply (wp_notCorrectPC with "HPC").
        - intros HH. inv HH. naive_solver.
        - iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. } }
  Qed.

End fundamental.
