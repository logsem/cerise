From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Lea.
From cap_machine.ftlr_binary Require Import interp_weakening.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma Lea_spec_determ r dst src regs regs' retv retv' :
    Lea_spec r dst src regs retv ->
    Lea_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
    - inv H6; try congruence. rewrite H0 in H5; congruence.
    - inv H6; try congruence. rewrite H0 in H5; congruence.
    - inv H0; try congruence. rewrite H1 in H2; congruence.
  Qed.

  Lemma lea_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr r p b e a w w' (Lea dst src) P.
  Proof.
    intros Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { eapply lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr; eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    (* we assert that w = w' *)
    iAssert (⌜w = w'⌝)%I as %Heqw.
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (inr (p, b, e, a)) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    iMod (step_lea _ [SeqCtx] with "[$Ha' $Hsmap $Hs $Hspec]") as (retv' regs'') "(Hs' & Hs & Ha' & Hsmap) /=";[rewrite Heqw in Hi|..];eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { solve_ndisj. }
    iDestruct "Hs" as %HSpec'.

    specialize (Lea_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w'; iFrame|iModIntro]. iNext.
      iApply wp_value; auto. iIntros; discriminate.
    - destruct Hregs as [-> |]; [| congruence].
      incrementPC_inv; simplify_map_eq.
      iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w',w'; iFrame|iModIntro].
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hs']") as "Hs' /=";auto.

      destruct (reg_eq_dec dst PC).
      + subst dst. rewrite lookup_insert in H4; inv H4.
        rewrite lookup_insert in H0; inv H0. rewrite !insert_insert.
        iApply ("IH" $! (r1,r1) with "[] [] Hmap Hsmap Hown Hs' Hspec").
        { iPureIntro. simpl. intros reg. destruct Hsome with reg;auto. }
        { simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
          rewrite /RegLocate. replace (r2 !! rr) with (r1 !! rr); [iExact "Hrr"|].
          erewrite <- (lookup_insert_ne r1 PC rr); auto.
          erewrite <- (lookup_insert_ne r2 PC rr); auto.
          f_equal. eapply Heq. }
        { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
      + rewrite lookup_insert_ne in H4; auto.
        rewrite lookup_insert in H4; inv H4.
        assert (H0':=H0). rewrite lookup_insert_ne in H0; auto.
        rewrite Heq lookup_insert_ne in H0'; auto.
        iDestruct ("Hreg" $! dst n) as "Hinvdst".
        rewrite /RegLocate H0 H0'.
        rewrite (insert_commute _ dst PC); auto.
        rewrite !insert_insert.
        iApply ("IH" $! (<[dst:=inr (p0, b0, e0, a')]> r1,<[dst:=inr (p0, b0, e0, a')]> r1) with "[] [] Hmap Hsmap Hown Hs' Hspec").
        { iPureIntro. simpl. intros reg.
          destruct (reg_eq_dec dst reg); [subst reg; rewrite lookup_insert; eauto|rewrite lookup_insert_ne;auto].
          destruct Hsome with reg;auto. }
        { iIntros. simpl. destruct (reg_eq_dec dst r0).
          - subst r0; rewrite lookup_insert. rewrite /interp.
            iApply (interp_weakening with "IH Hspec Hinvdst"); auto; try solve_addr.
            unfold Is_true. rewrite PermFlowsToReflexive. auto.
          - rewrite !lookup_insert_ne; auto.
            iDestruct ("Hreg" $! r0 H4) as "Hr0".
            replace (r2 !! r0) with (r1 !! r0); [iExact "Hr0"|].
            assert (<[PC:=inr (x, x0, x1, x2)]> r1 !! r0 = <[PC:=inr (x, x0, x1, x2)]> r2 !! r0) by (rewrite Heq; auto).
            rewrite !lookup_insert_ne in H6; auto. }
        { iModIntro. rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
  Qed.

End fundamental.


