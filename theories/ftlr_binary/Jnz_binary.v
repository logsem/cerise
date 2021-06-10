From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma Jnz_spec_determ r dst src regs regs' retv retv' :
    Jnz_spec r dst src regs retv ->
    Jnz_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
  Qed.

  Lemma jnz_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst src : RegName) (P : D):
    ftlr_instr r p b e a w w' (Jnz dst src) P.
  Proof.
    intros Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { eapply lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr; eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    (* we assert that w = w' *)
    iAssert (⌜w = w'⌝)%I as %Heqw.
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    iMod (step_Jnz _ [SeqCtx] with "[$Ha' $Hsmap $Hs $Hspec]") as (retv' regs'') "(Hs' & Hs & Ha' & Hsmap) /=";[rewrite Heqw in Hi|..];eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { solve_ndisj. }
    iDestruct "Hs'" as %HSpec'.

    specialize (Jnz_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].
    destruct Hregs as [-> | ->].
    { destruct HSpec.
      - iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w'; iFrame|iModIntro]. iNext.
        iApply wp_value; auto. iIntros; discriminate.
      - incrementPC_inv; simplify_map_eq.
        iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w',w'; iFrame|iModIntro].
        iApply wp_pure_step_later; auto. iNext.
        iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
        rewrite lookup_insert in H2; inv H2. rewrite !insert_insert.
        iApply ("IH" $! (r1,r1) with "[] [] Hmap Hsmap Hown Hs Hspec").
        { iPureIntro. simpl. intros reg. destruct Hsome with reg;auto. }
        { simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
          rewrite /RegLocate. replace (r2 !! rr) with (r1 !! rr); [iExact "Hrr"|].
          erewrite <- (lookup_insert_ne r1 PC rr); auto.
          erewrite <- (lookup_insert_ne r2 PC rr); auto.
          f_equal. eapply Heq. }
        { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
      - rewrite !insert_insert. subst w'.
        iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w,w; iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        case_eq (isCorrectPCb (updatePcPerm w'0)); intro HPCb.
        + destruct (reg_eq_dec dst PC).
          * subst dst. rewrite lookup_insert in H1; inv H1.
            replace (updatePcPerm (WCap p b e a)) with ((WCap p b e a):Word); [|destruct Hp; subst p; auto].
            iNext. iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /="; auto.
            iApply ("IH" $! (r1,r1) with "[] [] Hmap Hsmap Hown Hs Hspec").
            { iPureIntro. simpl. intros reg. destruct Hsome with reg; auto. }
            { simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
              rewrite /RegLocate. replace (r2 !! rr) with (r1 !! rr); [iExact "Hrr"|].
              erewrite <- (lookup_insert_ne r1 PC rr); auto.
              erewrite <- (lookup_insert_ne r2 PC rr); auto.
              f_equal. eapply Heq. }
            { rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
          * assert (H1' := H1). rewrite lookup_insert_ne in H1; auto.
            rewrite Heq lookup_insert_ne in H1'; auto.
            destruct w'0; simpl in HPCb; [congruence|].
            destruct (perm_eq_dec p0 E).
            { subst p0. iDestruct ("Hreg" $! dst with "[]") as "Hinvdst"; [iPureIntro; auto|].
              rewrite /RegLocate H1 H1'.
              rewrite /interp (fixpoint_interp1_eq (WCap E _ _ _, WCap _ _ _ _)) /=.
              iDestruct "Hinvdst" as (_) "Hinvdst".
              iDestruct ("Hinvdst" $! (r1, r2)) as "Hinvdst'".
              iNext. iMod (do_step_pure _ [] with "[$Hs]") as "Hs /="; auto.
              iDestruct ("Hinvdst'" with "[$Hown $Hs Hsmap $Hmap]") as "Hinvdst''".
              - iSplitR.
                + iSplit; [iPureIntro; simpl; auto|].
                  iApply "Hreg".
                + replace (<[PC:=WCap RX b0 e0 a0]> r2) with (<[PC:=WCap RX b0 e0 a0]> r1); auto.
                  unfold_leibniz. eapply map_eq. intros.
                  destruct (reg_eq_dec PC i); [subst i; rewrite !lookup_insert; auto|rewrite !lookup_insert_ne; auto].
                  assert (<[PC:=WCap p b e a]> r1 !! i = <[PC:=WCap p b e a]> r2 !! i).
                  { rewrite Heq; auto. }
                  rewrite !lookup_insert_ne in H3; auto.
              - iDestruct "Hinvdst''" as (_) "$". }
            { iDestruct ("Hreg" $! dst with "[]") as "Hinvdst"; [iPureIntro; auto|].
              rewrite /RegLocate H1 H1'.
              iNext. iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /="; auto.
              iApply ("IH" $! (r1,r2) with "[] [] [Hmap] [Hsmap] [$Hown] [$Hs] [$Hspec]"); simpl; auto.
              - destruct p0; auto. congruence.
              - replace (<[PC:=WCap p0 b0 e0 a0]> r2) with (<[PC:=WCap p0 b0 e0 a0]> r1); [destruct p0; auto; congruence|].
                unfold_leibniz. eapply map_eq. intros.
                destruct (reg_eq_dec PC i); [subst i; rewrite !lookup_insert; auto|rewrite !lookup_insert_ne; auto].
                assert (<[PC:=WCap p b e a]> r1 !! i = <[PC:=WCap p b e a]> r2 !! i).
                { rewrite Heq; auto. }
                rewrite !lookup_insert_ne in H3; auto. }
        + iNext. iMod (do_step_pure _ [] with "[$Hs]") as "Hs /="; auto.
          simpl. iApply (wp_bind (fill [SeqCtx])).
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [eapply lookup_insert|].
          iApply (wp_notCorrectPC with "HPC"); [eapply isCorrectPCb_nisCorrectPC; auto|].
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iApply wp_value; auto. iNext. iIntros; discriminate. }
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w'; iFrame|iModIntro]. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
