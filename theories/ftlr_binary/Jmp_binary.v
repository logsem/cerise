From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma jmp_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (P : D):
    ftlr_instr r p b e a w w' (Jmp dst) P.
  Proof.
    intros Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "Hsmap") as "[HsPC Hsmap] /="; [rewrite lookup_insert; reflexivity|].

    destruct (reg_eq_dec PC dst); [subst dst|].
    { iApply (rules_Jmp.wp_jmp_successPC with "[$Ha $HPC]"); eauto.
      iIntros "!>". iDestruct 1 as "[HPC Ha]".

      iAssert (⌜w = w'⌝)%I as %Heqw.
      { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
      destruct r as [r1 r2]. simpl in *.
      iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

      iMod (wp_jmp_successPC _ [SeqCtx] with "[$Ha' $HsPC $Hs]") as "(Hs & HsPC & Ha') /=";[rewrite Heqw in Hi|..];eauto.
      { solve_ndisj. }

      iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w,w'; iFrame|iModIntro].
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hs]") as "Hs /=";auto.
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      iApply ("IH" $! (r1, r2) with "[] [] [Hmap] [Hsmap] [$Hown] [$Hs] [$Hspec]").
      { iPureIntro. intros; simpl; auto. }
      { simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
        iFrame "#". }
      { simpl. instantiate (4 := match p with E => RX | _ => p end).
        destruct p; eauto. }
      { simpl. rewrite Heq insert_insert. destruct p; eauto. }
      { destruct p; auto.
        inv HisCorrect. destruct H5; congruence. } }

    { destruct (Hsome dst) as ((wdst1 & Hdst1) & wdst2 & Hdst2).
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap] /=".
      { rewrite lookup_delete_ne; eauto. }
      iApply (wp_jmp_success with "[$Ha $HPC $Hdst]"); eauto.
      iIntros "!>". iDestruct 1 as "(HPC & Ha & Hdst)".

      iAssert (⌜w = w'⌝)%I as %Heqw.
      { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
      destruct r as [r1 r2]. simpl in *.
      iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.
      subst w'.
      assert (wdst1 = wdst2) as <-.
      { assert (HA: <[PC:=WCap p b e a]> r1 !! dst = Some wdst1) by (rewrite lookup_insert_ne; auto).
        rewrite Heq lookup_insert_ne in HA; auto.
        rewrite Hdst2 in HA. inversion HA; auto. }

      iDestruct ((big_sepM_delete _ _ dst) with "Hsmap") as "[Hsdst Hsmap] /=".
      { rewrite lookup_delete_ne; eauto.
        rewrite lookup_insert_ne; eauto. }
      iMod (step_jmp_success _ [SeqCtx] with "[$Ha' $HsPC $Hs $Hsdst]") as "(Hs & HsPC & Ha' & Hsdst) /="; eauto.
      { solve_ndisj. }

      iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w,w; iFrame|iModIntro].
      iApply wp_pure_step_later; auto.
      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      iDestruct ((big_sepM_delete _ _ dst) with "[Hsdst Hsmap]") as "Hsmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite (insert_commute _ dst PC); auto.
      rewrite insert_insert.
      iDestruct ("Hreg" $! dst ltac:(auto)) as "Hinvdst"; auto.
      rewrite /RegLocate Hdst1 Hdst2.

      case_eq (isCorrectPCb (updatePcPerm wdst1)); intro HPCb.
      - destruct wdst1; simpl in HPCb; [congruence|].
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

        destruct (perm_eq_dec p0 E).
        + subst p0. rewrite /interp (fixpoint_interp1_eq (WCap E _ _ _, WCap _ _ _ _)) /=.
          iDestruct "Hinvdst" as (_) "Hinvdst".
          iDestruct ("Hinvdst" $! (<[dst:=_]>r1, <[dst:=_]>r2)) as "Hinvdst'".
          iNext. iMod (do_step_pure _ [] with "[$Hs]") as "Hs /="; auto.
          iDestruct ("Hinvdst'" with "[$Hown $Hs Hsmap $Hmap]") as "Hinvdst''".
          * simpl. iSplit.
            { iSplit.
              - iPureIntro. simpl; intros.
                destruct (reg_eq_dec dst x); [subst x; rewrite !lookup_insert; split; eauto| rewrite !lookup_insert_ne; eauto].
              - simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
                destruct (reg_eq_dec dst rr); [subst rr; rewrite /RegLocate !lookup_insert; auto| rewrite /RegLocate !lookup_insert_ne; auto]. instantiate (1 := WCap E b0 e0 a0).
                iDestruct ("Hreg" $! dst ltac:(auto)) as "Hinvdst2"; auto.
                 rewrite /RegLocate Hdst1 Hdst2. iFrame "#". }
            { assert (<[PC:=WCap RX b0 e0 a0]> (<[dst:=WCap E b0 e0 a0]> r1) = (<[PC:=WCap RX b0 e0 a0]> (<[dst:=WCap E b0 e0 a0]> r2))).
              { transitivity (<[PC:=WCap RX b0 e0 a0]> (<[dst:=WCap E b0 e0 a0]> (<[PC:=WCap p b e a]> r1))).
                - rewrite (insert_commute r1 dst); auto. rewrite insert_insert; auto.
                - rewrite Heq. rewrite (insert_commute r2 dst); auto. rewrite insert_insert; auto. }
              rewrite H0. iFrame. }
          * iDestruct "Hinvdst''" as "(_ & Hinvdst'')". iFrame.
        + iNext. iMod (do_step_pure _ [] with "[$Hs]") as "Hs /="; auto.
          iApply ("IH" $! (<[dst:=_]>r1, <[dst:=_]>r2)
                       match p0 with E => RX | _ => p0 end b0 e0 a0
                    with "[] [] [Hmap] [Hsmap] [$Hown] [$Hs] [$Hspec]").
          { iPureIntro. intros; simpl; auto.
            destruct (reg_eq_dec dst x); [subst x; rewrite !lookup_insert; split; eauto| rewrite !lookup_insert_ne; eauto]. }
          { simpl. iIntros (rr Hne). iDestruct ("Hreg" $! rr Hne) as "Hrr".
            destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; auto| rewrite !lookup_insert_ne; auto]. }
          { simpl. rewrite Hdst1. destruct p0; eauto. }
          { simpl. assert (<[PC:=match p0 with
                                 | E => WCap RX b0 e0 a0
                                 | _ => WCap p0 b0 e0 a0
                                 end]> (<[dst:=WCap p0 b0 e0 a0]> r1) = (<[PC:=WCap match p0 with
                                                                                    | E => RX
                                                                                    | _ => p0
                                                                                    end b0 e0 a0]> (<[dst:=match r2 !! dst with
                                                                                                           | Some w0 => w0
                                                                                                           | None => WInt 0%Z
                                                                                                           end]> r2))).
            { transitivity (<[PC:=match p0 with
                                  | E => WCap RX b0 e0 a0
                                  | _ => WCap p0 b0 e0 a0
                                  end]> (<[dst:=WCap p0 b0 e0 a0]> (<[PC:=WCap p b e a]> r1))).
              - rewrite !(insert_commute _ PC dst); auto.
                rewrite insert_insert. reflexivity.
              - rewrite Heq. rewrite !(insert_commute _ PC dst); auto.
                rewrite insert_insert. rewrite Hdst2. destruct p0; reflexivity. }
            rewrite H0. iFrame. }
          { destruct p0; auto. congruence. }
      - iNext. iMod (do_step_pure _ [] with "[$Hs]") as "Hs /="; auto.
        simpl. iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [eapply isCorrectPCb_nisCorrectPC; auto|].
        iIntros "!>". iDestruct 1 as "HPC".
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iIntros (Hne). congruence. }
    Unshelve. all:auto.
  Qed.

End fundamental.
