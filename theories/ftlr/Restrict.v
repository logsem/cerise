From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (*
  Lemma locality_eq_dec:
    forall (l1 l2: Locality), {l1 = l2} + {l1 <> l2}.
  Proof.
    destruct l1, l2; auto.
  Qed.

  Lemma PermPairFlows_interp_preserved W p p' l l' b e a :
    p <> E ->
    PermPairFlowsTo (p', l') (p, l) = true →
    □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1) -∗
    (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
    (fixpoint interp1) W (inr (p', l', b, e, a)).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)).
    simpl in H3, H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H3; inversion H3; simpl; auto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iDestruct "HA" as "[#HA #HB]".
      iFrame "#". iModIntro. rewrite /exec_cond /=.
      destruct (locality_eq_dec l' l).
      + subst l'. auto.
      + destruct l', l; simpl in H4; try congruence.
        iIntros. 
        iAssert (future_world Global W W') as "Hfuture".
        { iPureIntro. by apply related_sts_pub_priv. }
        iSpecialize ("HB" $! a0 r W' a1 with "Hfuture").
        iNext. iDestruct "HB" as (fs fr) "[% [% H]]". subst. 
        iExists _, _. do 2 (iSplitR; [eauto|]). 
        iIntros "[A [B [C [D E]]]]". 
        iSplitR; eauto.
        rewrite /interp_conf. 
        iDestruct "A" as "[A1 A2]".
        destruct W'. 
        iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
    - iDestruct "HA" as (p) "[% HA]".
      iDestruct "HA" as "[#HA #HB]".
      iModIntro. rewrite /exec_cond /enter_cond.
      iIntros (r W') "Hfuture". destruct (decide (in_range a b e)).
      + iAssert (future_world l W W') with "[Hfuture]" as "Hfuture".
        { destruct (locality_eq_dec l' l).
          - by subst l'.
          - destruct l', l; simpl in H4; try congruence.
            iDestruct "Hfuture" as %Hfuture.
            iPureIntro. by apply related_sts_pub_priv. 
        }
        iSpecialize ("HB" $! a r W' i with "Hfuture").
        iNext. rewrite /interp_expr /=. iExists _, _.
        do 2 (iSplitR; eauto). iIntros "A".
        iSplitR; auto.
        rewrite /interp_conf. iDestruct "HB" as (fs fr) "[% [% HB]]".
        iDestruct "A" as "[A [B [C [D E]]]]".
        iDestruct "A" as "[A1 A2]". destruct W'. 
        iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      + iNext. rewrite /interp_expr /=. iExists _, _.
        do 2 (iSplitR; eauto). iIntros "A". iClear "HB".
        iSplitR; auto.
        iDestruct "A" as "[A [B C]]".
        rewrite /registers_mapsto. rewrite /interp_conf.
        iDestruct ((big_sepM_delete _ _ PC) with "B") as "[HPC Hmap]".
        rewrite lookup_insert. reflexivity.
        rewrite delete_insert_delete.
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC").
        red; intros. apply n. inv H6. apply H9.
        iNext. iIntros "HPC".
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iIntros "%". discriminate.
    - elim HpnotE; auto.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[#HA #HB]". iFrame "#".
      iModIntro. rewrite /exec_cond.
      iIntros (a' r W' Hin) "Hfuture".
      iAssert (future_world l W W') with "[Hfuture]" as "Hfuture".
        { destruct (locality_eq_dec l' l).
          - by subst l'.
          - destruct l', l; simpl in H4; try congruence.
            iDestruct "Hfuture" as %Hfuture.
            iPureIntro. by apply related_sts_pub_priv. }
      iSpecialize ("HB" $! a' r W' Hin with "Hfuture").
      iNext. rewrite /interp_expr /=.
      iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'.
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + auto.
    - iDestruct "HA" as (p) "[% [#HA #HB]]".
      iModIntro. rewrite /exec_cond /enter_cond.
      iIntros. iNext. rewrite /interp_expr /=.
      iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'.
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + auto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iDestruct "HA" as "[#HA #HB]". iFrame "#".
      iModIntro. rewrite /exec_cond.
      iIntros (a' r W' Hin) "Hfuture".
      iNext. rewrite /interp_expr /=.
      iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'. 
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iFrame.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[#HA #HB]". auto.
      iFrame "#". iModIntro.
      rewrite /exec_cond. iIntros. iNext.
      rewrite /interp_expr /=.
      iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'. 
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + auto.
    - iDestruct "HA" as (p) "[% HA]".
      iDestruct "HA" as "[#HA #HB]". 
      iModIntro. rewrite /enter_cond /interp_expr /=.
      iIntros. iNext. iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'. 
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + auto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[#HA #HB]". iFrame "#".
      iModIntro. rewrite /exec_cond.
      iIntros (a' r W' Hin) "Hfuture".
      iNext. iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'. 
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + auto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iDestruct "HA" as "[#HA #HB]".
      iFrame "#". iModIntro.
      rewrite /exec_cond. iIntros (a' r W' Hin) "Hfuture".
      iNext. iExists _,_. iSplitR; auto. iSplitR; auto.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. destruct W'. 
      iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
  Qed.

  Lemma match_perm_with_E_rewrite:
    forall (A: Type) p (a1 a2: A),
      match p with
      | E => a1
      | _ => a2
      end = if (perm_eq_dec p E) then a1 else a2.
  Proof.
    intros. destruct (perm_eq_dec p E); destruct p; auto; congruence.
  Qed.

  Lemma restrict_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (r0 : Z + RegName) :
    ftlr_instr fs fr r p p' g b e a w (cap_lang.Restrict dst r0).
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (PermPairFlowsTo (decodePermPair z) (p, g)); intros.
        * case_eq (a + 1)%a; intros.
          { iApply (wp_restrict_success_z_PC with "[$HPC $Ha]"); eauto.
            iNext. iIntros "(HPC & Ha)".
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply wp_pure_step_later; auto.
            case_eq (decodePermPair z); intros. rewrite H5 in H3.
            destruct (andb_true_eq _ _ ltac:(symmetry in H3; exact H3)).
            simpl in H6. destruct p0; simpl in H6; try contradiction.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
              iNext. iAlways. iExists _; iFrame "#". auto.
              iPureIntro.
              apply PermFlows_trans with p; auto.
              destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; done. 
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
              iNext. iAlways. iExists _; iFrame "#". auto.
              iPureIntro.
              apply PermFlows_trans with p; auto.
              destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; try done.
              rewrite Hp in H6; inversion H6.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
              iNext. iAlways. iExists _; iFrame "#". auto.
              iPureIntro.
              apply PermFlows_trans with p; auto.
              destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; try done;
              rewrite Hp in H6; inversion H6. }
          { iApply (wp_restrict_failPC1' with "[$HPC $Ha]"); eauto.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
        * iApply (wp_restrict_failPC1 with "[$HPC $Ha]"); eauto.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (Hsome r0) as [wr0 Hsomer0].
        destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          repeat rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (p, g)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_reg_PC with "[$HPC $Ha $Hr0]"); eauto.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
                iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                case_eq (decodePermPair z); intros.
                destruct (andb_true_eq _ _ ltac:(symmetry in H3; exact H3)).
                rewrite H5 in H6; simpl in H6. destruct p0; simpl in H6; try congruence.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iDestruct (big_sepM_delete _ _ PC with "Hmap") as "[HPC Hmap]"; 
                    first by rewrite lookup_insert.
                  iNext. iApply (wp_bind (fill [SeqCtx])).
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iDestruct (big_sepM_delete _ _ PC with "Hmap") as "[HPC Hmap]"; 
                    first by rewrite lookup_insert.
                  iNext. iApply (wp_bind (fill [SeqCtx])).
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
                  iNext. iAlways. iExists _; iFrame "#".
                  iPureIntro.
                  destruct Hp as [Hp | [Hp | Hp] ]; 
                    apply PermFlows_trans with p;subst p; auto. 
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
                  iNext. iAlways. iExists _; iFrame "#".
                  iPureIntro.
                  destruct Hp as [Hp | [Hp | Hp] ]; 
                    apply PermFlows_trans with p;subst p; auto; congruence.
                - iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; eauto.
                  iNext. iAlways. iExists _; iFrame "#".
                  iPureIntro.
                  destruct Hp as [Hp | [Hp | Hp] ]; 
                    apply PermFlows_trans with p;subst p; auto; congruence.
              }
              { iApply (wp_restrict_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros.  iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_restrict_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
      rewrite lookup_delete_ne; eauto.
      destruct wdst.
      { iApply (wp_restrict_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c, p0, p0, p0.
        - destruct r0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (p0, l)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_z with "[$HPC $Ha $Hdst]"); eauto.
                repeat rewrite match_perm_with_E_rewrite. destruct (perm_eq_dec p0 E).
                - subst p0. iNext. iIntros "(HPC & Ha & Hdst)".
                  iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - iNext. iIntros "(HPC & Ha & Hdst)".
                  iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  repeat rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
                  iApply wp_pure_step_later; auto.
                  iAssert ((interp_registers _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> r)))%I
                    as "#[Hfull' Hreg']".
                  { iSplitL.
                    - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                    - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                      + subst r2. rewrite /RegLocate lookup_insert.
                        iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                        simpl. destruct (decodePermPair z).
                        iApply (PermPairFlows_interp_preserved); auto. done. auto.
                      + rewrite /RegLocate lookup_insert_ne; auto.
                        iApply "Hreg"; auto. }
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                    iFrame "#"; eauto. }
              { iApply (wp_restrict_fail1' with "[$HPC $Ha $Hdst]"); eauto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_fail1 with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (Hsome r0) as [wr0 Hsomer0].
            destruct (reg_eq_dec PC r0).
            * subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (reg_eq_dec dst r0).
              { subst r0. iApply (wp_restrict_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wr0.
                - case_eq (PermPairFlowsTo (decodePermPair z) (p0, l)); intros.
                  * case_eq (a + 1)%a; intros.
                    { revert H3; intro H3.
                      iApply (wp_restrict_success_reg with "[$HPC $Ha $Hdst $Hr0]"); eauto.
                      repeat rewrite match_perm_with_E_rewrite. destruct (perm_eq_dec p0 E).
                      - iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate.
                      - iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                        iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iDestruct (region_close with "[$Hr $Ha]") as "Hr";
                          [iFrame "#"; auto|].
                        iApply wp_pure_step_later; auto.
                        iAssert ((interp_registers _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> (<[r0:=inl z]> r))))%I
                          as "#[Hfull' Hreg']".
                        { iSplitL.
                          - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                            destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                          - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                            + subst r2. rewrite /RegLocate lookup_insert.
                              iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                              simpl. destruct (decodePermPair z).
                              iApply (PermPairFlows_interp_preserved); auto. done. auto. 
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r0 r2).
                              * subst r2; rewrite lookup_insert. simpl.
                                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                              * rewrite lookup_insert_ne; auto.
                                iApply "Hreg"; auto. }
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                          iFrame "#"; eauto. }
                    { iApply (wp_restrict_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  * iApply (wp_restrict_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_restrict_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Qed. *)

End fundamental.