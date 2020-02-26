From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine.rules Require Import rules_Restrict.

(* TODO: Move into logrel.v *)
Instance future_world_persistent (Σ: gFunctors) g W W': Persistent (@future_world Σ g W W').
Proof.
  unfold future_world. destruct g; apply bi.pure_persistent.
Qed.

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

  Lemma locality_eq_dec:
    forall (l1 l2: Locality), {l1 = l2} + {l1 <> l2}.
  Proof.
    destruct l1, l2; auto.
  Qed.

  Lemma loc_flowsto_region_state_nwl W y l l':
    LocalityFlowsTo l' l = true ->
    region_state_nwl W y l ->
    region_state_nwl W y l'.
  Proof.
    intros; destruct l, l'; simpl; auto; discriminate.
  Qed.

  Lemma PermPairFlows_interp_preserved W p p' l l' b e a :
    p <> E ->
    PermPairFlowsTo (p', l') (p, l) = true →
    □ ▷ (∀ (a7 : leibnizO (STS * STS)) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
           (a11 a12 a13 : Addr),
            full_map a8
            -∗ (∀ r1 : RegName,
                   ⌜r1 ≠ PC⌝
                   → ((fixpoint interp1) a7)
                       match a8 !! r1 with
                       | Some w0 => w0
                       | None => inl 0%Z
                       end)
            -∗ registers_mapsto (<[PC:=inr (a9, a10, a11, a12, a13)]> a8)
            -∗ region a7
            -∗ sts_full_world sts_std a7
            -∗ na_own logrel_nais ⊤
            -∗ ⌜a9 = RX ∨ a9 = RWX ∨ a9 = RWLX ∧ a10 = Local⌝
            → □ (∃ p'0 : Perm,
                    ⌜PermFlows a9 p'0⌝
                    ∧ ([∗ list] a14 ∈ region_addrs a11 a12, 
                       read_write_cond a14 p'0 interp
                       ∧ ⌜if pwl a9
                          then region_state_pwl a7 a14
                          else region_state_nwl a7 a14 a10⌝
                               ∧ ⌜region_std a7 a14⌝)) -∗ 
                interp_conf a7) -∗
    (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
    (fixpoint interp1) W (inr (p', l', b, e, a)).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)).
    simpl in H3, H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H3; inversion H3; simpl; auto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iFrame "%".
      iApply (big_sepL_mono with "HA").
      simpl; intros. iIntros "[H [% %]]".
      iSplitL; auto. iFrame "%".
      iPureIntro. eapply loc_flowsto_region_state_nwl; eauto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA").
        simpl; intros. iIntros "[H [% %]]".
        iSplitL; auto. iFrame "%".
        iPureIntro. eapply loc_flowsto_region_state_nwl; eauto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iFrame "%".
      iApply (big_sepL_mono with "HA").
      simpl; intros. iIntros "[H [% %]]".
      iSplitL; auto. iFrame "%".
      iPureIntro. eapply loc_flowsto_region_state_nwl; eauto.
    - destruct l; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + assert (l' = Local) by (destruct l'; auto; discriminate).
        subst l'. simpl. iApply (big_sepL_mono with "HA").
        simpl; intros. iIntros "[H [% %]]".
        iSplitL; auto.
    - destruct l; auto.
      iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + assert (l' = Local) by (destruct l'; auto; discriminate).
        subst l'. simpl. iApply (big_sepL_mono with "HA").
        simpl; intros. iIntros "[H [% %]]".
        iSplitL; auto.
    - destruct l; auto. assert (l' = Local) by (destruct l'; auto; discriminate).
      subst l'. auto.
    - iDestruct "HA" as (p) "[% [HA _]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto. iPureIntro; split; auto.
        eapply loc_flowsto_region_state_nwl; eauto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iDestruct "HA" as "[#HA #HB]".
      iSplit.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto. iPureIntro; split; auto.
        eapply loc_flowsto_region_state_nwl; eauto.
      + iModIntro. rewrite /exec_cond /=.
        destruct (locality_eq_dec l' l).
        * subst l'. auto.
        * destruct l', l; simpl in H4; try congruence.
          iIntros. 
          iAssert (future_world Global W W') as "Hfuture".
          { iPureIntro. by apply related_sts_pub_priv_world. }
          iSpecialize ("HB" $! a0 r W' a1 with "Hfuture").
          iNext. iIntros "[A [B [C [D E]]]]". 
          iSplitR; eauto.
          iDestruct "A" as "[A1 A2]".
          iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
          simpl. iModIntro.
          iExists p. iSplitR; auto.
          iApply (big_sepL_mono with "HA"); simpl; intros.
          iIntros "[H [% %]]".
          iSplitL; auto. iPureIntro; split; auto.
          { right. eapply (region_state_nwl_monotone W W' y Global); auto. }
          { eapply rel_is_std_i_monotone; eauto. }
    - iDestruct "HA" as (p) "[% HA]".
      iDestruct "HA" as "[#HA #HB]".
      iModIntro. rewrite /exec_cond /enter_cond.
      iIntros (r W') "Hfuture". destruct (decide (in_range a b e)).
      + iDestruct "Hfuture" as "#Hfuture".
        iNext. rewrite /interp_expr /=. iIntros "[[A1 A2] [B [C [D E]]]]".
        iSplitR; auto. rewrite /interp_conf. 
        iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
        iModIntro. iExists p. iSplitR; auto.
        destruct l'; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "HA"); simpl; intros; iIntros "[H [% %]]"; iSplitL; auto; iPureIntro.
        { destruct l; simpl in H4; try congruence.
          simpl in H7. split.
          - eapply (region_state_nwl_monotone_nl W W' y); auto.
          - eapply related_sts_rel_std; eauto. }
        { split.
          - destruct l; simpl in H7.
            + right. eapply (region_state_nwl_monotone W W' y Global); auto.
            + eapply (region_state_nwl_monotone W W' y Local); auto.
          - eapply rel_is_std_i_monotone; eauto. }
      + iNext. rewrite /interp_expr /=.
        iIntros "A". iClear "HB".
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
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto. iPureIntro; split; auto.
        eapply loc_flowsto_region_state_nwl; eauto.
    - iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto. iPureIntro; split; auto.
        eapply loc_flowsto_region_state_nwl; eauto.
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iPureIntro. eapply PermFlows_trans; eauto.
      reflexivity. iDestruct "HA" as "[#HA #HB]".
      iSplit.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto. iPureIntro; split; auto.
        eapply loc_flowsto_region_state_nwl; eauto.
      + iModIntro. rewrite /exec_cond.
        iIntros (a' r W' Hin) "#Hfuture".
        rewrite /interp_expr /=.
        iNext. iIntros "[[A1 A2] [B [C [D E]]]]".
        iSplitR; auto. iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
        iAlways. iExists p. iSplitR.
        * iPureIntro. eapply PermFlows_trans; eauto. constructor.
        * simpl. destruct l'; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "HA"); simpl; intros; iIntros "[H [% %]]"; iSplitL; auto; iPureIntro.
          { destruct l; simpl in H4; try congruence.
            simpl in H7. split.
            - eapply (region_state_nwl_monotone_nl W W' y); auto.
            - eapply related_sts_rel_std; eauto. }
          { split.
            - destruct l; simpl in H7.
              + right. eapply (region_state_nwl_monotone W W' y Global); auto.
              + eapply (region_state_nwl_monotone W W' y Local); auto.
            - eapply rel_is_std_i_monotone; eauto. }
    - iDestruct "HA" as (p) "[% [#HA #HB]]".
      iModIntro. rewrite /exec_cond /enter_cond.
      iIntros (r W') "#Hfuture". iNext.
      rewrite /interp_expr /=.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + simpl. destruct l'; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "HA"); simpl; intros; iIntros "[H [% %]]"; iSplitL; auto; iPureIntro.
        { destruct l; simpl in H4; try congruence.
          simpl in H7. split.
          - eapply (region_state_nwl_monotone_nl W W' y); auto.
          - eapply related_sts_rel_std; eauto. }
        { split.
          - destruct l; simpl in H7.
            + right. eapply (region_state_nwl_monotone W W' y Global); auto.
            + eapply (region_state_nwl_monotone W W' y Local); auto.
          - eapply rel_is_std_i_monotone; eauto. }
    - iDestruct "HA" as (p) "[% HA]".
      iExists p. iSplitR; auto.
      iDestruct "HA" as "[#HA #HB]".
      destruct (locality_eq_dec l l').
      + subst l'; auto.
      + destruct l, l'; simpl in H4; try congruence.
        iSplit.
        * iApply (big_sepL_mono with "HA"); simpl; intros.
          iIntros "[H [% %]]"; iSplitL; auto.
        * iAlways. rewrite /exec_cond.
          iIntros (a' r W' Hin) "%".
          iNext. rewrite /interp_expr /=.
          iIntros "[[A1 A2] [B [C [D E]]]]".
          iSplitR; auto. iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
          iAlways. iExists p.
          iSplitR; auto.
          iApply (big_sepL_mono with "HA"); simpl; intros; iIntros "[H [% %]]"; iSplitL; auto; iPureIntro.
          split; [right | eapply rel_is_std_i_monotone; eauto].
          eapply (region_state_nwl_monotone W W' y Global); auto.
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto.
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto.
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% [HA HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]".
        iSplitL; auto.
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% [#HA #HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iSplit.
        * iApply (big_sepL_mono with "HA"); simpl; intros.
          iIntros "[H [% %]]". iSplitL; auto.
        * iAlways. rewrite /exec_cond.
          iIntros (a0 r W' Hin Hfuture).
          iNext. iIntros "[[A1 A2] [B [C [D E]]]]".
          iSplitR; auto.
          iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
          iAlways. iExists p. iSplitR.
          { iPureIntro. eapply PermFlows_trans; eauto. constructor. }
          { iApply (big_sepL_mono with "HA"); simpl; intros.
            iIntros "[H [% %]]". iSplitL; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone W W' y Local); auto.
              left. auto.
            - eapply rel_is_std_i_monotone; eauto. }
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% HA]".
      iDestruct "HA" as "[#HA #HB]". 
      iModIntro. rewrite /enter_cond /interp_expr /=.
      iIntros (r W' Hfuture). iNext.
      iIntros "[[A1 A2] [B [C [D E]]]]".
      iSplitR; auto. iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
      iAlways. iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto. constructor.
      + simpl. iApply (big_sepL_mono with "HA"); simpl; intros.
        iIntros "[H [% %]]". iSplitL; auto.
        iPureIntro. split.
        * eapply (region_state_nwl_monotone W W' y Local); auto.
          left. auto.
        * eapply rel_is_std_i_monotone; eauto.
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      iDestruct "HA" as (p) "[% [#HA #HB]]".
      iExists p. iSplitR.
      + iPureIntro. eapply PermFlows_trans; eauto.
        reflexivity.
      + iSplit.
        * iApply (big_sepL_mono with "HA"); simpl; intros.
          iIntros "[H [% %]]". iSplitL; auto.
        * iAlways. rewrite /exec_cond.
          iIntros (a0 r W' Hin Hfuture).
          iNext. iIntros "[[A1 A2] [B [C [D E]]]]".
          iSplitR; auto.
          iApply ("IH" with "[A1] [A2] [B] [C] [D] [E]"); auto.
          iAlways. iExists p. iSplitR.
          { iPureIntro. eapply PermFlows_trans; eauto. constructor. }
          { iApply (big_sepL_mono with "HA"); simpl; intros.
            iIntros "[H [% %]]". iSplitL; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone W W' y Local); auto.
              left. auto.
            - eapply rel_is_std_i_monotone; eauto. }
    - destruct l; auto. destruct l'; simpl in H4; try discriminate.
      auto.
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

  Lemma restrict_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName):
    ftlr_instr W r p p' g b e a w (Restrict dst r0) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (PermPairFlowsTo (decodePermPair z) (p, g)); intros.
        * case_eq (a + 1)%a; intros.
          { iApply (wp_restrict_success_z_PC with "[$HPC $Ha]"); eauto.
            iNext. iIntros "(HPC & Ha)".
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
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
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
              iNext. iAlways. iExists p'. iSplit.
              + iPureIntro. apply PermFlows_trans with p; auto.
                eapply (proj1 (andb_prop _ _ H3)).
              + iApply (big_sepL_mono with "Hinv"); simpl; intros.
                iIntros "[H [% %]]". iSplitL; auto.
                iPureIntro. split; auto.
                destruct (locality_eq_dec l g).
                * subst g. destruct p; simpl in H9; try congruence.
                  destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; try discriminate.
                  subst l. left; auto.
                * destruct p; simpl in H9; try congruence.
                  { destruct l; destruct g; simpl in H7; try congruence.
                    right; auto. }
                  { destruct l; destruct g; simpl in H7; try congruence.
                    right; auto. }
                  { destruct Hp as [Hp | [ Hp | [Hp Hg] ] ]; try discriminate.
                    subst g. destruct l; simpl in H7; try congruence. }
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
              iNext. iAlways. iExists p'. iSplit.
              + iPureIntro. apply PermFlows_trans with p; auto.
                eapply (proj1 (andb_prop _ _ H3)).
              + iApply (big_sepL_mono with "Hinv"); simpl; intros.
                iIntros "[H [% %]]". iSplitL; auto.
                iPureIntro. split; auto.
                destruct (locality_eq_dec l g).
                * subst g. destruct p; simpl in H9; try congruence.
                  destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; try discriminate.
                  subst l. left; auto.
                * destruct p; simpl in H9; try congruence.
                  { destruct l; destruct g; simpl in H7; try congruence.
                    right; auto. }
                  { destruct l; destruct g; simpl in H7; try congruence.
                    left; auto. }
            - destruct p; try congruence.
              destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; try congruence; subst g.
              destruct l; simpl in H7; try congruence.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto. }
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
                iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
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
                - rewrite H5 in H3, H7.
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
                  iNext. iAlways. iExists p'. iSplit.
                  + iPureIntro. apply PermFlows_trans with p; auto.
                    eapply (proj1 (andb_prop _ _ H3)).
                  + iApply (big_sepL_mono with "Hinv"); simpl; intros.
                    iIntros "[H [% %]]". iSplitL; auto.
                    iPureIntro. split; auto.
                    destruct (locality_eq_dec l g).
                    * subst g. destruct p; simpl in H9; try congruence.
                      destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; try discriminate.
                      subst l. left; auto.
                    * destruct p; simpl in H9; try congruence.
                      { destruct l; destruct g; simpl in H7; try congruence.
                        right; auto. }
                      { destruct l; destruct g; simpl in H7; try congruence.
                        right; auto. }
                      { destruct Hp as [Hp | [ Hp | [Hp Hg] ] ]; try discriminate.
                        subst g. destruct l; simpl in H7; try congruence. }
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
                  erewrite lookup_insert; eauto.
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
                  rewrite H5 in H3, H7.
                  iNext. iAlways. iExists p'. iSplit.
                  + iPureIntro. apply PermFlows_trans with p; auto.
                    eapply (proj1 (andb_prop _ _ H3)).
                  + iApply (big_sepL_mono with "Hinv"); simpl; intros.
                    iIntros "[H [% %]]". iSplitL; auto.
                    iPureIntro. split; auto.
                    destruct (locality_eq_dec l g).
                    * subst g. destruct p; simpl in H9; try congruence.
                      destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; try discriminate.
                      subst l. left; auto.
                    * destruct p; simpl in H9; try congruence.
                      { destruct l; destruct g; simpl in H7; try congruence.
                        right; auto. }
                      { destruct l; destruct g; simpl in H7; try congruence.
                        left; auto. }
                - rewrite H5 in H3, H7.
                  destruct p; try congruence.
                  destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; try congruence; subst g.
                  destruct l; simpl in H7; try congruence.
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto. }
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
                  iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
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
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]");
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
                        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
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
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]");
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
  Qed.

End fundamental.
