From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine.rules Require Import rules_Mov.

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

  Lemma mov_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName):
    ftlr_instr W r p p' g b e a w (Mov dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { (* TODO: it might be possible to refactor the proof below by using more simplify_map_eq *)
      (* TODO: use incrementPC_inv *)
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst. rewrite lookup_insert in HPC. inv HPC.
        repeat rewrite insert_insert.
        destruct src; simpl in H3; try discriminate.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        destruct (reg_eq_dec PC r0).
        { subst r0. rewrite lookup_insert in H3. inv H3.
          iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto. }
        { rewrite lookup_insert_ne in H3; auto.
          rewrite /RegLocate. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0". rewrite H3.
          destruct (PermFlowsTo RX p'') eqn:Hpft.
          - iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
            + destruct p''; simpl in Hpft; auto.
              repeat rewrite fixpoint_interp1_eq. simpl.
              destruct g''; auto.
            + iModIntro.
              destruct p''; simpl in Hpft; try discriminate; repeat (rewrite fixpoint_interp1_eq); simpl; try (iDestruct "Hr0" as (px) "[% [H2 H3]]"; iExists px; try split; auto).
              destruct g''; auto. iDestruct "Hr0" as (px) "[% [H2 H3]]"; iExists px; try split; auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate. } }
      { rewrite lookup_insert_ne in HPC; auto.
        rewrite lookup_insert in HPC. inv HPC.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        iApply ("IH" $! _ (<[dst:=w0]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri Hri).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite /RegLocate lookup_insert.
            destruct src; simpl in H3.
            * inv H3; repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (reg_eq_dec PC r0).
              { subst r0.
                - rewrite lookup_insert in H3. inv H3.
                  rewrite (fixpoint_interp1_eq _ (inr (_, g'', b'', e'', a''))) /=.
                  iAssert (□ exec_cond W b'' e'' g'' p'' (fixpoint interp1))%I as "#Hexec".
                  { iAlways. rewrite /exec_cond. iIntros (a' r' W' Hin) "#Hfuture".
                    iNext. rewrite /interp_expr /=.
                    iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                    iSplitR; eauto.
                    iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                    iAlways. iExists p'. iSplitR; auto.
                    unfold future_world; destruct g''; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                    - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                      iPureIntro; split.
                      + assert (pwl p'' = false) by (destruct Hp as [Hp | [Hp | [Hp Hcontr] ] ]; subst p''; try congruence; auto).
                        rewrite H6 in H4. rewrite H6.
                        eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H4). auto.
                      + eapply related_sts_rel_std; eauto.
                    - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                      iPureIntro; split.
                      + destruct (pwl p'').
                        * eapply region_state_pwl_monotone; eauto.
                        * eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H4); eauto.
                      + eapply rel_is_std_i_monotone; eauto.
                  }
                destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p''; try subst g'';
                  (iExists p'; iSplitR;[auto|]; iFrame "Hinv Hexec"). }
              rewrite lookup_insert_ne in H3; auto.
              iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0".
              rewrite H3. auto.
          + repeat rewrite /RegLocate lookup_insert_ne; auto.
            iApply "Hreg"; auto.
      }
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
