From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ,
            logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : D.

  Lemma RX_jnz_case:
    ∀ r a g M fs fr b e p' w r1 r2
      (* RWX case *)
      (fundamental_RWX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ M r)%I)
      (* (* RWLX case *) *)
      (fundamental_RWLX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ M r)%I)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = Jnz r1 r2)
      (Heq : fs = M.1.1 ∧ fr = M.1.2),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
            full_map a0
         -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r0))
         -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
         -∗ Exact_w wγ a7
         -∗ sts_full a3 a4
         -∗ na_own logrel_nais ⊤
         -∗ ⌜a7.1.1 = a3⌝
         → ⌜a7.1.2 = a4⌝
         → □ (∃ p : Perm, ⌜PermFlows RX p⌝
                           ∧ ([∗ list] a8 ∈ region_addrs a5 a6, 
                              na_inv logrel_nais (logN.@a8)
                                     (∃ w0 : leibnizO Word, a8 ↦ₐ[p] w0 ∗ ▷ interp w0)))
         -∗ ⟦ [a3, a4] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ ▷ interp w0))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
        -∗ □ ▷ ▷ interp w
        -∗ Exact_w wγ M
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
              ∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais ⊤)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais ⊤
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros r a g M fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval". 
    iIntros "HM Hsts Ha Hown Hcls HPC Hmap".
    destruct Heq as [Heq1 Heq2].
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r2).
    * subst r2.
      destruct (reg_eq_dec PC r1).
      { subst r1. iApply (wp_jnz_success_jmpPC with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha)".
        simpl. iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        iApply wp_pure_step_later; auto. iNext.
        iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
        iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto; auto. }
      { destruct (H3 r1) as [wr1 Hsomer1].
        iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
        { rewrite lookup_delete_ne; eauto. }
        iApply (wp_jnz_success_jmpPC2 with "[HPC Hr1 Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr1)".
        iApply wp_pure_step_later; auto.
        iDestruct ("Hreg" $! r1 ltac:(auto)) as "Hwr1".
        rewrite /RegLocate Hsomer1. 
        iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
        rewrite -delete_insert_ne; auto.
        destruct (updatePcPerm wr1) eqn:Heq.
        { iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. }
        { destruct c,p,p,p.
          destruct p.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            destruct wr1; simpl in Heq; try congruence.
            destruct c,p,p,p,p; try congruence.
            + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
              simpl. rewrite /read_write_cond.
              iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
              iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H4.
              iDestruct "H" as (p) "[% [H1 H2]]".
              iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
            + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
              simpl. rewrite /enter_cond.
              iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H4.
              rewrite /interp_expr /=.
              iDestruct "H" as "#H".
              iDestruct ("H" $! M.1 r) as "H'".
              iAssert (|==> match g' with Global => Exact_w wγ (M.1, true) | Local => Exact_w wγ M end)%I with "[HM]" as "HM".
              { destruct M; destruct b0; destruct g'; auto.
                simpl. iMod (RelW_public_to_private with "HM") as "[HM1 HM2]".
                auto. }
              iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
              iMod "HM" as "HM".
              iDestruct "H'" as (fs fr) "[% [% HH]]".
              iDestruct ("HH" with "[HM Hsts Hmap Hcls']") as "Hx"; iFrame; eauto.
              { inv H4. destruct M. simpl.
                destruct g'; simpl.
                - iFrame. iSplitR; auto.
                - iFrame. iSplitR; auto.
                  destruct b0; auto.
                  (* We have M = (W, global) and we have an (E, local) capability
                   Can't convert global to local ? *)
                  admit. }
              iDestruct "Hx" as (px gx bx ex ax) "[% Hx]".
              inv H6; destruct gx; simpl; auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            destruct wr1; simpl in Heq; try congruence.
            destruct c,p,p,p,p; try congruence. inv Heq.
            rewrite (fixpoint_interp1_eq (inr _)).
            simpl. iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H4.
            iDestruct "H" as (p) "[% [H1 H2]]".
            iDestruct (fundamental_RWX with "[H1]") as "Hind"; eauto.
            rewrite /interp_expression /=.
            instantiate (H9:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
            inv H5. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
            iDestruct "Hind" as (px gx bx ex ax) "[% H]".
            iApply "H".
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            destruct wr1; simpl in Heq; try congruence.
            destruct c,p,p,p,p; try congruence. inv Heq.
            rewrite (fixpoint_interp1_eq (inr _)).
            simpl. iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H4.
            iDestruct "H" as (p) "[% [H1 H2]]".
            iDestruct (fundamental_RWLX with "[H1]") as "Hind"; eauto.
            rewrite /interp_expression /=.
            instantiate (H9:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
            inv H5. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
            iDestruct "Hind" as (px gx bx ex ax) "[% H]".
            iApply "H". } }
    * destruct (H3 r2) as [wr2 Hsomer2].
      iDestruct ((big_sepM_delete _ _ r2) with "Hmap") as "[Hr2 Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      case_eq (nonZero wr2); intros.
      { assert (wr2 <> inl 0%Z) by (intro; subst wr2; cbv in H4; congruence).
        destruct (reg_eq_dec PC r1).
        - subst r1. iApply (wp_jnz_success_jmpPC1 with "[HPC Hr2 Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto.
          simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r2); auto.
          iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
          iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto; auto.
        - destruct (reg_eq_dec r2 r1).
          + subst r1. iApply (wp_jnz_success_jmp2 with "[HPC Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr2)".
            iApply wp_pure_step_later; auto.
            simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r2); auto.
            destruct (updatePcPerm wr2) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iDestruct ("Hreg" $! r2 ltac:(auto)) as "Hwr2".
                rewrite /RegLocate Hsomer2.
                destruct wr2; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence.
                + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
                  simpl. rewrite /read_write_cond.
                  iDestruct "Hwr2" as (g' b' e' a') "[% H]". inv H6.
                  iDestruct "H" as (p) "[% [H1 H2]]".
                  iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                  iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                + inv Heq. rewrite (fixpoint_interp1_eq (inr _)).
                  simpl. rewrite /enter_cond.
                  iDestruct "Hwr2" as (g' b' e' a') "[% H]". inv H6.
                  rewrite /interp_expr /=.
                  iDestruct "H" as "#H".
                  iDestruct ("H" $! M.1 r) as "H'".
                  iAssert (|==> match g' with Global => Exact_w wγ (M.1, true) | Local => Exact_w wγ M end)%I with "[HM]" as "HM".
                  { destruct M; destruct b0; destruct g'; auto.
                    simpl. iMod (RelW_public_to_private with "HM") as "[HM1 HM2]".
                    auto. }
                  iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                  iMod "HM" as "HM".
                  iDestruct "H'" as (fs fr) "[% [% HH]]".
                  iDestruct ("HH" with "[HM Hsts Hmap Hcls']") as "Hx"; iFrame; eauto.
                  { inv H6. destruct M. simpl.
                    destruct g'; simpl.
                    - iFrame. iSplitR; auto.
                    - iFrame. iSplitR; auto.
                      destruct b0; auto.
                      (* We have M = (W, global) and we have an (E, local) capability
                   Can't convert global to local ? *)
                      admit. }
                  iDestruct "Hx" as (px gx bx ex ax) "[% Hx]".
                  inv H8; destruct gx; simpl; auto.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                destruct wr2; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence. inv Heq.
                iDestruct ("Hreg" $! r2 ltac:(auto)) as "Hwr2".
                rewrite /RegLocate Hsomer2 /=. rewrite (fixpoint_interp1_eq (inr _)).
                iDestruct "Hwr2" as (g' b' e' a') "[% H]". inv H6.
                simpl. iDestruct "H" as (p) "[% [H1 H2]]".
                iDestruct (fundamental_RWX with "[H1]") as "Hind"; eauto.
                rewrite /interp_expression /=.
                instantiate (H11:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
                inv H7. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
                iDestruct "Hind" as (px gx bx ex ax) "[% H]".
                iApply "H".
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                destruct wr2; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence. inv Heq.
                iDestruct ("Hreg" $! r2 ltac:(auto)) as "Hwr2".
                rewrite /RegLocate Hsomer2 /=. rewrite (fixpoint_interp1_eq (inr _)).
                iDestruct "Hwr2" as (g' b' e' a') "[% H]". inv H6.
                simpl. iDestruct "H" as (p) "[% [H1 H2]]".
                iDestruct (fundamental_RWLX with "[H1]") as "Hind"; eauto.
                rewrite /interp_expression /=.
                instantiate (H11:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
                inv H7. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
                iDestruct "Hind" as (px gx bx ex ax) "[% H]".
                iApply "H". }
          + destruct (H3 r1) as [wr1 Hsomer1].
            iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
            { repeat rewrite lookup_delete_ne; eauto. }
            iApply (wp_jnz_success_jmp with "[HPC Hr1 Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr1 & Hr2)".
            iApply wp_pure_step_later; auto.
            simpl. iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            repeat rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r1); auto.
            iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto. rewrite (insert_id r r2); auto.
            destruct (updatePcPerm wr1) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iDestruct ("Hreg" $! r1 ltac:(auto)) as "Hwr1".
                rewrite /RegLocate Hsomer1.
                destruct wr1; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence; inv Heq.
                + rewrite (fixpoint_interp1_eq (inr _)) /=.
                  iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                  iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H6.
                  simpl. iDestruct "H" as (p) "[% [H1 H2]]".
                  iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                + rewrite (fixpoint_interp1_eq (inr _)) /=.
                  rewrite /enter_cond.
                  iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H6.
                  rewrite /interp_expr /=.
                  iDestruct "H" as "#H".
                  iDestruct ("H" $! M.1 r) as "H'".
                  iAssert (|==> match g' with Global => Exact_w wγ (M.1, true) | Local => Exact_w wγ M end)%I with "[HM]" as "HM".
                  { destruct M; destruct b0; destruct g'; auto.
                    simpl. iMod (RelW_public_to_private with "HM") as "[HM1 HM2]".
                    auto. }
                  iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                  iMod "HM" as "HM".
                  iDestruct "H'" as (fs fr) "[% [% HH]]".
                  iDestruct ("HH" with "[HM Hsts Hmap Hcls']") as "Hx"; iFrame; eauto.
                  { inv H6. destruct M. simpl.
                    destruct g'; simpl.
                    - iFrame. iSplitR; auto.
                    - iFrame. iSplitR; auto.
                      destruct b0; auto.
                      (* We have M = (W, global) and we have an (E, local) capability
                   Can't convert global to local ? *)
                      admit. }
                  iDestruct "Hx" as (px gx bx ex ax) "[% Hx]".
                  inv H8; destruct gx; simpl; auto.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                iDestruct ("Hreg" $! r1 ltac:(auto)) as "Hwr1".
                rewrite /RegLocate Hsomer1.
                destruct wr1; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence. inv Heq.
                rewrite (fixpoint_interp1_eq (inr _)) /=.
                iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H6.
                simpl. iDestruct "H" as (p) "[% [H1 H2]]".
                iDestruct (fundamental_RWX with "[H1]") as "Hind"; eauto.
                rewrite /interp_expression /=.
                instantiate (H11:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
                inv H7. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
                iDestruct "Hind" as (px gx bx ex ax) "[% H]".
                iApply "H".
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iNext. iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
                iDestruct ("Hreg" $! r1 ltac:(auto)) as "Hwr1".
                rewrite /RegLocate Hsomer1.
                destruct wr1; simpl in Heq; try congruence.
                destruct c,p,p,p,p; try congruence. inv Heq.
                rewrite (fixpoint_interp1_eq (inr _)) /=.
                iDestruct "Hwr1" as (g' b' e' a') "[% H]". inv H6.
                simpl. iDestruct "H" as (p) "[% [H1 H2]]".
                iDestruct (fundamental_RWLX with "[H1]") as "Hind"; eauto.
                rewrite /interp_expression /=.
                instantiate (H11:= M). iDestruct "Hind" as (fs fr) "[% [% Hind]]".
                inv H7. iDestruct ("Hind" with "[HM Hsts Hcls' Hmap]") as "Hind"; iFrame; eauto.
                iDestruct "Hind" as (px gx bx ex ax) "[% H]".
                iApply "H". } }
      { assert (wr2 = inl 0%Z) by (destruct wr2; cbv in H4; try congruence; destruct z; try congruence).
        subst wr2. case_eq (a+1)%a; intros.
        - iApply (wp_jnz_success_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto. rewrite (insert_id r r2); auto.
          iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); eauto; auto.
        - iApply (wp_jnz_fail_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate. }
  Admitted.

End fundamental.