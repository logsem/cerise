From cap_machine Require Export logrel monotone.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ,
            logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : D.

  Lemma RX_jnz_case:
    ∀ E0 r a g fs fr b e p' w r1 r2
      (* RWX case *)
      (fundamental_RWX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = Jnz r1 r2),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RX p⌝
                      ∧ ([∗ list] a7 ∈ region_addrs a5 a6, 
                         na_inv logrel_nais (logN.@a7)
                                (∃ w0 : leibnizO Word,
                                    a7 ↦ₐ[p] w0
                                  ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))))
           -∗ □ ⌜∀ a' : Addr, (a5 ≤ a')%Z ∧ (a' ≤ a6)%Z → ↑logN.@a' ⊆ E0⌝
           -∗ ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0)))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ stsf E1, ▷ ((interp E1) stsf) w)
        -∗ □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (E0 ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ (∀ stsf E1, ▷ ((interp E1) stsf) w0))
              ∗ na_own logrel_nais (E0 ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais E0)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais E0
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E0 r a g fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval #Hval'".
    iIntros "Hsts Ha Hown Hcls HPC Hmap".
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
        iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; auto. }
      { destruct (H3 r1) as [wr1 Hsomer1].
        iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
        { rewrite lookup_delete_ne; eauto. }
        iApply (wp_jnz_success_jmpPC2 with "[HPC Hr1 Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr1)".
        iApply wp_pure_step_later; auto. iNext.
        iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
        iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
        rewrite -delete_insert_ne; auto.
        destruct (updatePcPerm wr1) eqn:Heq.
        { iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. }
        { destruct c,p,p,p.
          destruct p.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            (* use fundamental_RWX in some way ? *) admit.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            (* use fundamental_RWLX in some way ? *) admit. } }
    * destruct (H3 r2) as [wr2 Hsomer2].
      iDestruct ((big_sepM_delete _ _ r2) with "Hmap") as "[Hr2 Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      case_eq (nonZero wr2); intros.
      { assert (wr2 <> inl 0%Z) by (intro; subst wr2; cbv in H4; congruence).
        destruct (reg_eq_dec PC r1).
        - subst r1. iApply (wp_jnz_success_jmpPC1 with "[HPC Hr2 Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r2); auto.
          iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; auto.
        - destruct (reg_eq_dec r2 r1).
          + subst r1. iApply (wp_jnz_success_jmp2 with "[HPC Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr2)".
            iApply wp_pure_step_later; auto. iNext.
            simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r2); auto.
            iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            destruct (updatePcPerm wr2) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWX in some way ? *) admit.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWLX in some way ? *) admit. }
          + destruct (H3 r1) as [wr1 Hsomer1].
            iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
            { repeat rewrite lookup_delete_ne; eauto. }
            iApply (wp_jnz_success_jmp with "[HPC Hr1 Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr1 & Hr2)".
            iApply wp_pure_step_later; auto. iNext.
            simpl. iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            repeat rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r1); auto.
            iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto. rewrite (insert_id r r2); auto.
            iMod ("Hcls" with "[Ha $Hown]") as "Hcls'"; auto.
            destruct (updatePcPerm wr1) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWX in some way ? *) admit.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWLX in some way ? *) admit. } }
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
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; auto.
        - iApply (wp_jnz_fail_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate. }
      Admitted. 

End fundamental.