From cap_machine Require Export logrel monotone.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Lemma RX_Jnz_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (r1 r2: RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Jnz r1 r2),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r2).
    * subst r2.
      destruct (reg_eq_dec PC r1).
      { subst r1. iApply (wp_jnz_success_jmpPC with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha)".
        simpl. iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        iApply wp_pure_step_later; auto. iNext.
        iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                       "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. iFrame "#". }
        iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
        { iNext. iDestruct "Hregion" as "[$ _]". 
          iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
        iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto. }
      { destruct (H3 r1) as [wr1 Hsomer1].
        iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
        { rewrite lookup_delete_ne; eauto. }
        iApply (wp_jnz_success_jmpPC2 with "[HPC Hr1 Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr1)".
        iApply wp_pure_step_later; auto. iNext.
        iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                       "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. auto. }
        iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
        rewrite -delete_insert_ne; auto.
        iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
        { iNext. iDestruct "Hregion" as "[$ _]". 
          iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
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
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iFrame "#". }
          iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
          { iNext. iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto.
        - destruct (reg_eq_dec r2 r1).
          + subst r1. iApply (wp_jnz_success_jmp2 with "[HPC Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr2)".
            iApply wp_pure_step_later; auto. iNext.
            simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r2); auto.
            iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                           "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. iFrame "#". }
            iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
            { iNext. iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
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
            iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                           "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. iFrame "#". }
            iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
            { iNext. iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
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
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
          { iExists w. rewrite H5. iFrame. iFrame "#". }
          iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
          { iNext. iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto.
        - iApply (wp_jnz_fail_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate. }
  Admitted.

End fundamental.