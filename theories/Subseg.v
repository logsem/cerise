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

  Lemma RX_Subseg_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (r1 r2: Z + RegName)
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
      (Hi : cap_lang.decode w = Subseg dst r1 r2),
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
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r1.
      { case_eq (z_to_addr z); intros.
        - destruct r2.
          + case_eq (z_to_addr z0); intros.
            * case_eq (isWithin a0 a1 b e); intros.
              { case_eq (a+1)%a; intros.
                - (* success case *) admit.
                - (* fail, can't increase PC *) admit. }
              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha]"); iFrame; try (iSplitR; auto).
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (reg_eq_dec PC r0).
            * subst r0.
              iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
              destruct wr0.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * (* success case *) admit.
                    * (* fail, can't increase PC *) admit.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
        - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha]"); iFrame; auto.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
          destruct wr0.
          + case_eq (z_to_addr z); intros.
            * destruct r2.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * (* success case *) admit.
                    * (* fail, can't increase PC *) admit.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { destruct (reg_eq_dec PC r1).
                - subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - destruct (reg_eq_dec r0 r1).
                  + subst r1. case_eq (isWithin a0 a0 b e); intros.
                    * case_eq (a+1)%a; intros.
                      { (* success case *) admit. }
                      { (* fail, can't increment PC *) admit. }
                    * iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H4 H5 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence. auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + destruct (H3 r1) as [wr1 Hsomer1].
                    iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                    destruct wr1.
                    * case_eq (z_to_addr z0); intros.
                      { case_eq (isWithin a0 a1 b e); intros.
                        - case_eq (a+1)%a; intros.
                          + (* success case *) admit.
                          + (* fail, can't increment PC *) admit.
                        - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hr1]"); iFrame; try (iSplitL; auto). destruct (reg_eq_dec r0 r1); try congruence; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                      { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr1]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr1]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha Hr0]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC dst); eauto|].
      destruct wdst.
      { iApply (wp_subseg_fail_dst_z _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c,p,p,p. destruct r1.
        - case_eq (z_to_addr z); intros.
          + destruct r2.
            * case_eq (z_to_addr z0); intros.
              { case_eq (isWithin a3 a4 a2 a1); intros.
                - case_eq (a+1)%a; intros.
                  + (* success case *) admit.
                  + (* fail case, can't increment PC *) admit.
                - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * destruct (reg_eq_dec PC r0).
              { subst r0. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { destruct (reg_eq_dec dst r0).
                - subst r0. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                  destruct wr0.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - (* success case *) admit.
                        - (* fail case, can't increment PC *) admit. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
          + (* fail case, can't convert z *) admit.
        - destruct (reg_eq_dec PC r0).
          + subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
              destruct wr0.
              { case_eq (z_to_addr z); intros.
                - destruct r2.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - (* success case *) admit.
                        - (* fail case, can't increment PC *) admit. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + destruct (reg_eq_dec PC r1).
                    * subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                    * destruct (reg_eq_dec dst r1).
                      { subst r1. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                      { destruct (reg_eq_dec r0 r1).
                        - subst r1. case_eq (isWithin a3 a3 a2 a1); intros.
                          + case_eq (a+1)%a; intros.
                            * (* success case *) admit.
                            * (* fail case, can't increment PC *) admit.
                          + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H4 H5 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence; auto.
                            destruct (reg_eq_dec PC dst); try congruence; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate.
                        - destruct (H3 r1) as [wr1 Hsomer1].
                          iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                          destruct wr1.
                          + case_eq (z_to_addr z0); intros.
                            * case_eq (isWithin a3 a4 a2 a1); intros.
                              { case_eq (a+1)%a; intros.
                                - (* success case *) admit.
                                - (* fail case, can't increment PC *) admit. }
                              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hr1 Hdst]"); iFrame. iSplitL "Hr1". destruct (reg_eq_dec r0 r1); try congruence; auto.
                                destruct (reg_eq_dec PC dst); try congruence; auto.
                                iNext. iIntros. iApply wp_pure_step_later; auto.
                                iNext. iApply wp_value; auto. iIntros; discriminate. }
                            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0 Hr1]"); iFrame; auto.
                              iNext. iIntros. iApply wp_pure_step_later; auto.
                              iNext. iApply wp_value; auto. iIntros; discriminate.
                          + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr1]"); iFrame; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Admitted.

End fundamental.