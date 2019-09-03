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

  Lemma interp_cap_preserved E fs fr p l a2 a1 a0 a3 (Hne: p <> cap_lang.E):
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a0)) -∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a3)).
  Proof.
    repeat rewrite fixpoint_interp1_eq. simpl. iIntros "HA".
    destruct p; auto.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
    - elim Hne; reflexivity.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3. iFrame; auto.
  Qed.

  Lemma RX_Lea_case:
    ∀ E0 r a g fs fr b e p' w dst r0 
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
      (Hi : cap_lang.decode w = cap_lang.Lea dst r0),
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
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (a + z)%a; intros.
        * case_eq (a0 + 1)%a; intros.
           { iApply (wp_lea_success_z_PC with "[HPC Ha]"); eauto; iFrame.
             iNext. iIntros "(HPC & Ha)".
             iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
               [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
             (* iDestruct (extract_from_region' _ _ a with *)
             (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
             (* { iExists _. iFrame "∗ #". } *)
             iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
             { iFrame. iNext. iExists _. iFrame. auto. }
             iApply wp_pure_step_later; auto.
             iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto.  }
           { iApply (wp_lea_failPC1' with "[HPC Ha]"); eauto; iFrame.
             iNext. iIntros.  iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate. }
         * iApply (wp_lea_failPC1 with "[HPC Ha]"); eauto; iFrame.
           iNext. iIntros. iApply wp_pure_step_later; auto.
           iNext. iApply wp_value; auto. iIntros; discriminate. }
       { destruct (H3 r0) as [wr0 Hsomer0].
         destruct (reg_eq_dec PC r0).
         - subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
           iNext. iIntros. iApply wp_pure_step_later; auto.
           iNext. iApply wp_value; auto. iIntros; discriminate.
         - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
           repeat rewrite lookup_delete_ne; eauto.
           destruct wr0.
           + case_eq (a + z)%a; intros.
             * case_eq (a0 + 1)%a; intros.
               { iApply (wp_lea_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                 iNext. iIntros "(HPC & Ha & Hr0)".
                 iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
                 { iFrame. iNext. iExists _. iFrame. auto. }
                 iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                 iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto.  }
               { iApply (wp_lea_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                 iNext. iIntros.  iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate. }
     * destruct (H3 dst) as [wdst Hsomedst].
       iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
       rewrite lookup_delete_ne; eauto.
       destruct wdst.
       { iApply (wp_lea_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
         iNext. iIntros. iApply wp_pure_step_later; auto.
         iNext. iApply wp_value; auto. iIntros; discriminate. }
       { destruct c, p, p, p.
         destruct (perm_eq_dec p cap_lang.E).
         - subst p. destruct r0.
           + iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_fail3 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
         - destruct r0.
           + case_eq (a0 + z)%a; intros.
             * case_eq (a + 1)%a; intros.
               { iApply (wp_lea_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros "(HPC & Ha & Hdst)".
                 iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 repeat rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iMod ("Hcls" with "[Ha Hown]") as "Hcls'". 
                 { iFrame. iNext. iExists _. iFrame. auto. }
                 iApply wp_pure_step_later; auto.
                 iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> r)))%I
                   as "[Hfull' Hreg']".
                 { iSplitL.
                   - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                   - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                     + subst r2. rewrite /RegLocate lookup_insert.
                       iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                       simpl. iApply (interp_cap_preserved with "HA"); auto.
                     + rewrite /RegLocate lookup_insert_ne; auto.
                       iApply "Hreg"; auto. }
                 iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
               { iApply (wp_lea_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + destruct (H3 r0) as [wr0 Hsomer0].
             destruct (reg_eq_dec PC r0).
             * subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
             * destruct (reg_eq_dec dst r0).
               { subst r0. iApply (wp_lea_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
               { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                 repeat rewrite lookup_delete_ne; eauto.
                 destruct wr0.
                 - case_eq (a0 + z)%a; intros.
                   * case_eq (a + 1)%a; intros.
                     { revert H4; intro H4.
                       iApply (wp_lea_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                       iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                       iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
                       { iFrame. iNext. iExists _. iFrame. auto. }
                       iApply wp_pure_step_later; auto.
                       iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> (<[r0:=inl z]> r))))%I
                         as "[Hfull' Hreg']".
                       { iSplitL.
                         - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                           destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                         - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                           + subst r2. rewrite /RegLocate lookup_insert.
                             iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                             simpl. iApply (interp_cap_preserved with "HA"); auto.
                           + rewrite /RegLocate lookup_insert_ne; auto.
                             destruct (reg_eq_dec r0 r2).
                             * subst r2; rewrite lookup_insert. simpl.
                               repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                             * rewrite lookup_insert_ne; auto.
                               iApply "Hreg"; auto. }
                       iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                     { iApply (wp_lea_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                       iNext. iIntros. iApply wp_pure_step_later; auto.
                       iNext. iApply wp_value; auto. iIntros; discriminate. }
                   * iApply (wp_lea_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value; auto. iIntros; discriminate.
                 - iApply (wp_lea_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Qed. 
       

(*
  Lemma RWX_Lea_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (r0: Z + RegName)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Lea dst r0),
      □ ▷ ▷ ⌜isLocalWord w = false⌝
                                  -∗ □ ▷ ▷ ((interp E0) (fs, fr)) w
                                  -∗ □ ▷ ▷ ([∗ list] w0 ∈ ws, ⌜isLocalWord w0 = false⌝)
                                  -∗ □ ▷ ▷ ([∗ list] w0 ∈ ws, ((interp E0) (fs, fr)) w0)
                                  -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ (((interp E0) (fs, fr)) w0 ∗ ⌜isLocalWord w0 = false⌝))
                                  -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                                                 (((interp E1) stsf) w0 ∗ ⌜isLocalWord w0 = false⌝))
                                  -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
                                  -∗ □ na_inv logrel_nais (logN.@(b, e))
                                  (∃ ws0 : list Word, [[b,e]]↦ₐ[[ws0]]
                                                             ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                  (E1 : leibnizC coPset), [∗ list] w0 ∈ ws0, ▷ 
                                                                                                               (((interp E1) stsf) w0 ∗ ⌜isLocalWord w0 = false⌝)))
                                  -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                                            (a4 : leibnizC STS_rels) (a5 a6 : Addr), full_map a0
                                                                                              -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝
                                                                                                                  → 
                                                                                                                  (((fixpoint interp1) E0)
                                                                                                                     (a3, a4)) 
                                                                                                                    (a0 !r! r0))
                                                                                              -∗ registers_mapsto
                                                                                              (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
                                                                                              -∗ sts_full a3 a4
                                                                                              -∗ na_own logrel_nais E0
                                                                                              -∗ □ na_inv logrel_nais
                                                                                              (logN.@(a5, a6))
                                                                                              (∃ ws0 : list Word, 
                                                                                                  [[a5,a6]]↦ₐ[[ws0]]
                                                                                                           ∗ 
                                                                                                           (∀ (stsf : 
                                                                                                                 prodC 
                                                                                                                   (leibnizC STS_states)
                                                                                                                   (leibnizC STS_rels)) 
                                                                                                              (E1 : 
                                                                                                                 leibnizC coPset), [∗ list] w0 ∈ ws0, ▷ 
                                                                                                                                                        (((interp E1) stsf) w0
                                                                                                                                                                            ∗ ⌜
                                                                                                                                                                            isLocalWord w0 = false⌝)))
                                                                                              -∗ □ ⌜∀ ns : namespace, 
                                            Some (logN.@(a5, a6)) = Some ns
                                            → ↑ns ⊆ E0⌝ -∗ 
                                               ⟦ [a3, a4, E0] ⟧ₒ)
                                  -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RWX, g, b, e, a)]> r), k ↦ᵣ y)
                                  -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
                                  -∗ ▷ match (a + 1)%a with
                                       | Some ah =>
                                         [[ah,e]]↦ₐ[[drop
                                                       (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))))
                                                       ws]]
                                       | None =>
                                         ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
                                       end
                                  -∗ a ↦ₐ w
                                  -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                                                        (length
                                                                                           (region_addrs b
                                                                                                         (get_addr_from_option_addr
                                                                                                            (a + -1)%a))) ws]])
                                  -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w
           :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))))
           ws⌝
           -∗ (▷ (∃ ws0 : list Word, [[b,e]]↦ₐ[[ws0]]
                                            ∗ (∀ (stsf : prodC (leibnizC STS_states)
                                                               (leibnizC STS_rels)) 
                                                 (E1 : leibnizC coPset), [∗ list] w0 ∈ ws0, ▷ 
                                                                                              (((interp E1) stsf) w0 ∗ ⌜isLocalWord w0 = false⌝)))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ 
                                                               na_own logrel_nais E0)
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
    iIntros "#Hva2 #Hva1 #Hval2 #Hval1 #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (a + z)%a; intros.
        * case_eq (a0 + 1)%a; intros.
          { iApply (wp_lea_success_z_PC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            (* iDestruct (extract_from_region' _ _ a with *)
            (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
            (* { iExists _. iFrame "∗ #". } *)
            iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
            { iNext.
              iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                             "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
              { iExists w. iFrame "∗ #". }
              iExists ws. iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
            }
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto. }
          { iApply (wp_lea_failPC1' with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros.  iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
        * iApply (wp_lea_failPC1 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (H3 r0) as [wr0 Hsomer0].
        destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          repeat rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + case_eq (a + z)%a; intros.
            * case_eq (a0 + 1)%a; intros.
              { iApply (wp_lea_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                { iNext.
                  iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                 "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                  { iExists w. iFrame "∗ #". }
                  iExists ws. iDestruct "Hregion" as "[$ _]". 
                  iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                }
                iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto. }
              { iApply (wp_lea_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros.  iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_lea_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_lea_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
      rewrite lookup_delete_ne; eauto.
      destruct wdst.
      { iApply (wp_lea_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c, p, p, p.
        destruct (perm_eq_dec p cap_lang.E).
        - subst p. destruct r0.
          + iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_lea_fail3 with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate.
        - destruct r0.
          + case_eq (a0 + z)%a; intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_lea_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hdst)".
                iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                { iNext.
                  iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                 "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                  { iExists _. rewrite H5; iFrame "∗ #". }
                  iExists ws. iDestruct "Hregion" as "[$ _]". 
                  iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                }
                iApply wp_pure_step_later; auto.
                iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> r)))%I
                  as "[Hfull' Hreg']".
                { iSplitL.
                  - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                  - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                    + subst r2. rewrite /RegLocate lookup_insert.
                      iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                      simpl. iApply (interp_cap_preserved with "HA"); auto.
                    + rewrite /RegLocate lookup_insert_ne; auto.
                      iApply "Hreg"; auto. }
                iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
              { iApply (wp_lea_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (H3 r0) as [wr0 Hsomer0].
            destruct (reg_eq_dec PC r0).
            * subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (reg_eq_dec dst r0).
              { subst r0. iApply (wp_lea_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wr0.
                - case_eq (a0 + z)%a; intros.
                  * case_eq (a + 1)%a; intros.
                    { revert H4; intro H4.
                      iApply (wp_lea_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                      { iNext.
                        iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                       "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                        { iExists _. rewrite H5; iFrame "∗ #". }
                        iExists ws. iDestruct "Hregion" as "[$ _]". 
                        iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                      }
                      iApply wp_pure_step_later; auto.
                      iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> (<[r0:=inl z]> r))))%I
                        as "[Hfull' Hreg']".
                      { iSplitL.
                        - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                          destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                        - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                          + subst r2. rewrite /RegLocate lookup_insert.
                            iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                            simpl. iApply (interp_cap_preserved with "HA"); auto.
                          + rewrite /RegLocate lookup_insert_ne; auto.
                            destruct (reg_eq_dec r0 r2).
                            * subst r2; rewrite lookup_insert. simpl.
                              repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                            * rewrite lookup_insert_ne; auto.
                              iApply "Hreg"; auto. }
                      iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                    { iApply (wp_lea_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  * iApply (wp_lea_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_lea_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Qed.*)

End fundamental.