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

  Lemma RX_Load_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (src: RegName)
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
      (Hi : cap_lang.decode w = Load dst src),
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
    destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
    * (* Load PC PC ==> fail *)
      iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      iApply wp_value.
      iNext. iIntros "%"; inversion a0.
    * (* Load PC src ==> success if src ↦ inr, fail o/w *)
      simpl in H3. 
      specialize H3 with src as Hsrc. 
      destruct Hsrc as [wsrc Hsomesrc]. 
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete.
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros "%"; inversion a0.  
      } 
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p && withinBounds ((p,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros "%"; inversion a3. 
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n0
        as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge]. 
      (* get validity of capability in src from Hreg *)
      apply reg_eq_sym in n. 
      iDestruct ("Hreg" $! src n) as "Hvsrc". 
      rewrite /RegLocate Hsomesrc.
      iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
      (* Each condition in Hconds take a step in similar fashion *)
      rewrite /read_write_cond. 
      iAssert ((∃ w', ▷ (a0 ↦ₐ w' ∗ a ↦ₐ w
                         ={⊤}=∗ na_own logrel_nais E)
                        ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,fr)
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
                 ∗ sts_full fs fr
                 -∗ WP Instr Executable
                 {{ v, WP fill [SeqCtx] (of_val v)
                          {{ v0, ⌜v0 = HaltedV⌝
                                 → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                                 full_map r0
                                 ∧ registers_mapsto r0
                                                    ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                    ∗ na_own logrel_nais E
                                                    ∗ sts_full fs' fr' }} }} )%I
                                                               with "[Ha HPC Hsrc Hmap]" as "Hstep".
      {
        iIntros "(Hw0 & Hsts)".
        iDestruct "Hw0" as (w0) "(Hcls' & Ha0 & #Hw0)".
        (* iDestruct "Hsub" as (E') "#[Hns Hsub]".  *)
        iAssert (∀ w1 w2, full_map (<[PC:=w1]> (<[src:=w2]> r)))%I as "#Hfull".
        { iIntros (w1 w2 r0).
          iPureIntro.
          destruct (decide (PC = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
          rewrite lookup_insert_ne.
          destruct (decide (src = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
          rewrite lookup_insert_ne. apply H3. done. done.
        }
        destruct w0.
        { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]"); eauto.
          - split; apply Is_true_eq_true; eauto.
            apply andb_prop_intro. split; [apply Hle|apply Hge].
          - iFrame.
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a3. 
        }
        destruct c,p0,p0,p0.
        destruct ((a3 + 1)%a) eqn:Ha0.
        2: { (* If src points to top address, load crashes *)
          iApply (wp_load_fail4 with "[HPC Hsrc Ha Ha0]"); eauto.
          - split; apply Is_true_eq_true; eauto.
            apply andb_prop_intro. split; [apply Hle|apply Hge].
          - iFrame.
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a6. 
        }
        (* successful load into PC *)
        iApply (wp_load_success_PC with "[HPC Ha Hsrc Ha0]"); eauto.
        - split; apply Is_true_eq_true; eauto.
          apply andb_prop_intro. split; [apply Hle|apply Hge].
        - iFrame.
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iAssert (⌜p0 ≠ RX⌝ ∧ ⌜p0 ≠ RWX⌝ ∧ ⌜p0 ≠ RWLX⌝ →
                   PC ↦ᵣ inr (p0, l0, a5, a4, a6) -∗
                      WP Seq (Instr Executable) {{ w, ⌜w = FailedV⌝
                                                                  ∗ PC ↦ᵣ inr (p0, l0, a5, a4, a6) }})%I
            as "Hfail".
          { iIntros "(% & % & %) HPC".
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "[HPC]");
              [apply not_isCorrectPC_perm; eauto|iFrame|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iFrame. done.
          }
          (* The new register state is valid *)
          iAssert (interp_registers _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)) as "[Hfull' Hreg']".
          { iSplitL.
            { iIntros (r0). iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
            iIntros (r0) "%".
            destruct (decide (src = r0)); simplify_eq.
            + by rewrite /RegLocate lookup_insert.
            + rewrite /RegLocate lookup_insert_ne; auto.
              iDestruct ("Hreg" $! (r0) a7) as "Hr0".
              specialize H3 with r0.
              destruct H3 as [c Hsome].
              rewrite Hsome. iApply "Hr0"; auto.
          }
          destruct p0;
            [iAssert (⌜O ≠ RX⌝ ∧ ⌜O ≠ RWX⌝ ∧ ⌜O ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RO ≠ RX⌝ ∧ ⌜RO ≠ RWX⌝ ∧ ⌜RO ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RW ≠ RX⌝ ∧ ⌜RW ≠ RWX⌝ ∧ ⌜RW ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RWL ≠ RX⌝ ∧ ⌜RWL ≠ RWX⌝ ∧ ⌜RWL ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)| |
             iAssert (⌜cap_lang.E ≠ RX⌝ ∧ ⌜cap_lang.E ≠ RWX⌝ ∧ ⌜cap_lang.E ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)| | ];
            try ( iDestruct ("Hfail" with "Htrivial HPC") as "Hfail";
                  iApply (wp_wand with "Hfail");
                  iAssert ((∀ v : val cap_lang, ⌜v = FailedV⌝
                                                            ∗ PC ↦ᵣ inr (_, l0, a5, a4, a6)
                                                            -∗ ⌜v = HaltedV⌝
                                                → ∃ (r0 : Reg) fs' fr',
                                 full_map r0 ∧ registers_mapsto r0 ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                                ∗ na_own logrel_nais E
                                                                ∗ sts_full fs' fr'))%I
                    with "[Hmap Hsrc Hsts]" as "Hfailed";
                  [ iIntros (v) "[-> HPC]";
                    iDestruct ((big_sepM_delete _ _ src)
                                 with "[Hsrc Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                    rewrite -delete_insert_ne; auto;
                    iDestruct ((big_sepM_delete _ _ PC)
                                 with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                    iIntros "%"; inversion a7
                   |];iFrame);
            try (iNext;iDestruct ("Hfail" with "Htrivial HPC") as "Hfail"; 
                 iApply wp_wand_l;iFrame;iIntros (v) "[-> HPC] %";inversion a7).
          { (* new PC is RX ==> apply IH*)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            (* apply IH *)
            iNext.
            rewrite (fixpoint_interp1_eq _ _ (inr (RX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7 ws1) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iApply ("IH" $! _ _ _ _ _ _ _ ws1
                      with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hown]");
              iFrame; iFrame "#".
            iAlways. iPureIntro. by intros ns Hns; inversion Hns.  
          } 
          { (* new PC is RWX, apply fundamental_RWX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            iNext.
            rewrite (fixpoint_interp1_eq _ _ (inr (RWX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iDestruct (fundamental_RWX _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)
                         with "Hb0e0") as "Hexpr"; eauto.
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown]")
              as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame.
            iFrame. 
            iPureIntro. by intros ns Hns; inversion Hns.  
          }
          { (* new PC is RWLX, apply fundamental_RWLX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            rewrite (fixpoint_interp1_eq _ _ (inr (RWLX, l0, a5, a4, a3))).
            iNext.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iDestruct (fundamental_RWLX _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)
                         with "Hb0e0") as "Hexpr"; eauto.
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown]")
              as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame.
            iFrame. 
            iPureIntro. by intros ns Hns; inversion Hns.  
          }
      }

      destruct (decide ((b,e) = (a2,a1))).
      {
        inversion e0; subst.
        (* no need to open any invariant, in this case we need to do cases on 
               a = a0. if a = a0, then the program should crash, since we will not 
               be able to increment w once loaded into PC. Otherwise we just do as 
               below, except we don't need to open the invariant, we just destruct the 
               region a0 is in (either in Hregionl or Hregionh). *)
        admit. 
      }
      iDestruct "Hconds" as "[[#Hro|#[Hrw|Hrwl]] %]".
      (* each condition is similar, but with some subtle differences for closing *)
      { iDestruct "Hro" as (ws0) "#Hinv0".
        (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hinv0 Hown") as "[Hro_cond [Hown' Hcls']]"; auto. 
        rewrite /read_only_cond.
        iDestruct "Hro_cond" as "[Ha2a1 #Hro_cond]".
        iDestruct ("Hro_cond" $! (fs,fr) E) as "Hro_cond'".
        iCombine "Ha2a1 Hro_cond'" as "Hregion". 
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 Hva0". 
        iNext. iIntros "[Ha0 Ha]".
        iMod ("Hcls'" with "[Hown' Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame. 
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrw Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #".
            iDestruct (big_sepL_sepL with "Hrw_cond") as "[$ _]". 
          }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrwl Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
    * destruct (H3 dst) as [wdst Hsomedst].
      rewrite delete_insert_delete.
      assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
      { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto. 
      destruct (a + 1)%a eqn:Ha'. 
      2: { (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        iApply (wp_load_fail6 with "[HPC Hdst Ha]"); eauto.
        iFrame. iNext. iIntros "[HPC [Ha Hdst]] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto.
        iNext. 
        iIntros (Hcontr); inversion Hcontr. 
      }
      (* if PC can be incremented, load succeeds ==> apply IH *)
      iApply (wp_load_success_fromPC with "[HPC Hdst Ha]"); eauto.
      iFrame.
      iNext. iIntros "[HPC [Ha Hdst]] /=".
      iApply wp_pure_step_later; auto.
      (* we want to apply IH on the updated register state *)
      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
        rewrite -delete_insert_ne; auto;
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
      (* apply IH *)
      iAssert (▷ interp_registers _ (fs, fr) (<[dst:=w]> r))%I
        as "[Hfull Hreg']".
      { iNext. iSplitL.
        { iIntros (r0). iPureIntro.
          destruct (decide (dst = r0)); simplify_eq;
            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
        iIntros (r0) "%".
        destruct (decide (dst = r0)); simplify_eq.
        + by rewrite /RegLocate lookup_insert.
        + rewrite /RegLocate lookup_insert_ne; auto.
          iDestruct ("Hreg" $! (r0) a1) as "Hr0".
          specialize H3 with r0. 
          destruct H3 as [c Hsome].
          rewrite Hsome. iApply "Hr0"; auto.
      }
      iNext.
      iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
      { iNext.
        iDestruct (extract_from_region' _ _ a _
                                        (((fixpoint interp1) E) (fs, fr))
                     with "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
        { iExists _. iFrame. rewrite Ha'. iFrame "∗ #". }
        iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
      iApply ("IH" with "Hfull Hreg' Hmap Hsts Hown").
      iExact "Hinv". auto. 
    * destruct (H3 src) as [wsrc Hsomesrc].
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete. 
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      } 
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p && withinBounds ((p,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext.
          iIntros (Hcontr); inversion Hcontr. 
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n1
        as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge].
      (* the contents of src is valid *)
      iAssert ((fixpoint interp1) _ _ (inr (p, l, a2, a1, a0))) as "#Hvsrc".
      { apply reg_eq_sym in n0. iDestruct ("Hreg" $! src n0) as "Hvsrc".
        rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
      iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
      (* Each condition in Hconds take a step in similar fashion *)
      iAssert ((∃ w', ▷ (a0 ↦ₐ w' ∗ a ↦ₐ w
                         ={⊤}=∗ na_own logrel_nais E)
                        ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,fr)
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
                 ∗ sts_full fs fr
                 -∗ WP Instr Executable
                 {{ v, WP fill [SeqCtx] (of_val v)
                          {{ v0, ⌜v0 = HaltedV⌝
                                 → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                                 full_map r0
                                 ∧ registers_mapsto r0
                                                    ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                    ∗ na_own logrel_nais E
                                                    ∗ sts_full fs' fr' }} }} )%I
                                                               with "[Ha HPC Hsrc Hmap]" as "Hstep".
      { iIntros "[Hcls' Hsts]". iDestruct "Hcls'" as (w0) "[Hcls' [Ha0 #Hw0]]". 
        (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        destruct (a + 1)%a eqn:Ha'; simplify_eq.
        2: { destruct (decide (src = dst)); simplify_eq. 
             - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]"); eauto.
               { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
               iFrame. iNext. iIntros "[HPC [Ha [Hdst Ha0]]] /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
             - destruct (H3 dst) as [wdst Hsomedst].
               assert (delete PC r !! dst = Some wdst) as Hsomedst'.
               { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
               assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
               { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
                 eauto. }
               iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
                 eauto.
               iApply (wp_load_fail7 with "[HPC Hsrc Hdst Ha Ha0]"); eauto.
               { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
               iFrame. iNext. iIntros "(HPC & Ha & Hsrc & Ha0 & Hdst) /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
        }
        (* two successful steps: loading to a fresh dst, and loading to src *)
        destruct (decide (src = dst)); simplify_eq.
        - iApply (wp_load_success_same with "[HPC Hsrc Ha Ha0]"); eauto.
          { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
          iFrame. iNext. iIntros "(HPC & Hdst & Ha & Ha0) /=".
          iApply wp_pure_step_later; auto. 
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
            rewrite -delete_insert_ne; auto;
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers _ _ (<[dst:=w0]> r))%I as "[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              iPureIntro.
              destruct (H3 r0) as [c Hsome]. 
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "% /=".
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (H3 r0) as [c Hsome]. 
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. iApply "Hw0". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. iApply "Hv"; auto.  
          }
          iNext.
          iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
          iApply ("IH" with "Hfull' Hreg' Hmap Hsts Hown"); auto. 
        - destruct (H3 dst) as [wdst Hsomedst].
          assert (delete PC r !! dst = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
          { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
            eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
            eauto.
          iApply (wp_load_success with "[HPC Hsrc Hdst Ha Ha0]"); eauto.
          { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
          iFrame. iNext. iIntros "(HPC & Hdst & Ha & Hsrc & Ha0) /=".
          iApply wp_pure_step_later; auto. 
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
            rewrite -delete_insert_ne; auto;
              iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete|].
          rewrite -delete_insert_ne; auto. iFrame. 
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers _ _ (<[src:=inr (p, l, a2, a1, a0)]> (<[dst:=w0]> r)))%I
            as "[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              destruct (H3 r0) as [c Hsome].
              iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "%".
              destruct (H3 r0) as [c Hsome].
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (decide (src = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. iApply "Hvsrc". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                * by rewrite lookup_insert.
                * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                  auto. 
          }
          iNext.
          iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
          iApply ("IH" with "Hfull' Hreg' Hmap Hsts Hown"); auto. 
      }
      destruct (decide ((b,e) = (a2,a1))).
      {
        inversion e0; subst. 
        (* no need to open any invariant *)
        admit. 
      }
      iDestruct "Hconds" as "[[#Hro|#[Hrw|Hrwl]] %]".
      (* each condition is similar, but with some subtle differences for closing *)
      { iDestruct "Hro" as (ws0) "#Hinv0".
        (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hinv0 Hown") as "[Hro_cond [Hown' Hcls']]"; auto. 
        rewrite /read_only_cond.
        iDestruct "Hro_cond" as "[Ha2a1 #Hro_cond]".
        iDestruct ("Hro_cond" $! (fs,fr) E) as "Hro_cond'".
        iCombine "Ha2a1 Hro_cond'" as "Hregion". 
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 Hva0". 
        iNext. iIntros "[Ha0 Ha]".
        iMod ("Hcls'" with "[Hown' Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame. 
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrw Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #".
            iDestruct (big_sepL_sepL with "Hrw_cond") as "[$ _]". 
          }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrwl Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
  Admitted.

End fundamental.