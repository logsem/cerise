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

  Lemma RX_Load_case:
    ∀ r a g M fs fr b e p' w dst src
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
      (Hi : cap_lang.decode w = cap_lang.Load dst src)
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
      apply (not_false_is_true (_ && _)),andb_prop in n0
        as [Hra Hwb]. apply andb_prop in Hwb as [Hle Hge].
      rewrite /leb_addr in Hle,Hge. 
      (* get validity of capability in src from Hreg *)
      apply reg_eq_sym in n. 
      iDestruct ("Hreg" $! src n) as "Hvsrc". 
      rewrite /RegLocate Hsomesrc.
      iDestruct (read_allowed_inv a0 with "Hvsrc") as "Hconds"; auto; 
        first (split; by apply Z.leb_le).        
      (* Each condition in Hconds take a step in similar fashion *)
      destruct (decide (a = a0)).
      {
        subst. 
        (* no need to open any invariant, in this case we need to do cases on 
           a = a0. if a = a0, then the program should crash, since we will not 
           be able to increment w once loaded into PC. *)
        iApply (wp_load_fail5 with "[HPC Ha Hsrc]"); try iFrame; auto. 
        - apply PermFlows_refl.
        - split;auto. apply andb_true_iff. split; auto.
        - destruct (a0 =? a0)%a eqn:Hcontr; first done.
          rewrite /eqb_addr Z.eqb_refl in Hcontr; inversion Hcontr. 
        - iNext. iIntros "(_ & _ & _ & _) /=".
          iApply wp_pure_step_later;[auto|]. iNext.
          iApply wp_value. iIntros (Hcontr); inversion Hcontr.  
      }
      rewrite /read_write_cond. 
      iAssert ((∃ w' p'', ▷ ( a0 ↦ₐ[p''] w'
                               ∗ a ↦ₐ[p'] w
               ={⊤}=∗ na_own logrel_nais ⊤)
                            ∗ ▷ a0 ↦ₐ[p''] w'
                            ∗ ▷ ▷ ⟦ w' ⟧ ∗ ⌜PermFlows p p''⌝
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
        ∗ sts_full fs fr
        -∗ WP Instr Executable
       {{ v, WP fill [SeqCtx] (of_val v)
                {{ v0, ⌜v0 = HaltedV⌝
                  → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                       full_map r0
                       ∧ registers_mapsto r0
                                          ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                          ∗ na_own logrel_nais ⊤
                                          ∗ sts_full fs' fr' }} }} )%I
        with "[Ha HPC Hsrc Hmap HM]" as "Hstep".
      {
        iIntros "(Hw0 & Hsts)".
        iDestruct "Hw0" as (w0 p'') "(Hcls' & Ha0 & #Hw0 & %)".
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
        { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]")
          ;[eauto|apply Hfp|apply H4| | | | |]; eauto. 
          - split; [eauto|]. apply Is_true_eq_true; eauto.
            apply andb_prop_intro.
            split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
          - destruct (a0 =? a)%a; iFrame. 
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a3. 
        }
        destruct c,p0,p0,p0.
        destruct ((a3 + 1)%a) eqn:Ha0.
        2: { (* If src points to top address, load crashes *)
          iApply (wp_load_fail4 with "[HPC Hsrc Ha Ha0]")
          ;[eauto|apply Hfp|apply H4| | | | | |]; eauto. 
          - split; apply Is_true_eq_true; eauto.
            apply andb_prop_intro; split;
              apply Is_true_eq_left; [apply Hle|apply Hge].
          - destruct ((a0 =? a)%a); iFrame.
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a6. 
        }
        (* successful load into PC *)
        iApply (wp_load_success_PC with "[HPC Ha Hsrc Ha0]")
        ;[eauto|apply Hfp|apply H4| | | | |]; eauto. 
        - split; apply Is_true_eq_true; eauto.
          apply andb_prop_intro; split;
            apply Is_true_eq_left; [apply Hle|apply Hge].
        - destruct (a0 =? a)%a; iFrame.
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
          iAssert (interp_registers (<[src:=inr (p, l, a2, a1, a0)]> r)) as "[Hfull' Hreg']".
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
            rewrite (fixpoint_interp1_eq (inr (RX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (g0 b0 e0 a7) "(% & Hw0)".
            iDestruct "Hw0" as (p0 Hfp0) "[Hb0e0 Hexec]".   
            inversion H5;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown".
            destruct Heq as [-> ->]. 
            iApply ("IH" $! _ _ _ _ _ _ _
                      with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hown]");
              iFrame; iFrame "#"; auto. 
          } 
          { (* new PC is RWX, apply fundamental_RWX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                 rewrite -delete_insert_ne; auto;
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            iNext.
            rewrite (fixpoint_interp1_eq (inr (RWX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (g0 b0 e0 a7) "(% & Hw0)".
            iDestruct "Hw0" as (p0 Hfp0) "[Hb0e0 Hexec]".   
            inversion H5;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown".
            iAssert (∃ p1 : Perm, ⌜PermFlows RWX p1⌝
                    ∧ ([∗ list] a3 ∈ region_addrs b0 e0,
                     (read_write_cond a3 p1 interp)))%I
              as "#HRWX".
            { iExists p0. iFrame "Hb0e0". auto. }
            iDestruct (fundamental_RWX (* (<[src:=inr (p, l, a2, a1, a0)]> r) *)
                         with "HRWX") as "Hexpr"; eauto.
            rewrite /interp_expression /=. 
            (* iSpecialize ("Hexpr" $! _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)).  *)
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            destruct Heq as [-> ->]. 
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown HM]")
              as (p1 g1 b1 e1 a3) "[% Ho]"; iFrame "∗ #".
          }
          { (* new PC is RWLX, apply fundamental_RWLX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                 rewrite -delete_insert_ne; auto;
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                 [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            rewrite (fixpoint_interp1_eq (inr (RWLX, l0, a5, a4, a3))).
            iNext.
            iDestruct "Hw0" as (g0 b0 e0 a7) "(% & Hw0)".
            iDestruct "Hw0" as (p0 Hfp0) "[Hb0e0 Hexec]".   
            inversion H5;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown".
            iAssert (∃ p1 : Perm, ⌜PermFlows RWLX p1⌝
                                  ∧ ([∗ list] a3 ∈ region_addrs b0 e0,
                                     (read_write_cond a3 p1 interp)))%I
              as "#HRWX".
            { iExists p0. iFrame "#". auto. }
            iDestruct (fundamental_RWLX (* (<[src:=inr (p, l, a2, a1, a0)]> r) *)
                         with "HRWX") as "Hexpr"; eauto.
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            destruct Heq as [-> ->]. 
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown HM]")
              as (p1 g1 b1 e1 a3) "[% Ho]"; iFrame "∗ #".
          }
      }
      iDestruct "Hconds" as (p'' Hp'') "Hinv0".
      (* assert (↑logN.@a0 ⊆ (E ∖ ↑logN.@a)) as Ha2a1. *)
      (* { apply subseteq_difference_r.  *)
      (*   apply ndot_ne_disjoint; auto. *)
      (*   apply H4. split; apply Z.leb_le; auto.  *)
      (* } *)
      iMod (na_inv_open with "Hinv0 Hown") as "(Ha0 & Hown' & Hcls')"; auto.
      { apply subseteq_difference_r. 
        apply ndot_ne_disjoint; auto. done. }
      iDestruct "Ha0" as (ws0) "[Ha0 #Hva0]".
      iApply "Hstep". iFrame "Hsts".
      iExists ws0. iExists _. iFrame "Ha0 Hva0".
      iSplit;[|auto]. 
      iNext. iIntros "[Ha0 Ha]".
      iMod ("Hcls'" with "[Hown' Ha0]") as "Hown";iFrame "∗ #". 
      { iNext. iExists _. iFrame. iNext. auto. }
      iMod ("Hcls" with "[Hown Ha]") as "Hown"; iFrame "∗ #".
      { iNext. iExists _. iFrame. iNext. auto. }
      iModIntro; done. 
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
        iAssert (▷ interp_registers (<[dst:=w]> r))%I
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
        iMod ("Hcls" with "[Ha Hown]") as "Hown"; auto.
        { iFrame. iNext. iExists _. iFrame. auto. }
        destruct Heq as [-> ->]. 
        iApply ("IH" with "Hfull Hreg' Hmap HM Hsts Hown");auto. 
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
      apply (not_false_is_true (_ && _)),andb_prop in n1
        as [Hra Hwb]. apply andb_prop in Hwb as [Hle Hge].
      rewrite /leb_addr in Hle,Hge. 
      (* the contents of src is valid *)
      iAssert ((fixpoint interp1) (inr (p, l, a2, a1, a0))) as "#Hvsrc".
      { apply reg_eq_sym in n0. iDestruct ("Hreg" $! src n0) as "Hvsrc".
        rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
      iDestruct (read_allowed_inv a0 with "Hvsrc") as "Hconds"; auto; 
        first (split; by apply Z.leb_le).      
      (* Each condition in Hconds take a step in similar fashion *)
      iAssert ((∃ w' p'', ▷ ((if (a0 =? a)%a then emp else a0 ↦ₐ[p''] w') ∗ a ↦ₐ[p'] w
               ={⊤}=∗ na_own logrel_nais ⊤)
                            ∗ (if (a0 =? a)%a then emp else ▷ a0 ↦ₐ[p''] w')
                            ∗ ▷ ▷ ⟦ w' ⟧ ∗ ⌜PermFlows p p''⌝
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
        ∗ sts_full fs fr
        -∗ WP Instr Executable
       {{ v, WP fill [SeqCtx] (of_val v)
                {{ v0, ⌜v0 = HaltedV⌝
                  → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                       full_map r0
                       ∧ registers_mapsto r0
                                          ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                          ∗ na_own logrel_nais ⊤
                                          ∗ sts_full fs' fr' }} }} )%I
        with "[Ha HPC Hsrc Hmap HM]" as "Hstep".
      { iIntros "[Hcls' Hsts]".
        iDestruct "Hcls'" as (w0 p'') "[Hcls' [Ha0 [#Hw0 %]]]". 
        (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        destruct (a + 1)%a eqn:Ha'; simplify_eq.
        2: { destruct (decide (src = dst)); simplify_eq. 
             - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]");
                 [eauto|eauto|apply Hfp|apply H4| | | | | | ]; eauto.
               { split; apply Is_true_eq_true; [eauto|]. 
                 apply andb_prop_intro.
                 split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
               }
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
               iApply (wp_load_fail7 with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H4| | | | | | ]; eauto.
               { split; apply Is_true_eq_true; [eauto|]. 
                 apply andb_prop_intro.
                 split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
               }
               iFrame. iNext. iIntros "(HPC & Ha & Hsrc & Ha0 & Hdst) /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
            }
        (* two successful steps: loading to a fresh dst, and loading to src *)
        destruct (decide (src = dst)); simplify_eq.
        - iApply (wp_load_success_same with "[HPC Hsrc Ha Ha0]");
                 [eauto|eauto|apply Hfp|apply H4| | | | | | ]; eauto.
          { split; apply Is_true_eq_true; [eauto|]. 
            apply andb_prop_intro.
            split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
          }
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
          iAssert (▷ interp_registers (<[dst:=if (a0 =? a)%a then w else w0]> r))%I as "[Hfull' Hreg']".
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
              + rewrite /RegLocate lookup_insert.
                destruct (a0 =? a)%a; [iApply "Hval"|iApply "Hw0"]. 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. iApply "Hv"; auto.  
          }
          iNext.
          iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown".
          destruct Heq as [-> ->]. 
          iApply ("IH" with "Hfull' Hreg' Hmap HM Hsts Hown"); auto. 
        - destruct (H3 dst) as [wdst Hsomedst].
          assert (delete PC r !! dst = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
          { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
            eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
            eauto.
          iApply (wp_load_success with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H4| | | | | | ]; eauto.
          { split; apply Is_true_eq_true; [eauto|]. 
            apply andb_prop_intro.
            split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
          }
          destruct (a0 =? a)%a; iFrame. 
          iNext. iIntros "(HPC & Hdst & Ha & Hsrc & Ha0) /=".
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
          iAssert (▷ interp_registers (<[src:=inr (p, l, a2, a1, a0)]>
                                         (<[dst:=if (a0 =? a)%a then w else w0]> r)))%I
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
              + rewrite /RegLocate lookup_insert.
                iApply "Hvsrc". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                * rewrite lookup_insert. destruct (a0 =? a)%a; auto. 
                * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                  auto. 
          }
          iNext.
          iMod ("Hcls'" with "[Ha0 $Ha]") as "Hown".
          destruct (a0 =? a)%a; iFrame. 
          destruct Heq as [-> ->]. 
          iApply ("IH" with "Hfull' Hreg' Hmap HM Hsts Hown"); auto. 
      }
      destruct (decide (a = a0)).
      { iApply "Hstep". iFrame "Hsts".
        iExists w,p.
        destruct (a0 =? a)%a eqn:Ha0; [|apply Z.eqb_neq in Ha0;congruence].
        iFrame "#". iSplitL.
        - iNext. iIntros "[_ Ha]". 
          iMod ("Hcls" with "[Hown Ha]") as "Hown"; iFrame "∗ #".
          { iNext. iExists _. iFrame. iNext. auto. }
          iModIntro; done.
        - iPureIntro. apply PermFlows_refl. 
      }
      iDestruct "Hconds" as (p'' Hp'') "Hinv0". 
      (* assert (↑logN.@a0 ⊆ (E ∖ ↑logN.@a)) as Ha2a1. *)
      (* { apply subseteq_difference_r.  *)
      (*   apply ndot_ne_disjoint; auto. *)
      (*   apply H4. split; apply Z.leb_le; auto.  *)
      (* } *)
      iMod (na_inv_open with "Hinv0 Hown") as "(Ha0 & Hown' & Hcls')"; auto.
      { apply subseteq_difference_r. 
        apply ndot_ne_disjoint; auto. done. }
      iDestruct "Ha0" as (ws0) "[Ha0 #Hva0]".           
      iApply "Hstep". iFrame "Hsts".
      iExists ws0. iExists _.
      destruct (a0 =? a)%a eqn:Ha0; [apply Z.eqb_eq,z_of_eq in Ha0;congruence|]. 
      iFrame "Ha0 Hva0".
      iSplit;[|auto]. 
      iNext. iIntros "[Ha0 Ha]".
      iMod ("Hcls'" with "[Hown' Ha0]") as "Hown";iFrame "∗ #". 
      { iNext. iExists _. iFrame. iNext. auto. }
      iMod ("Hcls" with "[Hown Ha]") as "Hown"; iFrame "∗ #".
      { iNext. iExists _. iFrame. iNext. auto. }
      iModIntro; done.
      Unshelve. exact 0. 
  Qed. 
      
End fundamental.