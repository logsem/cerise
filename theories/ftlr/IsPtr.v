From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
(*
  Lemma RX_IsPtr_case:
    ∀ r a g M fs fr b e p' w dst (r0: RegName)
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
      (Hi : cap_lang.decode w = cap_lang.IsPtr dst r0)
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
    destruct (reg_eq_dec PC dst).
    * subst dst.
      specialize H3 with r0 as Hr0. 
      destruct Hr0 as [wr0 Hsomesr0]. 
      iAssert ((if reg_eq_dec PC r0 then ▷ PC ↦ᵣ inr (RX, g, b, e, a) else ▷ PC ↦ᵣ inr (RX, g, b, e, a) ∗ ▷ r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[HPC Hmap]" as "[H Hmap]".
      { destruct (reg_eq_dec PC r0); iFrame.
        iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
        rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
      iApply (wp_IsPtr_fail_PC with "[Ha H]"); eauto; iFrame.
      iNext. iIntros "(H & Ha)".
      iApply wp_pure_step_later; auto.
      iAssert ([∗ map] k↦y ∈ <[PC:=inl (if reg_eq_dec PC r0 then 1%Z else match wr0 with inl _ => 0%Z | _ => 1%Z end)]> (if reg_eq_dec PC r0 then r else (<[r0:=wr0]> r)), k ↦ᵣ y)%I with "[H Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ PC) with "[H Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame.
        - iDestruct "H" as "[H1 H2]".
          iDestruct ((big_sepM_delete _ _ r0) with "[H2 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[H1 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame. }
      iApply wp_value.
      iNext. iIntros (Hcontr). inversion Hcontr. 
    * case_eq (a + 1)%a; intros.
      { destruct (reg_eq_dec PC r0).
        - subst r0.
          specialize H3 with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst]. 
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
          rewrite (lookup_delete_ne _ PC dst); eauto.
          iApply (wp_IsPtr_successPC with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iAssert (interp_registers (<[dst:=inl 1%Z]> r))
                    as "[% Hreg']".
          { iSplitL.
            { iIntros (r0). iPureIntro.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
            iIntros (r0). iDestruct ("Hreg" $! (r0)) as "Hv".
            destruct H3 with r0 as [c Hsome].
            iIntros (Hnepc) "/=".
            rewrite /RegLocate.
            rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
            * rewrite lookup_insert.
              repeat rewrite fixpoint_interp1_eq. simpl; eauto.
            * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
              auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH"  with "[] Hreg' Hmap HM Hsts Hown"); eauto.
        - specialize H3 with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst].
          specialize H3 with r0 as Hr0. 
          destruct Hr0 as [wr0 Hsomer0]. 
          iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0dst Hmap]".
          { destruct (reg_eq_dec r0 dst).
            - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
            - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto.
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ r0 dst); eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
          iApply (wp_IsPtr_success with "[HPC Ha Hr0dst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0dst)".
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r else (<[r0:=wr0]> (<[dst:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r))), k ↦ᵣ y)%I with "[Hr0dst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec r0 dst).
            - iDestruct ((big_sepM_delete _ _ r0) with "[Hr0dst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto.
            - iDestruct "Hr0dst" as "[Hr0 Hdst]".
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto. rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto. }
          iAssert (interp_registers (if reg_eq_dec r0 dst
                        then <[r0:=inl match wr0 with
                                       | inl _ => 0%Z
                                       | inr _ => 1%Z
                                       end]> r
                        else <[r0:=wr0]> (<[dst:=inl match wr0 with
                                                     | inl _ => 0%Z
                                                     | inr _ => 1%Z
                                                     end]> r)))
                    as "[% Hreg']".
          { iSplit.
            - iPureIntro.
              destruct (reg_eq_dec r0 dst); simpl.
              + subst r0. intros r1. destruct (reg_eq_dec dst r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto; rewrite Hsome; eauto.
              + intros r1. destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst); [subst; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto; rewrite Hsome; eauto].
            - iIntros (r1).
              specialize H3 with r1 as Hr1. 
              destruct Hr1 as [c Hsome].
              iIntros (Hnepc) "/=".
              iSpecialize ("Hreg" $! r1 Hnepc).  
              rewrite /RegLocate Hsome.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                * rewrite lookup_insert_ne; eauto. rewrite Hsome. iApply "Hreg"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  rewrite Hsome in Hsomer0; inv Hsomer0.
                  iApply "Hreg"; auto.
                * rewrite lookup_insert_ne; eauto.
                  destruct (reg_eq_dec r1 dst).
                  ** subst r1. rewrite lookup_insert.
                     repeat rewrite fixpoint_interp1_eq; simpl; eauto.
                  ** rewrite lookup_insert_ne; auto. rewrite Hsome. iApply "Hreg"; auto. }

          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap HM Hsts Hown"); eauto.
      } 
      { specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else if reg_eq_dec r0 PC then ▷ dst ↦ᵣ wdst else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else if reg_eq_dec r0 PC then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[H Hmap]".
      { destruct (reg_eq_dec r0 dst).
        - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
          rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
        - destruct (reg_eq_dec r0 PC).
          + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
            iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
            rewrite (lookup_delete_ne _ r0 dst); eauto. rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
      iApply (wp_IsPtr_fail with "[Ha HPC H]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & H)".
      iApply wp_pure_step_later; auto.
      iAssert ([∗ map] k↦y ∈ (<[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r else (if reg_eq_dec r0 PC then <[dst:=inl 1%Z]> r else <[r0:= wr0]> (<[dst:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r)))), k ↦ᵣ y)%I with "[H HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec r0 dst).
        - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "[H Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
        - destruct (reg_eq_dec r0 PC).
          + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[H Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
          + iDestruct "H" as "[H1 H2]".
            iDestruct ((big_sepM_delete _ _ dst) with "[H2 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            repeat rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[H1 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
      iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
      } 
  Qed.
(*
  Lemma RWX_IsPtr_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst r0 : RegName)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = IsPtr dst r0),
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
    * subst dst.
      specialize H3 with r0 as Hr0. 
      destruct Hr0 as [wr0 Hsomesr0]. 
      iAssert ((if reg_eq_dec PC r0 then ▷ PC ↦ᵣ inr (RWX, g, b, e, a) else ▷ PC ↦ᵣ inr (RWX, g, b, e, a) ∗ ▷ r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[HPC Hmap]" as "[H Hmap]".
      { destruct (reg_eq_dec PC r0); iFrame.
        iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
        rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
      iApply (wp_IsPtr_fail_PC with "[Ha H]"); eauto; iFrame.
      iNext. iIntros "(H & Ha)".
      iApply wp_pure_step_later; auto.
      iAssert ([∗ map] k↦y ∈ <[PC:=inl (if reg_eq_dec PC r0 then 1%Z else match wr0 with inl _ => 0%Z | _ => 1%Z end)]> (if reg_eq_dec PC r0 then r else (<[r0:=wr0]> r)), k ↦ᵣ y)%I with "[H Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ PC) with "[H Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame.
        - iDestruct "H" as "[H1 H2]".
          iDestruct ((big_sepM_delete _ _ r0) with "[H2 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[H1 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame. }
      iApply wp_value.
      iNext. iIntros (Hcontr). inversion Hcontr. 
    * case_eq (a + 1)%a; intros.
      { destruct (reg_eq_dec PC r0).
        - subst r0.
          specialize H3 with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst]. 
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
          rewrite (lookup_delete_ne _ PC dst); eauto.
          iApply (wp_IsPtr_successPC with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          (* reconstruct regions *)
          (* iDestruct (extract_from_region _ _ a with *)
          (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
          (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iAssert (interp_registers _ _ (<[dst:=inl 1%Z]> r))
            as "[% Hreg']".
          { iSplitL.
            { iIntros (r0). iPureIntro.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
            iIntros (r0). iDestruct ("Hreg" $! (r0)) as "Hv".
            destruct H3 with r0 as [c Hsome].
            iIntros (Hnepc) "/=".
            rewrite /RegLocate.
            rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
            * rewrite lookup_insert.
              repeat rewrite fixpoint_interp1_eq. simpl; eauto.
            * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
              auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
          { iNext. iExists ws.
            iDestruct (extract_from_region' _ _ a _
                                            (((fixpoint interp1) E) (fs, fr)) with 
                           "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
            { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
            iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
        - specialize H3 with dst as Hdst. 
          destruct Hdst as [wdst Hsomesdst].
          specialize H3 with r0 as Hr0. 
          destruct Hr0 as [wr0 Hsomer0]. 
          iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0dst Hmap]".
          { destruct (reg_eq_dec r0 dst).
            - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
            - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto.
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ r0 dst); eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
          iApply (wp_IsPtr_success with "[HPC Ha Hr0dst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0dst)".
          iApply wp_pure_step_later; auto.
          (* reconstruct regions *)
          (* iDestruct (extract_from_region _ _ a with *)
          (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
          (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r else (<[r0:=wr0]> (<[dst:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r))), k ↦ᵣ y)%I with "[Hr0dst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec r0 dst).
            - iDestruct ((big_sepM_delete _ _ r0) with "[Hr0dst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto.
            - iDestruct "Hr0dst" as "[Hr0 Hdst]".
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto. rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              auto. }
          iAssert (interp_registers _ _ (if reg_eq_dec r0 dst
                                         then <[r0:=inl match wr0 with
                                                        | inl _ => 0%Z
                                                        | inr _ => 1%Z
                                                        end]> r
                                         else <[r0:=wr0]> (<[dst:=inl match wr0 with
                                                                      | inl _ => 0%Z
                                                                      | inr _ => 1%Z
                                                                      end]> r)))
            as "[% Hreg']".
          { iSplit.
            - iPureIntro.
              destruct (reg_eq_dec r0 dst); simpl.
              + subst r0. intros r1. destruct (reg_eq_dec dst r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto; rewrite Hsome; eauto.
              + intros r1. destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst); [subst; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto; rewrite Hsome; eauto].
            - iIntros (r1).
              specialize H3 with r1 as Hr1. 
              destruct Hr1 as [c Hsome].
              iIntros (Hnepc) "/=".
              iSpecialize ("Hreg" $! r1 Hnepc).  
              rewrite /RegLocate Hsome.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                * rewrite lookup_insert_ne; eauto. rewrite Hsome. iApply "Hreg"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert.
                  rewrite Hsome in Hsomer0; inv Hsomer0.
                  iApply "Hreg"; auto.
                * rewrite lookup_insert_ne; eauto.
                  destruct (reg_eq_dec r1 dst).
                  ** subst r1. rewrite lookup_insert.
                     repeat rewrite fixpoint_interp1_eq; simpl; eauto.
                  ** rewrite lookup_insert_ne; auto. rewrite Hsome. iApply "Hreg"; auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
          { iNext. iExists ws.
            iDestruct (extract_from_region' _ _ a _
                                            (((fixpoint interp1) E) (fs, fr)) with 
                           "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
            { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
            iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
      } 
      { specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else if reg_eq_dec r0 PC then ▷ dst ↦ᵣ wdst else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else if reg_eq_dec r0 PC then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[H Hmap]".
        { destruct (reg_eq_dec r0 dst).
          - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - destruct (reg_eq_dec r0 PC).
            + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
            + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ r0 dst); eauto. rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        iApply (wp_IsPtr_fail with "[Ha HPC H]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & H)".
        iApply wp_pure_step_later; auto.
        iAssert ([∗ map] k↦y ∈ (<[PC:=inr (RWX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r else (if reg_eq_dec r0 PC then <[dst:=inl 1%Z]> r else <[r0:= wr0]> (<[dst:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r)))), k ↦ᵣ y)%I with "[H HPC Hmap]" as "Hmap".
        { destruct (reg_eq_dec r0 dst).
          - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "[H Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
          - destruct (reg_eq_dec r0 PC).
            + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[H Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
            + iDestruct "H" as "[H1 H2]".
              iDestruct ((big_sepM_delete _ _ dst) with "[H2 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[H1 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. }
  Qed.*)
*)
End fundamental.