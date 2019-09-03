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

  Lemma RWX_getL_case:
    ∀ E0 r a g fs fr b e p' w dst r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = GetL dst r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
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
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
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
    specialize H3 with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize H3 with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetL_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      (* iDestruct (extract_from_region _ _ a with *)
      (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
      (* { iExists w. iFrame. iExact "Hva". } *)
      iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodeLoc g) else match wr0 with | inl _ => inr (RWX, g, b, e, a) | inr (_, g', _, _, _) => inl (encodeLoc g') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
      { destruct (reg_eq_dec PC r0).
        - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
          eapply lookup_insert.
          erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
        - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
            [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
      iAssert (interp_registers _ _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
      { iSplit.
        - iIntros (r1).
          iPureIntro. destruct (reg_eq_dec PC r0); auto.
          destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
        - iIntros (r1 Hnepc).
          iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
          specialize H3 with r1 as [wr1 Hr1]. 
          destruct (reg_eq_dec PC r0); eauto.
          destruct (reg_eq_dec r0 r1).
          + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
            iApply "Hv"; auto.
          + rewrite /RegLocate lookup_insert_ne; auto. }
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetL_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        (* iDestruct (extract_from_region _ _ a with *)
        (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
        (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (<[dst:=inl (encodeLoc g)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl.
          iAssert (interp_registers _ _ (<[dst:=inl (encodeLoc g)]> r)) as "[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize H3 with r1 as [wr1 Hr1]. 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways. iExists _; iFrame "#". auto. 
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p, p, p. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodeLoc l)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodeLoc l)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize H3 with r1 as [w0 Hsome]. 
              rewrite /RegLocate.
              rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
            { iFrame. iNext. iExists _. iFrame. auto. }
            (* apply IH *)
            iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
              iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
            iAlways. iExists _;iFrame "#";auto. 
      - iApply (wp_GetL_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        (* iDestruct (extract_from_region _ _ a with *)
        (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
        (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
    }
    Unshelve.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
    - apply _. 
  Qed. 

  
 Lemma RWX_getP_case:
    ∀ E0 r a g fs fr b e p' w dst r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = GetP dst r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
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
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
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
    specialize H3 with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize H3 with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetP_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0) /=".
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr.
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetP_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (<[dst:=inl (encodePerm RWX)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl. iAssert (interp_registers _ _ (<[dst:=inl (encodePerm RWX)]> r)) as "[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto. 
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv". 
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto.
          }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
            (* apply IH *)
            iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iApply wp_value. iNext.
            iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p, p, p. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodePerm p)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodePerm p)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
            { iSplit.
              - iIntros (r1). 
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
                iDestruct ("Hreg" $! r1 Hnepc) as "#Hv". 
                rewrite /RegLocate.
                destruct H3 with r1 as [w0 Hsome].
                rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
            { iFrame. iNext. iExists _. iFrame. auto. }
            (* apply IH *)
            iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
              iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
            iAlways;iExists _;iFrame "#";auto.
      - iApply (wp_GetP_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr.
    }
  Qed. 
  
  Lemma RWX_getB_case:
    ∀ E0 r a g fs fr b e p' w dst r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = GetB dst r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
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
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
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
    specialize H3 with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize H3 with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetB_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0) /=".
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr.
    }
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetB_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (<[dst:=inl (z_of b)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of b)]> r)) as "[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p, p, p. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a3)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a3)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                destruct a3; auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                destruct a3; auto.
            }
            iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=".
                iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                rewrite /RegLocate.
                destruct H3 with r1 as [w0 Hsome].
                rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
            iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
            { iFrame. iNext. iExists _. iFrame. auto. }
            (* apply IH *)
            iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
              iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
            iAlways;iExists _;iFrame "#";auto. 
      - iApply (wp_GetB_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
        iApply wp_pure_step_later;auto. iApply wp_value. 
        iNext. iIntros (Hcontr); inversion Hcontr.    
    }
  Qed.


  Lemma RWX_getE_case:
    ∀ E0 r a g fs fr b e p' w dst r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = GetE dst r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
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
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
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
    specialize H3 with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize H3 with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetE_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0) /=".
      iApply wp_pure_step_later;auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    }
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetE_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (<[dst:=inl (z_of e)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of e)]> r)) as "[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
            - iIntros (r1 Hnepc) "/=".
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
        + destruct wr0.
          * simpl. iApply wp_pure_step_later; auto.
            iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p, p, p. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a2)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a2)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc) "/=". 
                iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                rewrite /RegLocate.
                destruct H3 with r1 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
           (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
      - iApply (wp_GetE_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
        iApply wp_pure_step_later;auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
    }
  Qed.

  Lemma RWX_getA_case:
    ∀ E0 r a g fs fr b e p' w dst r0
      (* RWX case *)
      (fundamental_RX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (* RWLX case *)
      (fundamental_RWLX : ∀ stsf E r b e g a,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                      (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I)
      (Hreach : ∀ a' : Addr, (b <= a')%a ∧ (a' <= e)%a → ↑logN.@a' ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RWX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RWX p')
      (Hi : cap_lang.decode w = GetA dst r0),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
              full_map a0
           -∗ (∀ r0, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (a3, a4)) (a0 !r! r0))
           -∗ registers_mapsto (<[PC:=inr (RWX, a2, a5, a6, a1)]> a0)
           -∗ sts_full a3 a4
           -∗ na_own logrel_nais E0
           -∗ □ (∃ p, ⌜PermFlows RWX p⌝
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
        -∗ PC ↦ᵣ inr (RWX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RWX, g, b, e, a)]> r), 
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
     specialize H3 with dst as Hdst. 
    destruct Hdst as [wdst Hsomesdst].
    specialize H3 with r0 as Hr0. 
    destruct Hr0 as [wr0 Hsomer0]. 
    iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
    { destruct (reg_eq_dec PC r0); iFrame.
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
      rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
    iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
    { destruct (reg_eq_dec PC dst); iFrame.
      destruct (reg_eq_dec r0 dst); iFrame.
      destruct (reg_eq_dec PC r0).
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
      - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
        rewrite (lookup_delete_ne _ r0 dst); eauto.
        rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
    destruct (reg_eq_dec PC dst).
    { subst dst. iApply (wp_GetA_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
      iNext. iIntros "(HPC & Ha & Hr0)".
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext. iIntros (Hcontr); inversion Hcontr. 
    } 
    { case_eq (a + 1)%a; intros.
      - iApply (wp_GetA_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        destruct (reg_eq_dec PC r0).
        + subst r0. destruct (reg_eq_dec PC dst); try congruence.
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (<[dst:=inl (z_of a)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
          { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of a)]> r)) as "[% Hreg']".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto. 
            - iIntros (r1 Hnepc).
              iDestruct ("Hreg" $! r1 Hnepc) as "Hv".
              rewrite /RegLocate.
              destruct (reg_eq_dec r1 dst); simpl.
              + subst r1. rewrite lookup_insert; eauto.
                repeat rewrite fixpoint_interp1_eq. simpl. eauto.
              + rewrite lookup_insert_ne; auto. }
          (* reestablish invariant *)
          iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
        + destruct wr0.
          * iApply wp_pure_step_later; auto. iApply wp_value.
            iNext. iIntros (Hcontr); inversion Hcontr. 
          * destruct c, p, p, p. iApply wp_pure_step_later; auto.
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RWX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a1)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a1)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
            { destruct (reg_eq_dec r0 dst).
              - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                do 2 (rewrite -delete_insert_ne; auto).
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
            iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
            { iSplit.
              - iIntros (r1).
                iPureIntro. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                  right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
              - iIntros (r1 Hnepc).
                iDestruct ("Hreg" $! r1 Hnepc) as "Hv".
                rewrite /RegLocate.
                destruct H3 with r1 as [w0 Hsome].
                rewrite Hsome. destruct (reg_eq_dec r0 dst).
                + subst r0. destruct (reg_eq_dec dst r1).
                  * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                  * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                + destruct (reg_eq_dec r0 r1).
                  * subst r1. rewrite lookup_insert /=.
                    rewrite Hsome in Hsomer0; inv Hsomer0.
                    iApply "Hv"; auto.
                  * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                    { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                    { rewrite lookup_insert_ne; auto. rewrite Hsome.
                      iApply "Hv"; auto. } }
            (* reestablish invariant *)
         iNext. iMod ("Hcls" with "[Ha Hown]") as "Hown".
          { iFrame. iNext. iExists _. iFrame. auto. }
          (* apply IH *)
          iApply ("IH" with "[] Hreg' Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto| |iAlways;iPureIntro;eauto].
          iAlways;iExists _;iFrame "#";auto. 
      - iApply (wp_GetA_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
    }
  Qed. 
  
   
End fundamental.