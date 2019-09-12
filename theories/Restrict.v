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
(*
  Lemma PermPairFlows_interp_preserved E fs fr p p' l l' b e a:
    PermPairFlowsTo (p', l') (p, l) = true →
    (b <= a)%a ∧ (a <= e)%a →
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, b, e, a)) -∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p', l', b, e, a)).
  Proof.
    intros Hp Hbounds. iIntros "HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)).
    simpl in H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H3; try congruence; simpl; match goal with | H: PermPairFlowsTo (O, _) (_, _) = _ |- _ => auto | _ => idtac end.
    - iDestruct "HA" as (g b' e' a') "[% [HB HC]]".
      inv H5. iExists l', _,_,_. iFrame. auto.
    - iDestruct "HA" as (g b' e' a' Heq) "#[Ha HC]"; inversion Heq; subst.
      iDestruct "HC" as (p Hfl) "HC".
      iExists _,_,_,_. iSplit;[eauto|].
      iFrame "#".
      iExists _; iFrame "#".
      iPureIntro.
      apply PermFlows_trans with RW; auto.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "HC".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      iPureIntro.
      apply PermFlows_trans with RW; auto.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "HC".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      iPureIntro.
      apply PermFlows_trans with RWL; auto.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "HC".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      iPureIntro.
      apply PermFlows_trans with RWL; auto.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "HC".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      by iPureIntro.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "[HC HE]".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      iPureIntro.
      apply PermFlows_trans with RX; auto.
    - iDestruct "HA" as (g b0 e0 a0 Heq) "#[Ha HC]".
      iDestruct "HC" as (p' Hp') "[HC HE]".
      inv Heq. iExists _,_,_,_. iSplit;[eauto|]. iFrame "# ∗".
      iExists p'. iFrame "HC".
      iSplit; [auto|].
      rewrite /exec_cond /interp_expr.
      destruct g,l'; [iFrame "#"| | |iFrame "#"]; inversion H4.
      iIntros (E' r). iAlways.
      iIntros (a stsf' Hin Hrel).
      apply related_sts_pub_priv in Hrel.
      iSpecialize ("HE" $! E' r a stsf' Hin Hrel).
      iNext. iExists _,_.
      do 2 (iSplit;[eauto|]).
      iIntros "(Hreg & Hmaps & Hfull & Hna & Hincl)".
      simpl.
      iDestruct "HE" as (fs0 fr0 Heqs Heqr) "HE"; simplify_eq.
      iSpecialize ("HE" with "[Hreg Hmaps Hfull Hna Hincl]").
      { iFrame. admit. } (* can't be proved yet. we need some kind of lemma which  *)
(*                             states that executing a local capability is the same as  *)
(*                             executing that capability but globally. *)
      iDestruct "HE" as (p g b e a1) "[Heq HE]".
      iExists _,_,_,_,_. iSplit; [eauto|iFrame].
  Admitted.

  Lemma RX_Restrict_case:
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
      (Hi : cap_lang.decode w = cap_lang.Restrict dst r0),
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
    rewrite delete_insert_delete. (*
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
        * case_eq (a + 1)%a; intros.
          { iApply (wp_restrict_success_z_PC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
            { iFrame. iNext. iExists _. iFrame. auto. }
            iApply wp_pure_step_later; auto.
            case_eq (decodePermPair z); intros. rewrite H6 in H4.
            destruct (andb_true_eq _ _ ltac:(symmetry in H4; exact H4)).
            simpl in H7. destruct p; simpl in H7; try congruence.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto. auto. 
            - iNext. iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
          { iApply (wp_restrict_failPC1' with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
        * iApply (wp_restrict_failPC1 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (H3 r0) as [wr0 Hsomer0].
        destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          repeat rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Ha Hown]") as "Hcls'".
                { iFrame. iNext. iExists _. iFrame. auto. }
                iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                case_eq (decodePermPair z); intros.
                destruct p; admit.
                (* case analysis on the kind of permission, fail if not RX/RWX/RWLX *)
                (* iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto.*) }
              { iApply (wp_restrict_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros.  iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_restrict_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
      rewrite lookup_delete_ne; eauto.
      destruct wdst.
      { iApply (wp_restrict_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c, p, p, p.
        - destruct r0.
          + case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hdst)".
                iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                { iFrame. iNext. iExists _. iFrame. auto. }
                iApply wp_pure_step_later; auto.
                iAssert ((interp_registers _ _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> r)))%I
                  as "[Hfull' Hreg']".
                { iSplitL.
                  - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                  - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                    + subst r2. rewrite /RegLocate lookup_insert.
                      iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                      simpl. rewrite (fixpoint_interp1_eq _ _ (inr (decodePermPair z, a2, a1, a0))) /=.
                      admit. (* need to do a case analysis *)
                    + rewrite /RegLocate lookup_insert_ne; auto.
                      iApply "Hreg"; auto. }
                iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
              { iApply (wp_restrict_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (H3 r0) as [wr0 Hsomer0].
            destruct (reg_eq_dec PC r0).
            * subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (reg_eq_dec dst r0).
              { subst r0. iApply (wp_restrict_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wr0.
                - case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
                  * case_eq (a + 1)%a; intros.
                    { revert H4; intro H4.
                      iApply (wp_restrict_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                      { iFrame. iNext. iExists _. iFrame. auto. }
                      iApply wp_pure_step_later; auto.
                      iAssert ((interp_registers _ _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> (<[r0:=inl z]> r))))%I
                        as "[Hfull' Hreg']".
                      { iSplitL.
                        - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                          destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                        - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                          + subst r2. rewrite /RegLocate lookup_insert.
                            iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                            simpl. admit. (* case analysis again *)
                          + rewrite /RegLocate lookup_insert_ne; auto.
                            destruct (reg_eq_dec r0 r2).
                            * subst r2; rewrite lookup_insert. simpl.
                              repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                            * rewrite lookup_insert_ne; auto.
                              iApply "Hreg"; auto. }
                      iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                    { iApply (wp_restrict_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  * iApply (wp_restrict_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_restrict_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. } } *)
  Admitted.
*)

End fundamental.