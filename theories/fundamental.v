From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Lemma extract_r_ex reg (r : RegName) :
    (∃ w, reg !! r = Some w) →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) → ∃ w, r ↦ᵣ w)%I. 
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ r i, r ↦ᵣ i)%I reg r w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma extract_lookup_reg reg (r : RegName) :
    ((∀ r0, ⌜is_Some (reg !! r0)⌝ ∧ (⌜r0 ≠ PC⌝ → (fixpoint interp1) (reg !r! r0))) →
     ⌜is_Some (reg !! r)⌝)%I.
  Proof.
    iIntros "Hreg". 
    iDestruct ("Hreg" $! r) as "[Hr Hreg]". done. 
  Qed.

  Lemma extract_valid_reg reg (r : RegName) :
    r ≠ PC →
    ((∀ r0, ⌜is_Some (reg !! r0)⌝ ∧ (⌜r0 ≠ PC⌝ → (fixpoint interp1) (reg !r! r0))) →
     (fixpoint interp1) (reg !r! r))%I.
  Proof.
    iIntros (Hne) "Hreg".
    iAssert (⌜is_Some (reg !! r)⌝ ∧ (⌜r ≠ PC⌝ → (fixpoint interp1) (reg !r! r)))%I
                                             with "Hreg" as "[_ Hv]". 
    iApply "Hv". iPureIntro. done. 
  Qed. 

  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl). 

  Lemma fundamental_RX b e g (a : Addr) ws :
    (inv (logN .@ (b,e)) (read_only_cond b e ws interp) →
     ⟦ inr ((RX,g),b,e,a) ⟧ₑ )%I
  with fundamental_RWX b e g (a : Addr) :
    (inv (logN .@ (b,e)) (read_write_cond b e interp) →
     ⟦ inr ((RWX,g),b,e,a) ⟧ₑ )%I
  with fundamental_RWLX b e g (a : Addr) :
    (inv (logN .@ (b,e)) (read_write_local_cond b e interp) →
     ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ )%I. 
  Proof.
  {
    iIntros "#Hinv /=".
    iIntros (r m fs fr) "[Hreg [Hmreg Hsts]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv". iLöb as "IH" forall (r a g fs fr b e ws). iIntros "#Hinv". 
    iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iInv (logN.@(b, e)) as "Hregion" "Hcls".      
      iDestruct (extract_from_region _ _ a with "Hregion") as (w) "(Heqws & Hregionl & Hvalidl & >Ha & #Hva & Hh)"; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        rewrite delete_insert_delete.
        destruct (reg_eq_dec PC r0).
        * subst r0.
          iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros "[HPC Ha] /=".
          iApply wp_pure_step_later; auto.
          (* reconstruct regions *)
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          (* apply IH *)
          iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg Hmap Hsts").
          iFrame "Hinv". 
          (* reestablish invariants *)
          iApply "Hcls"; iFrame; iApply "Hcls'"; iFrame.
        * iDestruct (extract_lookup_reg r r0 with "Hreg") as "%".
          destruct H2 as [wsrc Hsomesrc].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
          rewrite (lookup_delete_ne r PC r0); eauto.
          iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; iFrame.
          iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          (* reconstruct regions *)
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          destruct (updatePcPerm wsrc) eqn:Heq; (* Same story as Load PC src*)
          admit.
      + admit. (* Jnz *)
      + admit. (* Mov *)
      + (* Load *)
        destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
        * (* Load PC PC ==> fail *)
          iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
          iNext. iIntros "[HPC Ha] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iDestruct (extract_from_region _ _ a with
               "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite insert_insert.
          iExists (<[PC:=w]> r),fs,fr. iFrame.
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. }
          iFrame "#". 
          iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=w]> r !! r0)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r0 PC).
            - subst r0. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto. iApply (extract_lookup_reg); auto. }
          iFrame. iApply "Hcls". iNext. iFrame.
        * (* Load PC src ==> success if src ↦ inr, fail o/w *)
          iDestruct (extract_lookup_reg r src with "Hreg") as "%".
          destruct H2 as [wsrc Hsomesrc]. 
          assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
          { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
          rewrite delete_insert_delete.
          iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
          destruct wsrc.
          { (* src ↦ inl z ==> fail *)
            iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
            iNext. iIntros "[HPC [Ha Hsrc]] /=".
            iApply wp_pure_step_later; auto. iApply wp_value.
            iDestruct (extract_from_region _ _ a with
               "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. iExact "Hva". }
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iExists _,fs,fr. iFrame.
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. }
            iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[src:=inl z]> r) !! r0)⌝)%I as "HA".
            { iIntros. destruct (reg_eq_dec r0 PC).
              - subst r0. rewrite lookup_insert. eauto.
              - rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec r0 src).
                + subst r0. rewrite lookup_insert. eauto.
                + rewrite lookup_insert_ne; auto.
                  iApply (extract_lookup_reg); auto. }
            iFrame "#". iFrame. iApply "Hcls". iNext. iFrame. 
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
              iDestruct (extract_from_region _ _ a with
               "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              { iExists w. iFrame. iExact "Hva". }
              iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iExists _,fs,fr. iFrame.
              iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
              { iPureIntro. apply related_sts_refl. }
              iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[src:=inr (p, l, a2, a1, a0)]> r) !! r0)⌝)%I as "HA".
              { iIntros. destruct (reg_eq_dec r0 PC).
                - subst r0. rewrite lookup_insert. eauto.
                - rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 src).
                  + subst r0. rewrite lookup_insert. eauto.
                  + rewrite lookup_insert_ne; auto.
                    iApply (extract_lookup_reg); auto. }
              iFrame "#". iFrame. iApply "Hcls". iNext. iFrame. 
          }
          (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
          apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n0
            as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge]. 
          (* get validity of capability in src from Hreg *)
          iDestruct (extract_valid_reg r src with "Hreg") as "#Hvsrc"; auto.
          rewrite /RegLocate Hsomesrc.
          iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
          (* Each condition in Hconds take a step in similar fashion *)
          iAssert ((∃ w, (a0 ↦ₐ w -∗
                   |={⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1),⊤ ∖ ↑logN.@(b, e)}=> emp)
            ∗  a0 ↦ₐ w ∗ ▷ ⟦ w ⟧)
           -∗ WP Instr Executable @ ⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1)
                 {{ v, |={⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1),⊤ ∖ ↑logN.@(b, e)}=>
                    |={⊤ ∖ ↑logN.@(b, e),⊤}=> WP fill [SeqCtx] (of_val v)
                    {{ v, (λne _ : valC cap_lang, ∃ (reg0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                                                             registers_mapsto reg0
                                                             ∗ (∀ r0 : RegName, ⌜is_Some (reg0 !! r0)⌝)
                                                               ∗ ⌜related_sts fs fs' fr fr'⌝ ∗ sts_full fs' fr')
                                                              v }} }})%I
            with "[-]" as "Hstep".
          {
            iIntros "Hw0". iDestruct "Hw0" as (w0) "(Hcls' & Ha0 & #Hw0)". 
            destruct w0.
            { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]"); eauto.
              - split; apply Is_true_eq_true; eauto.
                apply andb_prop_intro. split; [apply Hle|apply Hge].
              - iFrame.
              - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iDestruct (extract_from_region _ _ a with
                               "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
                { iExists w. iFrame. iExact "Hva". }
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iExists _,fs,fr. iFrame.
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. }
                iFrame "#". iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inl z]> (<[src:=inr (p, l, a2, a1, a0)]> r) !! r0)⌝)%I as "HA".
                { iIntros. destruct (reg_eq_dec r0 PC).
                  - subst r0. rewrite lookup_insert. eauto.
                  - rewrite lookup_insert_ne; auto.
                    destruct (reg_eq_dec r0 src).
                    + subst r0. rewrite lookup_insert. eauto.
                    + rewrite lookup_insert_ne; auto.
                      iApply (extract_lookup_reg); auto. }
                iFrame. iApply "Hcls". iFrame. iApply "Hcls'". iFrame. (* iNext. *)
                (* iApply (extract_from_region _ _ a0); *)
                (*   first (split; by apply Z.leb_le,Is_true_eq_true). *)
                (* iFrame. iExists a0l, (inl z), a0h. iFrame. iExact "Hva0".  *)
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
                iDestruct (extract_from_region _ _ a with
                               "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
                { iExists w. iFrame. iExact "Hva". }
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iExists _,fs,fr. iFrame.
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. }
                iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (p0, l0, a5, a4, a3)]> (<[src:=inr (p, l, a2, a1, a0)]> r) !! r0)⌝)%I as "HA".
                { iIntros. destruct (reg_eq_dec r0 PC).
                  - subst r0. rewrite lookup_insert. eauto.
                  - rewrite lookup_insert_ne; auto.
                    destruct (reg_eq_dec r0 src).
                    + subst r0. rewrite lookup_insert. eauto.
                    + rewrite lookup_insert_ne; auto.
                      iApply (extract_lookup_reg); auto. }
                iFrame "#". iFrame. iApply "Hcls". iFrame. iApply "Hcls'". iFrame.
            }
            (* successful load into PC *)
            iApply (wp_load_success_PC with "[HPC Ha Hsrc Ha0]"); eauto.
            - split; apply Is_true_eq_true; eauto.
              apply andb_prop_intro. split; [apply Hle|apply Hge].
            - iFrame.
            - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
              iApply wp_pure_step_later; auto.
              (* recontruct regions *)
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              { iExists w. iFrame. iExact "Hva". }
              (* We want to apply the IH on the updated r, however the PC has now 
                 changed region entirely! We have four cases: either the permission 
                 of the updated PC is valid: i.e. RX (IH), RWX (second lemma), 
                 RWLX (third lemma), or the permission is not valid, and the program 
                 crashes *)  
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
              iAssert (interp_registers (<[src:=inr (p, l, a2, a1, a0)]> r)) as "Hreg'".
              { iIntros (r0). iDestruct ("Hreg" $! (r0)) as "[% Hv]".
                  destruct H2 as [c Hsome].
                  iSplit; auto.
                - iPureIntro.
                  destruct (decide (src = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. 
                - iIntros (Hnepc) "/=".
                  destruct (decide (src = r0)); simplify_eq.
                  + by rewrite /RegLocate lookup_insert.
                  + rewrite /RegLocate lookup_insert_ne; auto. 
                    rewrite Hsome. iApply "Hv"; auto.  
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
                 iAssert (⌜E ≠ RX⌝ ∧ ⌜E ≠ RWX⌝ ∧ ⌜E ≠ RWLX⌝)%I as "Htrivial";
                 first (iSplit; iPureIntro; auto)| | ];
               try (iDestruct ("Hfail" with "Htrivial HPC") as "Hfail";
                    iApply (wp_wand with "Hfail");
                    iAssert ((∀ v : val cap_lang, ⌜v = FailedV⌝
                                ∗ PC ↦ᵣ inr (_, l0, a5, a4, a6)
                               -∗ ∃ (reg0 : Reg) (fs' : STS_states) (fr' : STS_rels), registers_mapsto reg0
                                                            ∗ (∀ r0 : RegName, ⌜is_Some (reg0 !! r0)⌝)
                                                              ∗ ⌜related_sts fs fs' fr fr'⌝ ∗ sts_full fs' fr'))%I
                      with "[Hmap Hsrc Hsts]" as "Hfailed";
                     [iIntros (v) "[-> HPC]";
                      iDestruct ((big_sepM_delete _ _ src)
                                   with "[Hsrc Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                      rewrite -delete_insert_ne; auto;
                      iDestruct ((big_sepM_delete _ _ PC)
                                   with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     iExists _,fs,fr; iFrame; iSplitL;
                       [iIntros; destruct (reg_eq_dec r0 PC);
                        [subst r0; rewrite lookup_insert; eauto|
                         rewrite lookup_insert_ne; auto;
                         destruct (reg_eq_dec r0 src);
                         [subst r0; rewrite lookup_insert; eauto|
                          rewrite lookup_insert_ne; auto;
                          iApply (extract_lookup_reg); auto] ]
                      |iPureIntro; apply related_sts_refl]
                     |];
                    iFrame;
                    (* close invariants *)
                    iApply "Hcls"; iFrame; iApply "Hcls'"; iFrame
                  ).
              { (* new PC is RX ==> apply IH*)
                iClear "Hfail".
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     rewrite -delete_insert_ne; auto;
                     iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
                (* apply IH *)
                rewrite (fixpoint_interp1_eq (inr (RX, l0, a5, a4, a3))). simpl.
                iDestruct "Hw0" as (p0 g0 b0 e0 a7 ws1) "[% [Hb0e0 Hexec]]"; simplify_eq.
                iDestruct ("IH" $! _ _ _ _ _ _ _ ws1 with "Hreg' Hmap Hsts Hb0e0") as "HA".
                iFrame.
                (* reestablish invariants *)
                iApply "Hcls"; iFrame; iApply "Hcls'"; iFrame.
              }
              { (* new PC is RWX, apply fundamental_RWX *)
                iClear "Hfail".
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     rewrite -delete_insert_ne; auto;
                     iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
                rewrite (fixpoint_interp1_eq (inr (RWX, l0, a5, a4, a3))). simpl.
                iDestruct "Hw0" as (p0 g0 b0 e0 a7) "[% [Hb0e0 Hexec]]"; simplify_eq.
                iDestruct (fundamental_RWX with "Hb0e0") as "Hexpr". 
                iDestruct ("Hexpr" $! (<[src:=inr (p, l, a2, a1, a0)]> r) m fs fr
                             with "[$]")
                  as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq. iFrame.
                (* reestablish invariants *)
                iApply "Hcls"; iFrame; iApply "Hcls'"; iFrame.
              }
              { (* new PC is RWLX, apply fundamental_RWLX *)
                iClear "Hfail".
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     rewrite -delete_insert_ne; auto;
                     iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
                rewrite (fixpoint_interp1_eq (inr (RWLX, l0, a5, a4, a3))). simpl.
                iDestruct "Hw0" as (p0 g0 b0 e0 a7) "[% [Hb0e0 Hexec]]"; simplify_eq.
                iDestruct (fundamental_RWLX with "Hb0e0") as "Hexpr". 
                iDestruct ("Hexpr" $! (<[src:=inr (p, l, a2, a1, a0)]> r) m fs fr
                             with "[$]")
                  as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq. iFrame.
                (* reestablish invariants *)
                iApply "Hcls"; iFrame. iApply "Hcls'"; iFrame.
              }
          }
          iDestruct "Hconds" as "[#Hro|#[Hrw|Hrwl]]".
          (* each condition is similar, but with some subtle differences for closing *)
          { iDestruct "Hro" as (ws0) "Hinv0".
            (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hro_cond" "Hcls'";[admit|].
            iDestruct (extract_from_region _ _ a0 with "Hro_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iApply (extract_from_region _ _ a0);
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iFrame. iExists _. iFrame. iExact "Hva0".
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hrw_cond" "Hcls'";[admit|].
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond". 
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iDestruct (extract_from_region _ _ a0 with
                "[Heqws Hregion0l Hvalid0l Hh0 Ha0]") as "Hregion0".
            { split; apply Z.leb_le,Is_true_eq_true; eauto. }
            { iExists _. iFrame. iFrame "#". }
            iExists ws0. iFrame.
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hrw_cond" "Hcls'";[admit|].
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond". 
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iDestruct (extract_from_region _ _ a0 with
                "[Heqws Hregion0l Hvalid0l Hh0 Ha0]") as "Hregion0".
            { split; apply Z.leb_le,Is_true_eq_true; eauto. }
            { iExists _. iFrame. iFrame "#". }
            iExists ws0. iFrame. }
        * rewrite delete_insert_delete.
          iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
          destruct H2 as [wdst Hsomedst]. 
          assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto. 
          destruct (a + 1)%a eqn:Ha'. 
          2: (* if PC cannot be incremented ==> dst is updated, then program crashes *)
            { iApply (wp_load_fail6 with "[HPC Hdst Ha]"); eauto.
              iFrame. iNext. iIntros "[HPC [Ha Hdst]] /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iExists (<[PC:=inr (RX, g, b, e, a)]> (<[dst:=w]> r)),fs,fr. iFrame. 
              iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
              { iPureIntro. apply related_sts_refl. }
              iFrame "#".
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                rewrite -delete_insert_ne; auto;
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
              iFrame. iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[dst:=w]> r) !! r0)⌝)%I as "HA".
              { iIntros. destruct (reg_eq_dec r0 PC).
                - subst r0. rewrite lookup_insert. eauto.
                - rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 dst).
                  + subst r0. rewrite lookup_insert. eauto.
                  + rewrite lookup_insert_ne; auto.
                    iApply (extract_lookup_reg); auto. }
              iFrame.
              iApply "Hcls".
              iDestruct (extract_from_region _ _ a with
                  "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              iExists _. iFrame. rewrite Ha'. iFrame. iExact "Hva". }
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
            iAssert (interp_registers (<[dst:=w]> r)) as "Hreg'".
            { iIntros (r0). iDestruct ("Hreg" $! (r0)) as "[% Hv]".
              destruct H2 as [c Hsome].
              iSplit; auto.
              - iPureIntro.
                destruct (decide (dst = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. 
              - iIntros (Hnepc) "/=".
                destruct (decide (dst = r0)); simplify_eq.
                + by rewrite /RegLocate lookup_insert.
                + rewrite /RegLocate lookup_insert_ne; auto. 
                  rewrite Hsome. iApply "Hv"; auto.  
            }
            iApply ("IH" with "Hreg' Hmap Hsts").
            iFrame "Hinv".
            (* reestablish invariants *)
            iApply "Hcls"; iFrame.
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            iExists _. iFrame. rewrite Ha'. iFrame. iExact "Hva". 
        * iDestruct (extract_lookup_reg r src with "Hreg") as "%".
          destruct H2 as [wsrc Hsomesrc].
          assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
          { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
          rewrite delete_insert_delete. 
          iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
          destruct wsrc.
          { (* src ↦ inl z ==> fail *)
            iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
            iNext. iIntros "[HPC [Ha Hsrc]] /=".
            iApply wp_pure_step_later; auto. iApply wp_value.
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists _. iFrame. iExact "Hva". }
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iExists _,fs,fr. iFrame.
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. }
            iFrame "#". iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[src:=inl z]> r) !! r0)⌝)%I as "HA".
              { iIntros. destruct (reg_eq_dec r0 PC).
                - subst r0. rewrite lookup_insert. eauto.
                - rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 src).
                  + subst r0. rewrite lookup_insert. eauto.
                  + rewrite lookup_insert_ne; auto.
                    iApply (extract_lookup_reg); auto. }
              iFrame. iApply "Hcls". iNext. iFrame.
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
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              { iExists _. iFrame. iExact "Hva". }
              iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iExists _,fs,fr. iFrame.
              iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
              { iPureIntro. apply related_sts_refl. }
              iFrame "#". iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[src:=inr (p, l, a2, a1, a0)]> r) !! r0)⌝)%I as "HA".
              { iIntros. destruct (reg_eq_dec r0 PC).
                - subst r0. rewrite lookup_insert. eauto.
                - rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 src).
                  + subst r0. rewrite lookup_insert. eauto.
                  + rewrite lookup_insert_ne; auto.
                    iApply (extract_lookup_reg); auto. }
              iFrame. iApply "Hcls". iNext. iFrame.
          }
          (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
          apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n1
            as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge].
          (* the contents of src is valid *)
          iAssert ((fixpoint interp1) (inr (p, l, a2, a1, a0))) as "#Hvsrc".
          { iDestruct ("Hreg" $! src) as "[_ Hvsrc]".
            rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
          iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
          (* Each condition in Hconds take a step in similar fashion *)
          iAssert ((∃ w, (a0 ↦ₐ w -∗
                   |={⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1),⊤ ∖ ↑logN.@(b, e)}=> emp)
            ∗  a0 ↦ₐ w ∗ ▷ ⟦ w ⟧)
           -∗ WP Instr Executable @ ⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1)
                 {{ v, |={⊤ ∖ ↑logN.@(b, e) ∖ ↑logN.@(a2, a1),⊤ ∖ ↑logN.@(b, e)}=>
                    |={⊤ ∖ ↑logN.@(b, e),⊤}=> WP fill [SeqCtx] (of_val v)
                    {{ v, (λne _ : valC cap_lang, ∃ reg0 fs' fr',
                          registers_mapsto reg0 ∗ (∀ r0 : RegName, ⌜is_Some (reg0 !! r0)⌝) ∗ ⌜related_sts fs fs' fr fr'⌝
                                           ∗ sts_full fs' fr') v }} }})%I
            with "[-]" as "Hstep".
          { iIntros "Hcls'". iDestruct "Hcls'" as (w0) "[Hcls' [Ha0 #Hw0]]". 
            (* if PC cannot be incremented ==> dst is updated, then program crashes *)
            destruct (a + 1)%a eqn:Ha'; simplify_eq.
            2: { destruct (decide (src = dst)); simplify_eq. 
                 - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]"); eauto.
                   { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
                   iFrame. iNext. iIntros "[HPC [Ha [Hdst Ha0]]] /=".
                   iApply wp_pure_step_later; auto.
                   iApply wp_value. iExists _,fs,fr.
                   iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     rewrite -delete_insert_ne; auto;
                       iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                       [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
                   iFrame. iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[dst:=w0]> r) !! r0)⌝)%I as "HA".
                   { iIntros. destruct (reg_eq_dec r0 PC).
                     - subst r0. rewrite lookup_insert. eauto.
                     - rewrite lookup_insert_ne; auto.
                       destruct (reg_eq_dec r0 dst).
                       + subst r0. rewrite lookup_insert. eauto.
                       + rewrite lookup_insert_ne; auto.
                         iApply (extract_lookup_reg); auto. }
                   iFrame.
                   iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                   { iPureIntro. apply related_sts_refl. }
                   iFrame "#". iApply "Hcls".
                   iDestruct (extract_from_region _ _ a with
                                  "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
                   iExists _. rewrite Ha'. iFrame "∗ #". iFrame. 
                   iApply "Hcls'". iFrame.
                 - iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
                   destruct H2 as [wdst Hsomedst].
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
                   iApply wp_value. iExists _,fs,fr.
                   iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                     repeat rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
                   iFrame. iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> (<[src:=inr (p, l, a2, a1, a0)]> (<[dst:=w0]> r)) !! r0)⌝)%I as "HA".
                   { iIntros. destruct (reg_eq_dec r0 PC).
                     - subst r0. rewrite lookup_insert. eauto.
                     - rewrite lookup_insert_ne; auto.
                       destruct (reg_eq_dec r0 src).
                       + subst r0. rewrite lookup_insert. eauto.
                       + rewrite lookup_insert_ne; auto.
                         destruct (reg_eq_dec r0 dst).
                         * subst r0. rewrite lookup_insert. eauto.
                         * rewrite lookup_insert_ne; auto.
                           iApply (extract_lookup_reg); auto. }
                   iFrame. 
                   iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                   { iPureIntro. apply related_sts_refl. }
                   iFrame "#". iApply "Hcls".
                   iDestruct (extract_from_region _ _ a with
                                  "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
                   iExists _. rewrite Ha'. iFrame "∗ #". iFrame. 
                   iApply "Hcls'". iFrame.
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
              iAssert (interp_registers (<[dst:=w0]> r)) as "Hreg'".
              { iIntros (r0). iDestruct ("Hreg" $! (r0)) as "[% Hv]".
                destruct H2 as [c Hsome].
                iSplit; auto.
                - iPureIntro.
                  destruct (decide (dst = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. 
                - iIntros (Hnepc) "/=".
                  destruct (decide (dst = r0)); simplify_eq.
                  + rewrite /RegLocate lookup_insert. iApply "Hw0". 
                  + rewrite /RegLocate lookup_insert_ne; auto. 
                    rewrite Hsome. iApply "Hv"; auto.  
              }
              iApply ("IH" with "Hreg' Hmap Hsts").
              iFrame "Hinv".
              (* reestablish invariants *)
              iApply "Hcls"; iFrame.
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              iExists _. rewrite Ha'. iFrame. iExact "Hva". iFrame. 
              iApply "Hcls'". iFrame. 
            - iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
              destruct H2 as [wdst Hsomedst].
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
              iAssert (interp_registers (<[src:=inr (p, l, a2, a1, a0)]> (<[dst:=w0]> r)))
                        as "Hreg'".
              { iIntros (r0). iDestruct ("Hreg" $! (r0)) as "[% Hv]".
                destruct H2 as [c Hsome].
                iSplit; auto.
                - iPureIntro.
                  destruct (decide (src = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                  destruct (decide (dst = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                - iIntros (Hnepc) "/=".
                  destruct (decide (src = r0)); simplify_eq.
                  + rewrite /RegLocate lookup_insert. iApply "Hvsrc". 
                  + rewrite /RegLocate lookup_insert_ne; auto. 
                    rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                    * by rewrite lookup_insert.
                    * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                      auto. 
              }
              iApply ("IH" with "Hreg' Hmap Hsts").
              iFrame "Hinv".
              (* reestablish invariants *)
              iApply "Hcls"; iFrame.
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              iExists _. rewrite Ha'. iFrame. iExact "Hva". iFrame. 
              iApply "Hcls'". iFrame. 
          }
          (* Now the final step is to open the invariant for each possible condition *)
          iDestruct "Hconds" as "[#Hro|#[Hrw|Hrwl]]".
          (* each condition is similar, but with some subtle differences for closing *)
          { iDestruct "Hro" as (ws0) "Hinv0".
            (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hro_cond" "Hcls'";[admit|].
            iDestruct (extract_from_region _ _ a0 with "Hro_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iApply (extract_from_region _ _ a0);
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iFrame. iExists _. iFrame. iExact "Hva0".
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hrw_cond" "Hcls'";[admit|].
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond". 
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iDestruct (extract_from_region _ _ a0 with
                "[Heqws Hregion0l Hvalid0l Hh0 Ha0]") as "Hregion0".
            { split; apply Z.leb_le,Is_true_eq_true; eauto. }
            { iExists _. iFrame. iFrame "#". }
            iExists ws0. iFrame.
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hrw_cond" "Hcls'";[admit|].
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond". 
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond") as (w0) "(Heqws & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep".
            iExists w0. iFrame "Ha0 #". iIntros "Ha0".
            iApply "Hcls'". iNext.
            iDestruct (extract_from_region _ _ a0 with
                "[Heqws Hregion0l Hvalid0l Hh0 Ha0]") as "Hregion0".
            { split; apply Z.leb_le,Is_true_eq_true; eauto. }
            { iExists _. iFrame. iFrame "#". }
            iExists ws0. iFrame. }
      + admit. (* Store *)
      + admit. (* Lt *)
      + admit. (* Add *)
      + admit. (* Sub *)
      + admit. (* Lea *)
      + admit. (* Restrict *)
      + admit. (* Subseg *)
      + (* IsPtr *)
        rewrite delete_insert_delete.
        destruct (reg_eq_dec PC dst).
        * subst dst.
          iDestruct (extract_lookup_reg r r0 with "Hreg") as "%".
          destruct H2 as [wr0 Hsomer0].
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
          iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=inl
                                                           (if reg_eq_dec PC r0
                                                            then 1%Z
                                                            else
                                                             match wr0 with
                                                             | inl _ => 0%Z
                                                             | inr _ => 1%Z
                                                             end)]>
                                                     (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0); [iApply (extract_lookup_reg); auto|].
              destruct (reg_eq_dec r1 r0).
              + subst r1. rewrite lookup_insert. eauto.
              + rewrite lookup_insert_ne; auto.
                iApply (extract_lookup_reg); auto. }
          iFrame.
          iApply "Hcls".
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          iExists _. iFrame "∗ #".
        * case_eq (a + 1)%a; intros.
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
              destruct H3 as [wdst Hsomedst].
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto.
              iApply (wp_IsPtr_successPC with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto.
              (* reconstruct regions *)
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iAssert (interp_registers (<[dst:=inl 1%Z]> r))
                        as "Hreg'".
              { iIntros (r0). iDestruct ("Hreg" $! (r0)) as "[% Hv]".
                destruct H3 as [c Hsome].
                iSplit; auto.
                - iPureIntro.
                  destruct (decide (dst = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                - iIntros (Hnepc) "/=".
                  rewrite /RegLocate.
                  rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                  * rewrite lookup_insert.
                    repeat rewrite fixpoint_interp1_eq. simpl; eauto.
                  * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                    auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". 
              (* reestablish invariants *)
              iApply "Hcls"; iFrame.
            - iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
              destruct H3 as [wdst Hsomedst].
              iDestruct (extract_lookup_reg r r0 with "Hreg") as "%".
              destruct H3 as [wr0 Hsomer0].
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
              iDestruct (extract_from_region _ _ a with
                             "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
              { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
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
                        as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                destruct H3 as [c Hsome].
                iSplit; auto.
                - iPureIntro.
                  destruct (reg_eq_dec r0 dst); simpl.
                  + subst r0. destruct (reg_eq_dec dst r1).
                    * subst r1. rewrite lookup_insert; eauto.
                    * rewrite lookup_insert_ne; auto; rewrite Hsome; eauto.
                  + destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert; eauto.
                    * rewrite lookup_insert_ne; auto.
                      destruct (reg_eq_dec r1 dst); [subst; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto; rewrite Hsome; eauto].
                - iIntros (Hnepc) "/=".
                  rewrite /RegLocate.
                  rewrite Hsome. destruct (reg_eq_dec r0 dst).
                  + destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert.
                      repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                    * rewrite lookup_insert_ne; eauto. rewrite Hsome; iApply "Hv"; auto.
                  + destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert.
                      rewrite Hsome in Hsomer0; inv Hsomer0.
                      iApply "Hv"; auto.
                    * rewrite lookup_insert_ne; eauto.
                      destruct (reg_eq_dec r1 dst).
                      ** subst r1. rewrite lookup_insert.
                         repeat rewrite fixpoint_interp1_eq; simpl; eauto.
                      ** rewrite lookup_insert_ne; auto. rewrite Hsome. iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". 
              (* reestablish invariants *)
              iApply "Hcls"; iFrame. }
          { iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
            destruct H3 as [wdst Hsomedst].
            iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
            destruct H3 as [wr0 Hsomer0].
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
          iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=inr (RX, g, b, e, a)]>
                                                     (if reg_eq_dec r0 dst
                                                      then
                                                       <[r0:=inl
                                                               match wr0 with
                                                               | inl _ => 0%Z
                                                               | inr _ => 1%Z
                                                               end]> r
                                                      else
                                                       if reg_eq_dec r0 PC
                                                       then <[dst:=inl 1%Z]> r
                                                       else
                                                        <[r0:=wr0]>
                                                          (<[dst:=inl
                                                                    match wr0 with
                                                                    | inl _ => 0%Z
                                                                    | inr _ => 1%Z
                                                                    end]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec r1 r0).
                * subst r1. rewrite lookup_insert. eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply (extract_lookup_reg); auto.
              + destruct (reg_eq_dec r0 PC).
                * destruct (reg_eq_dec dst r1).
                  -- subst r1. rewrite lookup_insert. eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; auto.
                * destruct (reg_eq_dec r0 r1).
                  -- subst r1. rewrite lookup_insert. eauto.
                  -- rewrite lookup_insert_ne; auto.
                     destruct (reg_eq_dec dst r1).
                     ++ subst r1. rewrite lookup_insert. eauto.
                     ++ rewrite lookup_insert_ne; auto.
                        iApply extract_lookup_reg; auto. }
          iFrame. iApply "Hcls".
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          iExists _. rewrite H2. iFrame "∗ #". }
      + (* GetL *)
        rewrite delete_insert_delete.
        iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
        destruct H2 as [wdst Hsomedst].
        iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
        destruct H2 as [wr0 Hsomer0].
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
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodeLoc g) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (_, g', _, _, _) => inl (encodeLoc g') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=if reg_eq_dec PC r0
                                                         then inl (encodeLoc g)
                                                         else
                                                          match wr0 with
                                                          | inl _ => inr (RX, g, b, e, a)
                                                          | inr (_, g', _, _, _) => inl (encodeLoc g')
                                                          end]> (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)
                                                                  !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0).
              + iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame. iApply "Hcls".
          iFrame "∗ #". }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetL_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (encodeLoc g)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers (<[dst:=inl (encodeLoc g)]> r)) as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                iSplit; auto.
                - iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (Hnepc) "/=". rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. destruct H3. rewrite H3.
                    iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". iApply "Hcls"; iFrame.
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 (inl z))); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inl z))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert. rewrite Hsome in Hsomedst; inv Hsomedst.
                          iApply "Hv"; auto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply wp_value. iExists _,fs,fr. iFrame. 
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                    (<[PC:=inr (RX, g, b, e, a)]>
                                     (if reg_eq_dec r0 dst
                                      then <[dst:=inl z]> r
                                      else <[r0:=inl z]> (<[dst:=wdst]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec dst r1).
                * subst r1; rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst).
                  -- subst r1; rewrite lookup_insert; eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; eauto. }
                iFrame. iApply "Hcls".
                iFrame "∗ #".
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodeLoc l)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodeLoc l)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
                iFrame "Hinv". iApply "Hcls"; iFrame.
          - iApply (wp_GetL_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            iApply wp_pure_step_later; auto.
            iApply wp_value. iExists _,fs,fr. iFrame. 
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. } iFrame "#".
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (<[dst:=(if reg_eq_dec PC r0
               then inl (encodeLoc g)
               else
                match wr0 with
                | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                | inr (_, g', _, _, _) => inl (encodeLoc g')
                end)]> (if reg_eq_dec PC r0 then r else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (delete PC r) dst _).
              destruct (reg_eq_dec PC dst); try congruence.
              iFrame.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (<[dst:=inl (encodeLoc g)]> r) PC _).
              rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
              auto.
            - destruct (reg_eq_dec r0 dst).
              + subst r0. iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete PC r) dst _).
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> r) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
                auto.
              + iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete dst (delete PC r)) r0 _).
                rewrite delete_commute. iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[r0:=wr0]> (delete PC r)) dst _).
                rewrite delete_insert_ne; auto.
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> (<[r0:=_]> r)) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto.
                rewrite (delete_insert_ne _ PC r0 _); auto.
                iFrame.
                auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iFrame.
          iAssert (∀ r1 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]>
                                             (<[dst:=if reg_eq_dec PC r0
                                                     then inl (encodeLoc g)
                                                     else
                                                       match wr0 with
                                                       | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                                                       | inr (_, g', _, _, _) => inl (encodeLoc g')
                                                       end]>
                                              (if reg_eq_dec PC r0
                                               then r
                                               else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r))
                                               !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec PC r1).
            - subst r1. rewrite lookup_insert; eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec dst r1).
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec PC r0); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 dst); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame.
          iApply "Hcls".
          iFrame "∗ #". }
      + (* GetP *)
        rewrite delete_insert_delete.
        iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
        destruct H2 as [wdst Hsomedst].
        iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
        destruct H2 as [wr0 Hsomer0].
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
          iNext. iIntros "(HPC & Ha & Hr0)".
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodePerm RX) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (p', _, _, _, _) => inl (encodePerm p') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=if reg_eq_dec PC r0
                                                         then inl (encodePerm RX)
                                                         else
                                                          match wr0 with
                                                          | inl _ => inr (RX, g, b, e, a)
                                                          | inr (p', _, _, _, _) => inl (encodePerm p')
                                                          end]> (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)
                                                                  !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0).
              + iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame. iApply "Hcls".
          iFrame "∗ #". }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetP_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (encodePerm RX)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers (<[dst:=inl (encodePerm RX)]> r)) as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                iSplit; auto.
                - iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (Hnepc) "/=". rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. destruct H3. rewrite H3.
                    iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". iApply "Hcls"; iFrame.
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 (inl z))); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inl z))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert. rewrite Hsome in Hsomedst; inv Hsomedst.
                          iApply "Hv"; auto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply wp_value. iExists _,fs,fr. iFrame. 
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                    (<[PC:=inr (RX, g, b, e, a)]>
                                     (if reg_eq_dec r0 dst
                                      then <[dst:=inl z]> r
                                      else <[r0:=inl z]> (<[dst:=wdst]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec dst r1).
                * subst r1; rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst).
                  -- subst r1; rewrite lookup_insert; eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; eauto. }
                iFrame. iApply "Hcls".
                iFrame "∗ #".
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodePerm p)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodePerm p)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
                iFrame "Hinv". iApply "Hcls"; iFrame.
          - iApply (wp_GetP_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            iApply wp_pure_step_later; auto.
            iApply wp_value. iExists _,fs,fr. iFrame. 
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. } iFrame "#".
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (<[dst:=(if reg_eq_dec PC r0
               then inl (encodePerm RX)
               else
                match wr0 with
                | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                | inr (p', _, _, _, _) => inl (encodePerm p')
                end)]> (if reg_eq_dec PC r0 then r else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (delete PC r) dst _).
              destruct (reg_eq_dec PC dst); try congruence.
              iFrame.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (<[dst:=inl _]> r) PC _).
              rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
              auto.
            - destruct (reg_eq_dec r0 dst).
              + subst r0. iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete PC r) dst _).
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> r) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
                auto.
              + iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete dst (delete PC r)) r0 _).
                rewrite delete_commute. iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[r0:=wr0]> (delete PC r)) dst _).
                rewrite delete_insert_ne; auto.
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> (<[r0:=_]> r)) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto.
                rewrite (delete_insert_ne _ PC r0 _); auto.
                iFrame.
                auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iFrame.
          iAssert (∀ r1 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]>
                                             (<[dst:=if reg_eq_dec PC r0
                                                     then inl (encodePerm RX)
                                                     else
                                                       match wr0 with
                                                       | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                                                       | inr (p', _, _, _, _) => inl (encodePerm p')
                                                       end]>
                                              (if reg_eq_dec PC r0
                                               then r
                                               else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r))
                                               !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec PC r1).
            - subst r1. rewrite lookup_insert; eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec dst r1).
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec PC r0); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 dst); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame.
          iApply "Hcls".
          iFrame "∗ #". }
      + (* GetB *)
        rewrite delete_insert_delete.
        iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
        destruct H2 as [wdst Hsomedst].
        iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
        destruct H2 as [wr0 Hsomer0].
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
          iNext. iIntros "(HPC & Ha & Hr0)".
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of b) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (_, _, b', e', a') => inl (z_of b') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=if reg_eq_dec PC r0
                                                         then inl (z_of b)
                                                         else
                                                          match wr0 with
                                                          | inl _ => inr (RX, g, b, e, a)
                                                          | inr (p', _, b', e', a') => inl (z_of b')
                                                          end]> (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)
                                                                  !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0).
              + iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame. iApply "Hcls".
          iFrame "∗ #". }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetB_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of b)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers (<[dst:=inl (z_of b)]> r)) as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                iSplit; auto.
                - iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (Hnepc) "/=". rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. destruct H3. rewrite H3.
                    iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". iApply "Hcls"; iFrame.
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 (inl z))); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inl z))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert. rewrite Hsome in Hsomedst; inv Hsomedst.
                          iApply "Hv"; auto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply wp_value. iExists _,fs,fr. iFrame. 
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                    (<[PC:=inr (RX, g, b, e, a)]>
                                     (if reg_eq_dec r0 dst
                                      then <[dst:=inl z]> r
                                      else <[r0:=inl z]> (<[dst:=wdst]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec dst r1).
                * subst r1; rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst).
                  -- subst r1; rewrite lookup_insert; eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; eauto. }
                iFrame. iApply "Hcls".
                iFrame "∗ #".
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a3)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a3)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
                iFrame "Hinv". iApply "Hcls"; iFrame.
          - iApply (wp_GetB_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            iApply wp_pure_step_later; auto.
            iApply wp_value. iExists _,fs,fr. iFrame. 
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. } iFrame "#".
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (<[dst:=(if reg_eq_dec PC r0
               then inl (z_of b)
               else
                match wr0 with
                | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                | inr (p', _, b', e', a') => inl (z_of b')
                end)]> (if reg_eq_dec PC r0 then r else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (delete PC r) dst _).
              destruct (reg_eq_dec PC dst); try congruence.
              iFrame.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (<[dst:=inl _]> r) PC _).
              rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
              auto.
            - destruct (reg_eq_dec r0 dst).
              + subst r0. iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete PC r) dst _).
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> r) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
                auto.
              + iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete dst (delete PC r)) r0 _).
                rewrite delete_commute. iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[r0:=wr0]> (delete PC r)) dst _).
                rewrite delete_insert_ne; auto.
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> (<[r0:=_]> r)) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto.
                rewrite (delete_insert_ne _ PC r0 _); auto.
                iFrame.
                auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iFrame.
          iAssert (∀ r1 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]>
                                             (<[dst:=if reg_eq_dec PC r0
                                                     then inl (z_of b)
                                                     else
                                                       match wr0 with
                                                       | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                                                       | inr (p', _, b', e', a') => inl (z_of b')
                                                       end]>
                                              (if reg_eq_dec PC r0
                                               then r
                                               else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r))
                                               !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec PC r1).
            - subst r1. rewrite lookup_insert; eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec dst r1).
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec PC r0); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 dst); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame.
          iApply "Hcls".
          iFrame "∗ #". }
      + (* GetE *)
        rewrite delete_insert_delete.
        iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
        destruct H2 as [wdst Hsomedst].
        iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
        destruct H2 as [wr0 Hsomer0].
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
          iNext. iIntros "(HPC & Ha & Hr0)".
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of e) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (_, _, b', e', a') => inl (z_of e') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=if reg_eq_dec PC r0
                                                         then inl (z_of e)
                                                         else
                                                          match wr0 with
                                                          | inl _ => inr (RX, g, b, e, a)
                                                          | inr (p', _, b', e', a') => inl (z_of e')
                                                          end]> (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)
                                                                  !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0).
              + iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame. iApply "Hcls".
          iFrame "∗ #". }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetE_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of e)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers (<[dst:=inl (z_of e)]> r)) as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                iSplit; auto.
                - iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (Hnepc) "/=". rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. destruct H3. rewrite H3.
                    iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". iApply "Hcls"; iFrame.
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 (inl z))); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inl z))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert. rewrite Hsome in Hsomedst; inv Hsomedst.
                          iApply "Hv"; auto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply wp_value. iExists _,fs,fr. iFrame. 
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                    (<[PC:=inr (RX, g, b, e, a)]>
                                     (if reg_eq_dec r0 dst
                                      then <[dst:=inl z]> r
                                      else <[r0:=inl z]> (<[dst:=wdst]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec dst r1).
                * subst r1; rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst).
                  -- subst r1; rewrite lookup_insert; eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; eauto. }
                iFrame. iApply "Hcls".
                iFrame "∗ #".
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a2)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a2)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
                iFrame "Hinv". iApply "Hcls"; iFrame.
          - iApply (wp_GetE_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            iApply wp_pure_step_later; auto.
            iApply wp_value. iExists _,fs,fr. iFrame. 
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. } iFrame "#".
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (<[dst:=(if reg_eq_dec PC r0
               then inl (z_of e)
               else
                match wr0 with
                | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                | inr (p', _, b', e', a') => inl (z_of e')
                end)]> (if reg_eq_dec PC r0 then r else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (delete PC r) dst _).
              destruct (reg_eq_dec PC dst); try congruence.
              iFrame.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (<[dst:=inl _]> r) PC _).
              rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
              auto.
            - destruct (reg_eq_dec r0 dst).
              + subst r0. iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete PC r) dst _).
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> r) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
                auto.
              + iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete dst (delete PC r)) r0 _).
                rewrite delete_commute. iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[r0:=wr0]> (delete PC r)) dst _).
                rewrite delete_insert_ne; auto.
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> (<[r0:=_]> r)) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto.
                rewrite (delete_insert_ne _ PC r0 _); auto.
                iFrame.
                auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iFrame.
          iAssert (∀ r1 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]>
                                             (<[dst:=if reg_eq_dec PC r0
                                                     then inl (z_of e)
                                                     else
                                                       match wr0 with
                                                       | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                                                       | inr (p', _, b', e', a') => inl (z_of e')
                                                       end]>
                                              (if reg_eq_dec PC r0
                                               then r
                                               else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r))
                                               !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec PC r1).
            - subst r1. rewrite lookup_insert; eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec dst r1).
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec PC r0); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 dst); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame.
          iApply "Hcls".
          iFrame "∗ #". }
      + (* GetA *)
        rewrite delete_insert_delete.
        iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
        destruct H2 as [wdst Hsomedst].
        iDestruct (extract_lookup_reg r r0 with "Hreg") as "%". 
        destruct H2 as [wr0 Hsomer0].
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
          iDestruct (extract_from_region _ _ a with
                         "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iExact "Hva". }
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (z_of a) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (_, _, b', e', a') => inl (z_of a') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value. iExists _,fs,fr. iFrame. 
          iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
          { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                                  (<[PC:=if reg_eq_dec PC r0
                                                         then inl (z_of a)
                                                         else
                                                          match wr0 with
                                                          | inl _ => inr (RX, g, b, e, a)
                                                          | inr (p', _, b', e', a') => inl (z_of a')
                                                          end]> (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)
                                                                  !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec PC r0).
              + iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame. iApply "Hcls".
          iFrame "∗ #". }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetA_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of a)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers (<[dst:=inl (z_of a)]> r)) as "Hreg'".
              { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                iSplit; auto.
                - iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (Hnepc) "/=". rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. destruct H3. rewrite H3.
                    iApply "Hv"; auto. }
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
              iFrame "Hinv". iApply "Hcls"; iFrame.
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl z]> r else <[r0:=inl z]> (<[dst:=wdst]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 (inl z))); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inl z))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r dst r1 _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert. rewrite Hsome in Hsomedst; inv Hsomedst.
                          iApply "Hv"; auto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply wp_value. iExists _,fs,fr. iFrame. 
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. } iFrame "#".
          iAssert (∀ r1 : RegName, ⌜is_Some
                                    (<[PC:=inr (RX, g, b, e, a)]>
                                     (if reg_eq_dec r0 dst
                                      then <[dst:=inl z]> r
                                      else <[r0:=inl z]> (<[dst:=wdst]> r)) !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec r1 PC).
            - subst r1. rewrite lookup_insert. eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r0 dst).
              + destruct (reg_eq_dec dst r1).
                * subst r1; rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  destruct (reg_eq_dec r1 dst).
                  -- subst r1; rewrite lookup_insert; eauto.
                  -- rewrite lookup_insert_ne; auto.
                     iApply extract_lookup_reg; eauto. }
                iFrame. iApply "Hcls".
                iFrame "∗ #".
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a1)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a1)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
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
                iAssert (interp_registers (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "Hreg'".
                { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
                  iSplit; auto.
                  - iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (Hnepc) "/=". rewrite /RegLocate.
                    destruct H3 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                        iApply "Hv"; auto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "Hreg' Hmap Hsts").
                iFrame "Hinv". iApply "Hcls"; iFrame.
          - iApply (wp_GetA_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iDestruct (extract_from_region _ _ a with
                           "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. rewrite H2. iFrame. iExact "Hva". }
            iApply wp_pure_step_later; auto.
            iApply wp_value. iExists _,fs,fr. iFrame. 
            iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
            { iPureIntro. apply related_sts_refl. } iFrame "#".
            iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a)]> (<[dst:=(if reg_eq_dec PC r0
               then inl (z_of a)
               else
                match wr0 with
                | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                | inr (p', _, b', e', a') => inl (z_of a')
                end)]> (if reg_eq_dec PC r0 then r else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (delete PC r) dst _).
              destruct (reg_eq_dec PC dst); try congruence.
              iFrame.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete (<[dst:=inl _]> r) PC _).
              rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
              auto.
            - destruct (reg_eq_dec r0 dst).
              + subst r0. iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete PC r) dst _).
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> r) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto. iFrame.
                auto.
              + iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (delete dst (delete PC r)) r0 _).
                rewrite delete_commute. iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[Hdst Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[r0:=wr0]> (delete PC r)) dst _).
                rewrite delete_insert_ne; auto.
                iFrame.
                iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
                eapply lookup_insert.
                erewrite (delete_insert_delete (<[dst:=_]> (<[r0:=_]> r)) PC _).
                rewrite (delete_insert_ne _ PC dst _ n); auto.
                rewrite (delete_insert_ne _ PC r0 _); auto.
                iFrame.
                auto. }
          iAssert (interp_registers (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iIntros (r1). iDestruct ("Hreg" $! (r1)) as "[% Hv]".
            iSplit; auto.
            - iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (Hnepc). destruct (reg_eq_dec PC r0); eauto.
              + iApply "Hv"; auto.
              + destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                  iApply "Hv"; auto.
                * rewrite /RegLocate lookup_insert_ne; auto. iApply "Hv"; auto. }
          iFrame.
          iAssert (∀ r1 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]>
                                             (<[dst:=if reg_eq_dec PC r0
                                                     then inl (z_of a)
                                                     else
                                                       match wr0 with
                                                       | inl _ => if reg_eq_dec r0 dst then wr0 else wdst
                                                       | inr (p', _, b', e', a') => inl (z_of a')
                                                       end]>
                                              (if reg_eq_dec PC r0
                                               then r
                                               else if reg_eq_dec r0 dst then r else <[r0:=wr0]> r))
                                               !! r1)⌝)%I as "HA".
          { iIntros. destruct (reg_eq_dec PC r1).
            - subst r1. rewrite lookup_insert; eauto.
            - rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec dst r1).
              + subst r1. rewrite lookup_insert; eauto.
              + rewrite lookup_insert_ne; auto.
                destruct (reg_eq_dec PC r0); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 dst); [iApply extract_lookup_reg; eauto|].
                destruct (reg_eq_dec r0 r1).
                * subst r1. rewrite lookup_insert; eauto.
                * rewrite lookup_insert_ne; auto.
                  iApply extract_lookup_reg; eauto. }
          iFrame.
          iApply "Hcls".
          iFrame "∗ #". }
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct (extract_from_region _ _ a with
                       "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. iExact "Hva". }
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert.
        iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,fr. iFrame.
        iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto.
            iApply extract_lookup_reg; eauto. }
        iFrame. iApply "Hcls". iNext. iFrame.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct (extract_from_region _ _ a with
                       "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. iExact "Hva". }
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert.
        iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,fr. iFrame.
        iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto.
            iApply extract_lookup_reg; eauto. }
        iFrame. iApply "Hcls". iNext. iFrame.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))). 
      iApply (wp_notCorrectPC with "HPC"); eauto.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iApply wp_value.
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
      apply lookup_insert. rewrite delete_insert_delete. iFrame.
      rewrite insert_insert.
      iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,fr. iFrame.
      iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
      { iPureIntro. apply related_sts_refl. }
      iFrame "#". iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
      { iIntros. destruct (reg_eq_dec PC r0).
        - subst r0; rewrite lookup_insert; eauto.
        - rewrite lookup_insert_ne; auto.
          iApply extract_lookup_reg; eauto. }
      iFrame.
  }
  { admit. }
  { admit. }
  Admitted.  
  
  Theorem fundamental (perm : Perm) b e g (a : Addr) :
    (⌜perm = RX⌝ ∧ ∃ ws, (inv (logN .@ (b,e)) (read_only_cond b e ws interp)%I)) ∨
    (⌜perm = RWX⌝ ∧ (inv (logN .@ (b,e)) (read_write_cond b e interp)%I)) ∨
    (⌜perm = RWLX⌝ ∧ (inv (logN .@ (b,e)) (read_write_local_cond b e interp)%I)) -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ.
  Proof. 
    iIntros "[#[-> Hinv] | [#[-> Hinv] | #[-> Hinv]]]".
    - iDestruct "Hinv" as (ws) "Hinv". by iApply fundamental_RX.
    - by iApply fundamental_RWX.
    - by iApply fundamental_RWLX.
  Qed.

End fundamental. 