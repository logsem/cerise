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
    - iAssert (⌜is_Some (reg !! r)⌝ ∧ (⌜r ≠ PC⌝ → (fixpoint interp1) (reg !r! r)))%I
        with "Hreg" as "Hreg". 
      iDestruct ("Hreg") as "[Hr Hreg]". done. 
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
      + admit. (* Jmp *)
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
          iFrame "#". iApply "Hcls". iNext. iFrame. 
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
            iFrame "#". iApply "Hcls". iNext. iFrame. 
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
              iFrame "#". iApply "Hcls". iNext. iFrame. 
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
                    {{ v, (λne _ : valC cap_lang, ∃ r0 fs' fr',
                          registers_mapsto r0 ∗ ⌜related_sts fs fs' fr fr'⌝
                                           ∗ sts_full fs' fr') v }} }})%I
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
                iFrame "#". iApply "Hcls". iFrame. iApply "Hcls'". iFrame. (* iNext. *)
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
                iFrame "#". iApply "Hcls". iFrame. iApply "Hcls'". iFrame.
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
              try ( iDestruct ("Hfail" with "Htrivial HPC") as "Hfail";
                    iApply (wp_wand with "Hfail");
                    iAssert ((∀ v : val cap_lang, ⌜v = FailedV⌝
                                ∗ PC ↦ᵣ inr (_, l0, a5, a4, a6)
                               -∗ ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                               registers_mapsto r0 ∗ ⌜related_sts fs fs' fr fr'⌝
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
                      iExists _,fs,fr; iFrame; iPureIntro; apply related_sts_refl
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
                iApply ("IH" $! _ _ _ _ _ _ _ ws1 with "Hreg' Hmap Hsts").
                iFrame "Hb0e0".
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
        * iDestruct (extract_lookup_reg r dst with "Hreg") as "%".
          destruct H2 as [wdst Hsomedst]. 
          assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          rewrite delete_insert_delete.
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto. 
          destruct (a + 1)%a eqn:Ha'. 
          2: (* if PC cannot be incremented ==> dst is updated, then program crashes *)
            { iApply (wp_load_fail6 with "[HPC Hdst Ha]"); eauto.
              iFrame. iNext. iIntros "[HPC [Ha Hdst]] /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iExists _,fs,fr. iFrame. 
              iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
              { iPureIntro. apply related_sts_refl. }
              iFrame "#".
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
            iFrame "#". iApply "Hcls". iNext. iFrame. 
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
              iFrame "#". iApply "Hcls". iNext. iFrame. 
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
                    {{ v, (λne _ : valC cap_lang, ∃ r0 fs' fr',
                          registers_mapsto r0 ∗ ⌜related_sts fs fs' fr fr'⌝
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
                   iApply wp_value. iExists _,fs,fr. iFrame. 
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
                   iApply wp_value. iExists _,fs,fr. iFrame. 
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
      + admit. (* IsPtr *)
      + admit. (* GetL *)
      + admit. (* GetP *)
      + admit. (* GetB *)
      + admit. (* GetE *)
      + admit. (* GetA *)
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
        iFrame "#". iApply "Hcls". iNext. iFrame.
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
        iFrame "#". iApply "Hcls". iNext. iFrame.
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
      iFrame "#".
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
    - (* read and write condition, non local *) admit. 
    - (* read and write condition, permit local *) admit. 
  Admitted.

End fundamental. 