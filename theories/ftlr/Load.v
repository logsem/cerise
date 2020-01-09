From stdpp Require Import base. 
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.

Lemma region_open_next
    (Σ : gFunctors) (H : heapG Σ) (H0 : memG Σ) (H2 : STSG Σ) (MonRef : MonRefG _ Σ) 
    (W : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels))) 
    (φ : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)) * Word → iProp Σ) 
    (ls : list Addr) (l : Addr) (p : Perm) (ρ : region_type) (Hρnotrevoked : ρ <> Revoked):
    l ∉ ls
    → std_sta W !! countable.encode l = Some (countable.encode ρ)
      → open_region_many ls W ∗ rel l p φ ∗ sts_full_world sts_std W
        -∗ ∃ v : Word,
             sts_full_world sts_std W
             ∗ sts_state_std (countable.encode l) ρ
               ∗ open_region_many (l :: ls) W
               ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ ▷ (match ρ with
                                          | Permanent => future_priv_mono
                                          | Temporary => if pwl p then
                                                          future_pub_mono
                                                        else future_priv_mono
                                          | Revoked => fun _ _ => True%I
                                          end) φ v ∗
               ▷ φ (W, v).
Proof.
  intros. iIntros "H".
  destruct ρ; try congruence.
  - case_eq (pwl p); intros.
    + iDestruct (region_open_next_temp_pwl with "H") as (v) "[A [B [C D]]]"; eauto.
      iExists v. iFrame.
    + iDestruct (region_open_next_temp_nwl with "H") as (v) "[A [B [C D]]]"; eauto.
      iExists v. iFrame.
  - iApply (region_open_next_perm with "H"); eauto.
Qed.

Lemma region_close_next
    (Σ : gFunctors) (H : heapG Σ) (H0 : memG Σ) (H2 : STSG Σ) (MonRef : MonRefG _ Σ) 
    (W : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels))) 
    (φ : prodO (leibnizO (STS_states * STS_rels)) (leibnizO (STS_states * STS_rels)) * Word → iProp Σ) 
    (ls : list Addr) (l : Addr) (p : Perm) (v : Word) (ρ : region_type) (Hρnotrevoked : ρ <> Revoked):
    l ∉ ls
    → sts_state_std (countable.encode l) ρ
      ∗ open_region_many (l :: ls) W
        ∗ l ↦ₐ[p] v ∗ ⌜p ≠ O⌝ ∗ (match ρ with
                                          | Permanent => future_priv_mono
                                          | Temporary => if pwl p then
                                                          future_pub_mono
                                                        else future_priv_mono
                                          | Revoked => fun _ _ => True%I
                                          end) φ v ∗ ▷ φ (W, v) ∗ rel l p φ -∗ 
        open_region_many ls W.
Proof.
  intros. iIntros "[A [B [C [D [E [F G]]]]]]".
  destruct ρ; try congruence.
  - case_eq (pwl p); intros.
    + iApply (region_close_next_temp_pwl with "[A B C D E F G]"); eauto; iFrame.
    + iApply (region_close_next_temp_nwl with "[A B C D E F G]"); eauto; iFrame.
  - iApply (region_close_next_perm with "[A B C D E F G]"); eauto; iFrame.
Qed.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma withinBounds_le_addr p l b e a:
    withinBounds (p, l, b, e, a) = true ->
    (b <= a)%a ∧ (a <= e)%a.
  Proof.
    simpl; intros A. eapply andb_true_iff in A.
    unfold le_addr in *. unfold leb_addr in *.
    generalize (proj1 (Z.leb_le _ _) (proj1 A)).
    generalize (proj1 (Z.leb_le _ _) (proj2 A)).
    lia.
  Qed.

  Lemma readAllowed_valid_cap_implies W p l b e a:
    readAllowed p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a)) -∗
    ⌜region_std W a /\ ∃ ρ, std_sta W !! countable.encode a = Some (countable.encode ρ) /\ ρ <> Revoked⌝.
  Proof.
    intros. iIntros "Hvalid".
    eapply withinBounds_le_addr in H4.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H3; try congruence.
    - iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - destruct l; auto.
      iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
    - iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - destruct l; auto.
      iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
  Qed.

  Lemma load_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst src : RegName) :
    ftlr_instr W r p p' g b e a w (Load dst src) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
    * (* Load PC PC ==> fail *)
      iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      iApply wp_value.
      iNext. iIntros "%"; inversion a0.
    * (* Load PC src ==> success if src ↦ inr, fail o/w *)
      specialize Hsome with src as Hsrc. 
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
      destruct c. do 3 destruct p0.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p0 && withinBounds ((p0,l),a2,a1,a0)) = false)).
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
      iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto; 
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
      iDestruct "Hconds" as (p0' Hfl') "Hrel'".
      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
      { rewrite /withinBounds /leb_addr Hle Hge. auto. }
      destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
      iDestruct (region_open_next _ _ _ _ _ _ _ _ a0 p0' ρ' with "[$Hrel' $Hr $Hsts]") as (w0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
      { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
      iAssert (∀ w1 w2, full_map (<[PC:=w1]> (<[src:=w2]> r)))%I as "#Hfull'".
      { iIntros (w1 w2 r0).
        iPureIntro.
        destruct (decide (PC = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
        rewrite lookup_insert_ne.
        destruct (decide (src = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
        rewrite lookup_insert_ne. apply Hsome. done. done.
      }
      destruct w0.
      { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]")
        ;[eauto|apply Hfp|apply Hfl'| | | | |]; eauto. 
        - split; [eauto|]. apply Is_true_eq_true; eauto.
          apply andb_prop_intro.
          split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
        - destruct (a0 =? a)%a; iFrame. 
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros "%"; inversion a3. 
      }
      destruct c,p1,p1,p1.
      destruct ((a3 + 1)%a) eqn:Ha0.
      2: { (* If src points to top address, load crashes *)
        iApply (wp_load_fail4 with "[HPC Hsrc Ha Ha0]")
        ;[eauto|apply Hfp|apply Hfl'| | | | | |]; eauto.
        - split; [eauto|]. apply Is_true_eq_true; eauto.
          apply andb_prop_intro.
          split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
        - destruct (a0 =? a)%a; iFrame. 
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr. 
      }
      (* successful load into PC *)
      iApply (wp_load_success_PC with "[$HPC $Ha $Hsrc Ha0]")
      ;[eauto|apply Hfp|apply Hfl'| | | | |]; eauto.
      { split; [eauto|]. apply Is_true_eq_true; eauto.
        apply andb_prop_intro.
        split; apply Is_true_eq_left; [apply Hle|apply Hge].  }
      iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
      iApply wp_pure_step_later; auto. iNext. 
      iAssert (⌜p1 ≠ RX⌝ ∧ ⌜p1 ≠ RWX⌝ ∧ ⌜p1 ≠ RWLX⌝ →
               PC ↦ᵣ inr (p1, l0, a5, a4, a6) -∗
                  WP Seq (Instr Executable) {{ w, ⌜w = FailedV⌝
                    ∗ PC ↦ᵣ inr (p1, l0, a5, a4, a6) }})%I
            as "Hfail".
      { iIntros "(% & % & %) HPC".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "[HPC]");
              [apply not_isCorrectPC_perm;eauto|iFrame|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iFrame. done.
      }
      (* The new register state is valid *)
      iAssert (interp_registers W (<[src:=inr (p0, l, a2, a1, a0)]> r)) as "[#Hfull'' #Hreg'']".
      { iSplitL.
        { iIntros (r0). iPureIntro.
          destruct (decide (src = r0)); simplify_eq;
            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
        iIntros (r0) "%".
        destruct (decide (src = r0)); simplify_eq.
        + by rewrite /RegLocate lookup_insert.
        + rewrite /RegLocate lookup_insert_ne; auto.
          iDestruct ("Hreg" $! (r0) a7) as "Hr0".
          specialize Hsome with r0.
          destruct Hsome as [c Hsome].
          rewrite Hsome. iApply "Hr0"; auto.
      }
      (* close region *)
      iDestruct (region_close_next with "[$Hr $Ha0 $Hrel' $Hstate' $Hfuture]") as "Hr"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      iDestruct (region_open_prepare with "Hr") as "Hr". 
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      destruct (perm_eq_dec p1 RX).
      { iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. 
        iAlways. subst p1.
        rewrite (fixpoint_interp1_eq _ (inr (RX, l0, a5, a4, a3))) /=.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      destruct (perm_eq_dec p1 RWX).
      { subst p1. iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. 
        iAlways.
        rewrite (fixpoint_interp1_eq _ (inr (RWX, l0, a5, a4, a3))) /=.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      destruct (perm_eq_dec p1 RWLX).
      { subst p1. iClear "Hfail".
        iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
          rewrite -delete_insert_ne; auto;
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
        rewrite (fixpoint_interp1_eq _ (inr (RWLX, l0, a5, a4, a3))) /=.
        destruct l0; auto.
        (* apply IH *)
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. 
        iAlways.
        iDestruct "Hval" as (q Hq) "[Hb0e0 Hexec]".
        iExists q. iSplit; auto. }
      iDestruct ("Hfail" with "[%] [HPC]") as "Hfail"; auto.
      iApply (wp_wand with "Hfail"). iIntros (v) "[-> HPC]".
      iIntros. discriminate.
    * destruct (Hsome dst) as [wdst Hsomedst].
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
        iAssert (▷ interp_registers _ (<[dst:=w]> r))%I
          as "#[Hfull' Hreg']".
        { iNext. iSplitL.
          { iIntros (r0). iPureIntro.
            destruct (decide (dst = r0)); simplify_eq;
              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
          iIntros (r0) "%".
          destruct (decide (dst = r0)); simplify_eq.
              + by rewrite /RegLocate lookup_insert.
              + rewrite /RegLocate lookup_insert_ne; auto.
                iDestruct ("Hreg" $! (r0) a1) as "Hr0".
                specialize Hsome with r0. 
                destruct Hsome as [c Hsome].
                rewrite Hsome. iApply "Hr0"; auto.
        } 
        iNext.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#". 
    * destruct (Hsome src) as [wsrc Hsomesrc].
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
      destruct c. do 3 destruct p0.
       (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p0 && withinBounds ((p0,l),a2,a1,a0)) = false)).
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
      iAssert ((fixpoint interp1) _ (inr (p0, l, a2, a1, a0))) as "#Hvsrc".
      { apply reg_eq_sym in n0. iDestruct ("Hreg" $! src n0) as "Hvsrc".
        rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
      iDestruct (read_allowed_inv _ a0 with "Hvsrc") as "Hconds"; auto; 
        first (split; by apply Z.leb_le).
      (* Each condition in Hconds take a step in similar fashion *)
      iAssert ((∃ w' p'', ▷ ((if (a0 =? a)%a then emp else a0 ↦ₐ[p''] w') -∗ open_region a W)
                            ∗ (if (a0 =? a)%a then emp else ▷ a0 ↦ₐ[p''] w')
                            ∗ ▷ ▷ (fixpoint interp1) W w' ∗ ⌜PermFlows p0 p''⌝
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
        ∗ sts_full_world sts_std W
        -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (W' : leibnizO (STS * STS)),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv_world W W'⌝
                                           ∗ na_own logrel_nais ⊤ ∗ sts_full_world sts_std W' ∗ region W' }} }} )%I
        with "[Ha HPC Hsrc Hmap Hown Hstate Hmono]" as "Hstep".
      { iIntros "[Hres Hsts]".
        iDestruct "Hres" as (w0 p'') "[Hr [Ha0 [#Hw0 %]]]". 
        (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        destruct (a + 1)%a eqn:Ha'; simplify_eq.
        2: { destruct (decide (src = dst)); simplify_eq. 
             - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]");
                 [eauto|eauto|apply Hfp|apply H3| | | | | | ]; eauto.
               { split; apply Is_true_eq_true; [eauto|]. 
                 apply andb_prop_intro.
                 split; apply Is_true_eq_left; [apply Hle|apply Hge]. 
               }
               iFrame. iNext. iIntros "[HPC [Ha [Hdst Ha0]]] /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
             - destruct (Hsome dst) as [wdst Hsomedst].
               assert (delete PC r !! dst = Some wdst) as Hsomedst'.
               { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
               assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
               { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
                 eauto. }
               iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
                 eauto.
               iApply (wp_load_fail7 with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H3| | | | | | ]; eauto.
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
                 [eauto|eauto|apply Hfp|apply H3| | | | | | ]; eauto.
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
          iAssert (▷ interp_registers W (<[dst:=if (a0 =? a)%a then w else w0]> r))%I as "#[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              iPureIntro.
              destruct (Hsome r0) as [c Hsomec]. 
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "% /=".
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (Hsome r0) as [c Hsomec]. 
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert.
                destruct (a0 =? a)%a;[iApply "Hw"|iApply "Hw0"]. 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsomec. iApply "Hv"; auto.  
          }
          iNext.
          iSpecialize ("Hr" with "Ha0").
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#". 
        - destruct (Hsome dst) as [wdst Hsomedst].
          assert (delete PC r !! dst = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
          { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
            eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
            eauto.
          iApply (wp_load_success with "[HPC Hsrc Hdst Ha Ha0]");
                 [eauto|apply Hfp|apply H3| | | | | | ]; eauto.
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
          iAssert (▷ interp_registers _ (<[src:=inr (p0, l, a2, a1, a0)]>
                                         (<[dst:=if (a0 =? a)%a then w else w0]> r)))%I
                    as "#[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              destruct (Hsome r0) as [c Hsomec].
              iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "%".
              destruct (Hsome r0) as [c Hsomec].
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (decide (src = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert.
                iApply "Hvsrc". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsomec. destruct (decide (dst = r0)); simplify_eq.
                * rewrite lookup_insert. destruct (a0 =? a)%a; auto. 
                * rewrite lookup_insert_ne. rewrite Hsomec. iApply "Hv"; auto.
                  auto. 
          }
          iNext.
          iSpecialize ("Hr" with "Ha0").
          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto; iFrame "#". 
      }
      destruct (decide (a = a0)).
      { iApply "Hstep". iFrame "Hsts".
        iExists w,p0.
        destruct (a0 =? a)%a eqn:Ha0; [|apply Z.eqb_neq in Ha0;congruence].
        iFrame "#". iSplitL.
        - iIntros "_". iFrame. 
        - iPureIntro. apply PermFlows_refl. 
      }
      iDestruct "Hconds" as (p'' Hp'') "Hinv0". 
      iDestruct (region_open_prepare with "Hr") as "Hr".
      iDestruct (readAllowed_valid_cap_implies with "Hvsrc") as "%"; eauto.
      { rewrite /withinBounds /leb_addr Hle Hge. auto. }
      destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
      rewrite /read_write_cond.
      iDestruct (region_open_next _ _ _ _ _ _ _ _ a0 p'' ρ' with "[$Hinv0 $Hr $Hsts]") as (w0) "(Hsts & Hstate' & Hr & Ha0 & % & Hmono' & #Hw0)"; eauto.
      { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
      iApply "Hstep". iFrame.
      iExists w0,p''. 
      destruct (a0 =? a)%a eqn:Ha0; [apply Z.eqb_eq,z_of_eq in Ha0;congruence|].
      iFrame "∗ #". 
      iSplitL; auto. iNext. 
      iIntros "Ha0".
      iDestruct (region_close_next with "[$Hr $Ha0 $Hinv0 $Hstate' $Hmono']") as "Hr"; eauto.
      { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
      iDestruct (region_open_prepare with "Hr") as "$". 
      Unshelve. exact 0. 
  Qed.
      
End fundamental.