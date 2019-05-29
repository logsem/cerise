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
    ⟦ inr ((RX,g),b,e,a) ⟧ₑ )%I. 
  Proof.
    iIntros "#Hinv /=".
    iIntros (r m fs fr) "[Hreg [Hmreg Hsts]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iLöb as "IH" forall (r a fs fr). 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iInv (logN.@(b, e)) as "Hregion" "Hcls".      
      iDestruct (extract_from_region _ _ a with "Hregion")
        as (al w ah) "(Hal & Hah & Hregionl & Hvalidl & >Ha & #Hva & Hregionh & Hvalidh)";
        auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))). 
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + admit. (* Jmp *)
      + admit. (* Jnz *)
      + admit. (* Mov *)
      + (* Load *)
        (* TODO: destruct between success and fail, and different versions of the rule *)
        destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
        * (* Load PC PC ==> fail *)
          iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
          iNext. iIntros "[HPC Ha] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iDestruct (extract_from_region _ _ a with
               "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
          { iExists al,w,ah. iFrame. iExact "Hva". }
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
                 "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
            { iExists al,w,ah. iFrame. iExact "Hva". }
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
                 "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
            { iExists al,w,ah. iFrame. iExact "Hva". }
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
          iDestruct "Hconds" as "[#Hro|#[Hrw|Hrwl]]".
          (* each condition is similar, but with some subtle differences *)
          { iDestruct "Hro" as (ws0) "Hinv0".
            (* open the invariant to access a0 ↦ₐ _ *)
            iInv (logN.@(a2, a1)) as "Hro_cond" "Hcls'";[admit|].
            iDestruct (extract_from_region _ _ a0 with "Hro_cond")
            as (a0l w0 a0h)
            "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            (* if w0 is a Z, load crashes *)
            destruct w0.
            { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]"); eauto.
              - split; apply Is_true_eq_true; eauto.
                apply andb_prop_intro. split; [apply Hle|apply Hge].
              - iFrame.
              - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iDestruct (extract_from_region _ _ a with
                  "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
                { iExists al,w,ah. iFrame. iExact "Hva". }
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iExists _,fs,fr. iFrame.
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. }
                iFrame "#". iApply "Hcls". iFrame. iApply "Hcls'". iNext.
                iApply (extract_from_region _ _ a0);
                  first (split; by apply Z.leb_le,Is_true_eq_true).
                iFrame. iExists a0l, (inl z), a0h. iFrame. iExact "Hva0". 
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
                  "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
                { iExists al,w,ah. iFrame. iExact "Hva". }
                iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iExists _,fs,fr. iFrame.
                iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl". 
                { iPureIntro. apply related_sts_refl. }
                iFrame "#". iApply "Hcls". iFrame. iApply "Hcls'". iNext.
                iApply (extract_from_region _ _ a0);
                  first (split; by apply Z.leb_le,Is_true_eq_true).
                iFrame. iExists a0l, _, a0h. iFrame. iExact "Hva0". 
            }
            (* success load into PC *)
            iApply (wp_load_success_PC with "[HPC Ha Hsrc Ha0]"); eauto.
            - split; apply Is_true_eq_true; eauto.
              apply andb_prop_intro. split; [apply Hle|apply Hge].
            - iFrame.
            - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
              iApply wp_pure_step_later; auto.
              iDestruct (extract_from_region _ _ a with
                "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]") as "Hregion"; eauto.
              { iExists al,w,ah. iFrame. iExact "Hva". }
              iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              admit. 
              (* iApply ("IH" with "[Hmap]"). *)
              (* iFrame.  *)
              (* rewrite /registers_mapsto. *)

              (* iExists _,fs,fr. iFrame. *)
              (* iAssert (⌜related_sts fs fs fr fr⌝)%I as "#Hrefl".  *)
              (* { iPureIntro. apply related_sts_refl. } *)
              (* iFrame "#". iApply "Hcls". iFrame. iApply "Hcls'". iNext. *)
              (* iApply (extract_from_region _ _ a0); *)
              (*   first (split; by apply Z.leb_le,Is_true_eq_true). *)
              (* iFrame. iExists a0l, _, a0h. iFrame. iExact "Hva0".  *)
              
          }
          { admit. }
          { admit. }
        * (* Load dst PC *) admit.
        * (* Load dst src *) admit. 
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
      + admit. (* Fail *)
      + admit. (* Halt *)   
    - (* Incorrect PC *) admit.
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