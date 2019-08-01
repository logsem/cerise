From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
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

  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl).


  Lemma fundamental_RX stsf E r b e g (a : Addr) ws :
    (na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws stsf E interp) →
     ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e stsf E interp) →
     ⟦ inr ((RWX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWLX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e stsf E interp) →
     ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I. 
  Proof.
  { destruct stsf as [fs [fr_pub fr_priv] ].
    iIntros "#Hinv /=". iExists fs,fr_pub,fr_priv.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hsts [Hown #Hreach]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv Hreach". iLöb as "IH" forall (r a g fs fr_priv b e ws).
    iIntros "#Hinv %". rename a0 into Hreach. 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as %Hbe.
      { iPureIntro. by apply Hreach. }
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto. 
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
        destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
        * (* Load PC PC ==> fail *)
          iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
          iNext. iIntros "[HPC Ha] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iDestruct (extract_from_region _ _ a with
                         "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]")
            as "[Hregion Hvalid]"; eauto.
          { iExists al,w,ah. iFrame. iExact "Hva". }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
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
            iDestruct (extract_from_region _ _ a with
                           "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]")
              as "[Hregion Hvalid]"; eauto.
            { iExists al,w,ah. iFrame. iExact "Hva". }
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
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
              iDestruct (extract_from_region _ _ a with
                             "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]")
                as "[Hregion Hvalid]"; eauto.
            { iExists al,w,ah. iFrame. iExact "Hva". }
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
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
            ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,(fr_pub,fr_priv))
                   (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
            ∗ sts_full fs fr_pub fr_priv
            -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                      → ∃ (r0 : Reg) (fs' : STS_states) (fr_pub' fr_priv' : STS_rels),
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts fs fs' fr_priv fr_priv'⌝
                                              ∗ na_own logrel_nais E
                                              ∗ sts_full fs' fr_pub' fr_priv' }} }} )%I
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
                                  → ∃ (r0 : Reg) fs' fr_pub' fr_priv',
                                       full_map r0 ∧ registers_mapsto r0 ∗ ⌜related_sts fs fs' fr_priv fr_priv'⌝
                                                                      ∗ na_own logrel_nais E
                                                                      ∗ sts_full fs' fr_pub' fr_priv'))%I
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
                iDestruct "Hexpr" as (fs0 frpub0 frpriv0) "(% & % & % & Hexpr)";
                  simplify_eq.
                iDestruct ("Hexpr" 
                             with "[Hfull' Hreg' Hmap Hsts Hown]")
                  as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame. 
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
                iDestruct "Hexpr" as (fs0 frpub0 frpriv0) "(% & % & % & Hexpr)";
                  simplify_eq.
                iDestruct ("Hexpr" 
                             with "[Hfull' Hreg' Hmap Hsts Hown]")
                  as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame.
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
          { iDestruct "Hro" as (ws0) "Hinv0".
            (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hinv0 Hown")
              as "(Hro_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct (extract_from_region _ _ a0 with "Hro_cond")
              as (a0l w0 a0h)
                   "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame "Hsts".
            iExists w0. iFrame "Ha0 Hva0". 
            iNext. iIntros "[Ha0 Ha]".
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "Hregion";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iExact "Hva0". }
            iMod ("Hcls'" with "[$Hown $Hregion]") as "Hown".
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hrw Hown")
              as "(Hrw_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond")
            as (a0l w0 a0h)
     "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #[Hva0 Hnl] & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame. 
            iExists w0. iFrame "Ha0 #".
            iNext. iIntros "[Ha0 Ha]". 
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "[Hbe Hregion]";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iFrame "#". } 
            iMod ("Hcls'" with "[$Hown Hbe Hregion]") as "Hown".
            { iNext. iExists _. iFrame. iApply big_sepL_later. iNext. iFrame. }
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hrwl Hown")
              as "(Hrwl_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct "Hrwl_cond" as (ws0) "Hrwl_cond".
            iDestruct (extract_from_region _ _ a0 with "Hrwl_cond")
            as (a0l w0 a0h)
     "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame. 
            iExists w0. iFrame "Ha0 #".
            iNext. iIntros "[Ha0 Ha]". 
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "[Hbe Hregion]";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iFrame "#". } 
            iMod ("Hcls'" with "[$Hown Hbe Hregion]") as "Hown".
            { iNext. iExists _. iFrame. iApply big_sepL_later. iNext. iFrame. }
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
        * destruct (H3 dst) as [wdst Hsomedst].  
          assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          rewrite delete_insert_delete.
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
            iAssert (▷ interp_registers _ (fs, (fr_pub, fr_priv)) (<[dst:=w]> r))%I
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
            iDestruct (extract_from_region _ _ a with
                           "[Hal Hah Hregionl Hvalidl Hregionh Hvalidh Ha]")
              as "[Hbe Hregion]"; eauto.
            iExists _,_,_; rewrite Ha'; iFrame. iExact "Hva". 
            iMod ("Hcls" with "[Hbe Hregion $Hown]") as "Hown".
            { iNext. iFrame. iApply big_sepL_later. iNext. iFrame. }
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
            ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,(fr_pub,fr_priv))
                   (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
            ∗ sts_full fs fr_pub fr_priv
            -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                      → ∃ (r0 : Reg) (fs' : STS_states) (fr_pub' fr_priv' : STS_rels),
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts fs fs' fr_priv fr_priv'⌝
                                              ∗ na_own logrel_nais E
                                              ∗ sts_full fs' fr_pub' fr_priv' }} }} )%I
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
          { iDestruct "Hro" as (ws0) "Hinv0".
            (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hinv0 Hown")
              as "(Hro_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct (extract_from_region _ _ a0 with "Hro_cond")
              as (a0l w0 a0h)
                   "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame "Hsts".
            iExists w0. iFrame "Ha0 Hva0". 
            iNext. iIntros "[Ha0 Ha]".
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "Hregion";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iExact "Hva0". }
            iMod ("Hcls'" with "[$Hown $Hregion]") as "Hown".
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hrw Hown")
              as "(Hrw_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
            iDestruct (extract_from_region _ _ a0 with "Hrw_cond")
            as (a0l w0 a0h)
     "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #[Hva0 Hnl] & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame. 
            iExists w0. iFrame "Ha0 #".
            iNext. iIntros "[Ha0 Ha]". 
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "[Hbe Hregion]";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iFrame "#". } 
            iMod ("Hcls'" with "[$Hown Hbe Hregion]") as "Hown".
            { iNext. iExists _. iFrame. iApply big_sepL_later. iNext. iFrame. }
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
          { (* open the invariant to access a0 ↦ₐ _ *)
            iMod (na_inv_open _ _ _ (logN.@(a2, a1)) with "Hrwl Hown")
              as "(Hrwl_cond & Hown & Hcls')"; auto.
            { apply namespace_subseteq_difference; auto.
              rewrite /namespace_subseteq_difference.
              by apply ndot_ne_disjoint. 
            }
            rewrite /read_only_cond.
            iDestruct "Hrwl_cond" as (ws0) "Hrwl_cond".
            iDestruct (extract_from_region _ _ a0 with "Hrwl_cond")
            as (a0l w0 a0h)
     "(Ha0l & Ha0h & Hregion0l & Hvalid0l & >Ha0 & #Hva0 & Hregion0h & Hvalid0h)";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            iApply "Hstep". iFrame. 
            iExists w0. iFrame "Ha0 #".
            iNext. iIntros "[Ha0 Ha]". 
            iDestruct (extract_from_region _ _ a0
                         with "[Hregion0l Hvalid0l Hregion0h Hvalid0h Ha0 Ha0l Ha0h]")
              as "[Hbe Hregion]";
              first (split; by apply Z.leb_le,Is_true_eq_true).
            { iFrame. iExists a0l, _, a0h. iFrame. iFrame "#". } 
            iMod ("Hcls'" with "[$Hown Hbe Hregion]") as "Hown".
            { iNext. iExists _. iFrame. iApply big_sepL_later. iNext. iFrame. }
            iDestruct (extract_from_region _ _ a
                         with "[Hregionl Hvalidl Hregionh Hvalidh Ha Hal Hah]")
              as "Hregion"; eauto. 
            { iFrame. iExists al, _, ah. iFrame. iExact "Hva". }
            iMod ("Hcls" with "[$Hown $Hregion]") as "Hown".
            iModIntro. iFrame. 
          }
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
  }
  { admit. }
  { admit. }
  Admitted.
  

  Theorem fundamental (perm : Perm) b e g (a : Addr) stsf E r :
    (⌜perm = RX⌝ ∧ ∃ ws, (na_inv logrel_nais (logN .@ (b,e))
                                 (read_only_cond b e ws stsf E interp)%I)) ∨
    (⌜perm = RWX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_cond b e stsf E interp)%I)) ∨
    (⌜perm = RWLX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_local_cond b e stsf E interp)%I)) -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ stsf E r.
  Proof. 
    iIntros "[#[-> Hinv] | [#[-> Hinv] | #[-> Hinv]]]".
    - iDestruct "Hinv" as (ws) "Hinv". by iApply fundamental_RX. 
    - by iApply fundamental_RWX. 
    - by iApply fundamental_RWLX.
  Qed.  

    
      
End fundamental. 