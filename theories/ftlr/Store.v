From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_Store.

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

  Lemma execcPC_implies_interp W p p' g b e a0:
    PermFlows p p' → p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Local →
    □ exec_cond W b e g p (fixpoint interp1) -∗
      ([∗ list] a ∈ region_addrs b e,
       rel a p'(λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word),
                       ((fixpoint interp1) Wv.1) Wv.2)
       ∧ ⌜if pwl p
          then region_state_pwl W a
          else region_state_nwl W a g⌝
               ∧ ⌜region_std W a⌝) -∗
      ((fixpoint interp1) W) (inr (p, g, b, e, a0)).
  Proof.
    iIntros (Hpf Hp) "#HEC #HR".
    rewrite (fixpoint_interp1_eq _ (inr _)).
    (do 2 try destruct Hp as [ | Hp]). 3:destruct Hp.
    all:subst; iExists p' ; by do 2 (iSplit; [auto | ]).
  Qed.

  Lemma store_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) :
    ftlr_instr W r p p' g b e a w (Store dst src) ρ.

  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.

    destruct (reg_eq_dec dst PC).
    - subst dst.
      destruct Hp as [-> | Hp].
      { (* if p is RX, write is not allowed *)
        iApply (wp_store_fail1' with "[$HPC $Ha]"); eauto.
        iNext. iIntros (_).
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iIntros. discriminate. }
      destruct src.
      + (* successful inl write into a *)
        destruct (a + 1)%a eqn:Hnext.
        { (* successful PC increment *)
          iApply (wp_store_success_z_PC with "[$HPC $Ha]"); eauto;
            [by destruct Hp as [-> | [-> _] ] |].
          iNext. iIntros "[HPC Ha]".
          iApply wp_pure_step_later; auto; iNext.
          iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".
          { iSplitR; [auto|]. iSplitL.

            {destruct (decide (ρ = Temporary ∧ pwl p' = true)); iAlways; simpl.
             - iIntros (W0 W1) "% HIW0".
                 by iApply interp_monotone.
             - iIntros (W0 W1) "% HIW0".
                 by iApply interp_monotone_nl.
            }
            iNext. simpl. by rewrite (fixpoint_interp1_eq _ (inl _)).
          }

          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
            as "Hmap"; [by rewrite lookup_delete|].
          rewrite insert_delete.
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.

        }
        { (* failure to increment PC *)
          iApply (wp_store_fail_z_PC_1 with "[$HPC $Ha]"); eauto.
          { split; [destruct Hp as [-> | [-> _] ]; auto|].
            destruct Hbae as [Hb He].
            apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto.
          }
          iNext. iIntros (_).
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        }
      + destruct (Hsome r0) as [wdst Hsomedst].
        destruct (reg_eq_dec r0 PC).
        * simplify_eq.
          destruct Hp as [-> | [-> Hg] ].
          ** destruct (isLocal g) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               iApply (wp_store_fail_PC_PC3 with "[$HPC $Ha]"); eauto.
               { destruct Hbae as [Hb He].
                 apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
                   { split; auto. destruct Hbae as [Hb He].
                     apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                   iNext. iIntros "[HPC Ha]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".

                   { iSplitR; [auto|]. iSplitL.

                     {destruct (decide (ρ = Temporary ∧ pwl p' = true)); iAlways; simpl.
                      - iIntros (W0 W1) "% HIW0".
                          by iApply interp_monotone.
                      - iIntros (W0 W1) "% HIW0".
                          by iApply interp_monotone_nl.
                     }
                     iApply execcPC_implies_interp; eauto.
                     { iAlways.
                       rewrite /exec_cond. iIntros (a' r' W' Hin) "#Hfuture".
                       iNext. rewrite /interp_expr /=.
                       iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                       iSplitR; eauto.
                       iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                       iAlways. iExists p'. iSplitR; auto.
                       unfold future_world; destruct g; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                       - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                         iPureIntro; split.
                         + by apply (region_state_nwl_monotone_nl _ _ y H5 Hfuture H4).
                         + eapply related_sts_rel_std; eauto.
                       - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                     }

                   }

                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|].
                   rewrite insert_delete.
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 }
                 { (* failure to increment PC *)
                   destruct g; inversion Hlocal; auto.
                   iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
                   { split;auto. destruct Hbae as [Hb He].
                     apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
               { split; auto. destruct Hbae as [Hb He].
                 apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
               iNext. iIntros "[HPC Ha]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".
               { iSplitR; [auto|]. iSplitL.
                 {destruct (decide (ρ = Temporary ∧ pwl p' = true)); iAlways; simpl.
                  - iIntros (W0 W1) "% HIW0".
                      by iApply interp_monotone.
                  - iIntros (W0 W1) "% HIW0".

                    assert (ρ = Temporary).
                    {
                      simpl in Hpwl. unfold region_state_pwl in Hpwl.
                      rewrite Hstd in Hpwl. inversion Hpwl.
                      apply (f_equal (countable.decode (A:=region_type))) in H4.
                      do 2 rewrite countable.decode_encode in H4. by inversion H4.
                    }

                    assert (pwl p' = true).
                    {
                      unfold PermFlows in Hfp; unfold PermFlowsTo in Hfp.
                      destruct p'; last by eauto.
                      all:congruence.
                    }

                    assert ( ρ = Temporary ∧ pwl p' = true) by (split;auto).
                      by apply n in H5.
                 }
                 iNext. simpl. rewrite (fixpoint_interp1_eq _ (inr _)). simpl. rewrite Hg.
                 iExists p'. do 2 (iSplit; [auto | ]).
                 { iAlways.
                   rewrite /exec_cond. iIntros (a' r' W' Hin) "#Hfuture".
                   iNext. rewrite /interp_expr /=.
                   iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                   iSplitR; eauto.
                   iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                   iAlways. iExists p'. iSplitR; auto.
                   unfold future_world; destruct g; first by congruence. iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                   iIntros "[HA [% %]]". iSplitL "HA"; auto.
                   iPureIntro; split.
                   + apply (region_state_pwl_monotone _ _ y H5 Hfuture H4); eauto.
                   + apply related_sts_pub_priv_world in Hfuture.
                     eapply related_sts_rel_std; eauto.
                 }

               }

               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|].
               rewrite insert_delete.
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
             }
             { (* failure to increment PC *)
               iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
               { split;auto. destruct Hbae as [Hb He].
                 apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             }
        * iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
            as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
          destruct Hp as [-> | [-> Hg] ].
          ** destruct (isLocalWord wdst) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               destruct wdst; first inversion Hlocal. destruct c,p,p,p.
               iApply (wp_store_fail_PC3 with "[$HPC $Ha $Hdst]"); eauto.
               { destruct Hbae as [Hb He].
                 apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
                   iNext. iIntros "[HPC [Ha Hr0 ]]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".

                   {iSplitR; [auto|]. iSplitL.

                    {destruct (decide (ρ = Temporary ∧ pwl p' = true)); iAlways; simpl.
                     - iIntros (W0 W1) "% HIW0".
                         by iApply interp_monotone.
                     - iIntros (W0 W1) "% HIW0".
                         by iApply interp_monotone_nl.
                    }
                    iSpecialize ("Hreg" $! r0 n).
                      by rewrite /RegLocate Hsomedst.
                   }

                   iDestruct ((big_sepM_insert) with "[$Hmap $Hr0]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                   - iPureIntro. intros r1.
                     destruct (decide (r0 = r1)); subst;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                   - iIntros (r1 Hne).
                     destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     iSpecialize ("Hreg" $! r1 n). by rewrite Hsomedst.
                     iSpecialize ("Hreg" $! r1 Hne).
                     destruct (r !! r1); auto.
                 }
                 { (* failure to increment PC *)
                   iApply (wp_store_fail_reg_PC_1 with "[$HPC $Ha $Hdst]"); eauto.
                   { split;auto. destruct Hbae as [Hb He].
                     apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
               iNext. iIntros "[HPC [Ha Hdst]]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".

               {  iSplitR; [auto|]. iSplitL.
                  {destruct (decide (ρ = Temporary ∧ pwl p' = true)); iAlways; simpl.
                   - iIntros (W0 W1) "% HIW0".
                       by iApply interp_monotone.
                   - iIntros (W0 W1) "% HIW0".

                     assert (ρ = Temporary).
                     {
                       simpl in Hpwl. unfold region_state_pwl in Hpwl.
                       rewrite Hstd in Hpwl. inversion Hpwl.
                       apply (f_equal (countable.decode (A:=region_type))) in H4.
                       do 2 rewrite countable.decode_encode in H4. by inversion H4.
                     }

                     assert (pwl p' = true).
                     {
                       unfold PermFlows in Hfp; unfold PermFlowsTo in Hfp.
                       destruct p'; last by eauto.
                       all:congruence.
                     }

                     assert ( ρ = Temporary ∧ pwl p' = true) by (split;auto).
                       by apply n0 in H5.
                  }

                  iSpecialize ("Hreg" $! r0 n).
                    by rewrite /RegLocate Hsomedst.
               }
               iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
               - iPureIntro. intros r1.
                 destruct (decide (r0 = r1)); subst;
                   [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
               - iIntros (r1 Hne).
                 destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                   [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                 iSpecialize ("Hreg" $! r1 n). by rewrite Hsomedst.
                 iSpecialize ("Hreg" $! r1 Hne).
                 destruct (r !! r1); auto.
             }
             { (* failure to increment PC *)
               iApply (wp_store_fail_reg_PC_1 with "[$HPC $Ha $Hdst]"); eauto.
               { split;auto. destruct Hbae as [Hb He].
                 apply andb_true_iff; split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             }
    - destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap")
        as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
      destruct wdst.
      { (* if dst does not contain cap, fail *)
        iApply (wp_store_fail2 with "[HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate. }
      destruct c,p0,p0,p0.
      case_eq (writeAllowed p0
                            && withinBounds (p0,l,a2,a1,a0));
        intros Hconds.
      + apply andb_true_iff in Hconds as [Hwa Hwb].

        (* Before we destruct the source, we derive interp for its value *)


        destruct src.
        * destruct (a + 1)%a eqn:Hnext.
          { (* successful write into a0 *)
            destruct (decide (a = a0));[subst|].
            {
              (* We need to derive that p0 flows into p', so that we know we can write into dst*)
              iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond.
              iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
              iApply (wp_store_success_same with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto. iNext.
              (* close the region *)
              iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".

              { iSplitR; [auto|]. iSplitL.
                {destruct (decide (ρ = Temporary ∧ pwl p'' = true)); iAlways; simpl.
                 - iIntros (W0 W1) "% HIW0".
                     by iApply interp_monotone.
                 - iIntros (W0 W1) "% HIW0".
                     by iApply interp_monotone_nl.
                }
                iNext. simpl. by rewrite (fixpoint_interp1_eq _ (inl _)).
              }

              iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              (* apply IH *)
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
              iFrame "#"; auto.
              - iPureIntro. intros r1.
                destruct (decide (dst = r1)); subst;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              - iIntros (r1 Hne).
                destruct (decide (dst = r1)); subst; rewrite /RegLocate;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                iSpecialize ("Hreg" $! r1 Hne).
                destruct (r !! r1); auto.
            }
            { iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct ("Hreg" $! dst n) as "#Hvdst".
              rewrite /RegLocate Hsomedst.
              iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
              { destruct p0; inversion Hwa; auto. }
              destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
              { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
              iApply (wp_store_success_z with "[$HPC $Hdst $Ha $Ha0]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
              iApply wp_pure_step_later; auto. iNext.

              (* close the region *)
              iDestruct (region_close_next with "[$Hr $Ha0 $Ha2a1 $Hstate']") as "Hr"; eauto.
              { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
              iSplit; auto. iSplit.
              (* To close the region, we need to reestablish interp and monotonicity for the new value *)
              iApply interp_monotone_generalZ; eauto.
              {  iNext. simpl. by rewrite (fixpoint_interp1_eq _ (inl z)) /=. }

              iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct (region_close with "[$Hr $Ha $Hmono $Hstate]") as "Hr"; auto.
              iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              (* apply IH *)
              iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
              - iPureIntro. intros r1.
                destruct (decide (dst = r1)); subst;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
              - iIntros (r1 Hne).
                destruct (decide (dst = r1)); subst; rewrite /RegLocate;
                  [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                iSpecialize ("Hreg" $! r1 Hne).
                destruct (r !! r1); auto.
            }
          }
          { (* failure to increment PC *)
            destruct (decide (a = a0));[subst|].
            - iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond.
              iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst]"); eauto.
              { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
            - iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct ("Hreg" $! dst n) as "#Hvdst".
              rewrite /RegLocate Hsomedst.
              iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
              { destruct p0; inversion Hwa; auto. }
              destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
              { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst Ha0]"); eauto.
              { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|].
                iFrame. auto. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
          }
        * destruct (reg_eq_dec PC r0),(reg_eq_dec dst r0);
            first congruence; subst.
          ** (* If the below condition does not hold: permission problem when writing *)
            case_eq (negb (isLocal g) || match p0 with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'.
            { destruct (a + 1)%a eqn:Hnext.
              { (* successful write from PC into a0 *)
                destruct (decide (a = a0));[subst|].
                { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                  iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                  { apply andb_true_iff in Hwb as [Hle Hge].
                    split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                  { destruct p0; inversion Hwa; auto. }
                  rewrite /read_write_cond.
                  iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                  iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst]"); eauto;
                    (destruct (a0 =? a0)%a eqn:Hcontr;
                     [auto|by apply Z.eqb_neq in Hcontr]).
                  { destruct g; auto. right.
                    rewrite orb_false_l in Hconds'.
                    destruct p0; auto; inversion Hconds'. }
                  iNext. iIntros "(HPC & Ha & Hdst & _)".
                  iApply wp_pure_step_later; auto. iNext.
                  (* close the region *)
                  iDestruct (region_close with "[$Hr $Ha $Hstate]") as "Hr"; auto. iFrame "#".

                  { iSplitR; [auto|]. iSplitL.
                    {destruct (decide (ρ = Temporary ∧ pwl p'' = true)); iAlways; simpl.
                     - iIntros (W0 W1) "% HIW0".
                         by iApply interp_monotone.
                     - iIntros (W0 W1) "% HIW0".
                       destruct g.
                       * by iApply interp_monotone_nl.
                       * rewrite orb_false_l in Hconds'.

                         iAssert (⌜ρ = Temporary⌝)%I as "%".
                         {
                           iDestruct ( writeLocalAllowed_valid_cap_implies with "Hdstv" ) as "%"; eauto.
                           iPureIntro. destruct H3. rewrite Hstd in H4. inversion H4.
                           apply (f_equal (countable.decode (A:=region_type))) in H6.
                           do 2 rewrite countable.decode_encode in H6. by inversion H6.

                         }

                         assert (pwl p'' = true).
                         { destruct p0; try congruence; unfold PermFlows in Hfl'; unfold PermFlowsTo in Hfl'.
                           - destruct p''; try congruence. all:eauto.
                           - destruct p''; last by eauto. all:congruence.
                         }

                         assert ( ρ = Temporary ∧ pwl p'' = true) by (split;auto).
                           by apply n1 in H5.
                    }

                    iClear "Hdstv". iNext. simpl.
                    iApply execcPC_implies_interp; eauto.
                    iAlways;rewrite /exec_cond;iIntros (a' r' W' Hin) "#Hfuture".
                    iNext; rewrite /interp_expr /=.
                    iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                    iSplitR; eauto.
                    iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                    iAlways. iExists p''. iSplitR; auto.
                    unfold future_world; destruct g; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                    (*g is global*)
                    - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                      iPureIntro; split.
                      + destruct (pwl p) eqn:Hppwl.
                        * (do 2 try destruct Hp as [ | Hp]); last by (destruct Hp; exfalso).
                          all: (rewrite H6 in Hppwl; simpl in Hppwl; by exfalso).
                        * by apply (region_state_nwl_monotone_nl _ _ y H5 Hfuture H4).
                      + eapply related_sts_rel_std; eauto.
                    (*g is local*)
                    - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                      iPureIntro; split.
                      +  destruct (pwl p).
                         * apply (region_state_pwl_monotone _ _ y H5 Hfuture H4); auto.
                         * apply (region_state_nwl_monotone _ _ y Local H5 Hfuture H4); auto.
                      + apply related_sts_pub_priv_world in Hfuture.
                        eapply related_sts_rel_std; eauto.
                  }


                  iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                    as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                  rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                    as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                  (* apply IH *)
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                  - iPureIntro. intros r1.
                    destruct (decide (dst = r1)); subst;
                      [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                  - iIntros (r1 Hne).
                    destruct (decide (dst = r1)); subst; rewrite /RegLocate;
                      [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                    iSpecialize ("Hreg" $! r1 Hne).
                    destruct (r !! r1); auto.
                }
                {  iDestruct (region_open_prepare with "Hr") as "Hr".
                   iDestruct ("Hreg" $! dst n) as "#Hvdst".
                   rewrite /RegLocate Hsomedst.
                   iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                   { destruct p0; inversion Hwa; auto. }
                   destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                   iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                   { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                   iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst Ha0]"); eauto;
                     (destruct (a0 =? a)%a eqn:Hcontr;
                      [by apply Z.eqb_eq, z_of_eq in Hcontr|auto]).
                   { destruct g; auto. right. rewrite orb_false_l in Hconds'.
                     destruct p0;auto;inversion Hconds'. }
                   iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                   iApply wp_pure_step_later; auto. iNext.

                   (* close the region *)
                   iDestruct (region_close_next with "[$Hr $Ha0 $Ha2a1 $Hstate']") as "Hr"; eauto.
                   { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                   iSplit; auto. iSplit.
                   (* To close the region, we need to reestablish interp and monotonicity for the new value *)
                   {
                     unfold monotonicity_guarantees_region.
                     destruct ρ'.
                     - destruct (pwl p1) eqn: HpwlP1 ; iAlways; simpl.
                       * iIntros (W0 W1) "% HIW0".
                           by iApply interp_monotone.
                       * iIntros (W0 W1) "% HIW0".
                         destruct g.
                       + by iApply interp_monotone_nl.
                       (*The below case is a contradiction, since if g is local,p0 must be WL and p0 flows into the non-WL p1*)
                       + destruct p0 ; try (simpl in Hconds'; by exfalso).
                         all:destruct p1 eqn:Hp1v ; (by exfalso).
                     - iAlways. simpl. iIntros (W0 W1) "% HIW0".
                       destruct g.
                       + by iApply interp_monotone_nl.
                       + (*Trick here: value relation leads to a contradiction if p0 is WL, since then its region cannot be permanent*)
                         iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as "%"; eauto.
                         destruct H4. rewrite Hstd' in H5. inversion H5.
                         apply (f_equal (countable.decode (A:=region_type))) in H7.
                         do 2 rewrite countable.decode_encode in H7. by inversion H7.
                     - auto.
                   }
                   {
                     iNext. simpl.
                     iApply execcPC_implies_interp; eauto.
                     iAlways;rewrite /exec_cond;iIntros (a' r' W' Hin) "#Hfuture".
                     iNext; rewrite /interp_expr /=.
                     iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
                     iSplitR; eauto.
                     iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
                     iAlways. iExists p'. iSplitR; auto.
                     unfold future_world; destruct g; iDestruct "Hfuture" as %Hfuture; iApply (big_sepL_mono with "Hinv"); intros; simpl.
                     (*g is global*)
                     - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                       iPureIntro; split.
                       + destruct (pwl p) eqn:Hppwl.
                         * (do 2 try destruct Hp as [ | Hp]); last by (destruct Hp; exfalso).
                           all: (rewrite H7 in Hppwl; simpl in Hppwl; by exfalso).
                         * by apply (region_state_nwl_monotone_nl _ _ y H6 Hfuture H5).
                       + eapply related_sts_rel_std; eauto.
                     (*g is local*)
                     - iIntros "[HA [% %]]". iSplitL "HA"; auto.
                       iPureIntro; split.
                       +  destruct (pwl p).
                          * apply (region_state_pwl_monotone _ _ y H6 Hfuture H5); auto.
                          * apply (region_state_nwl_monotone _ _ y Local H6 Hfuture H5); auto.
                       + apply related_sts_pub_priv_world in Hfuture.
                         eapply related_sts_rel_std; eauto.

                   }

                   iDestruct (region_open_prepare with "Hr") as "Hr".
                   iDestruct (region_close with "[$Hr $Ha $Hmono $Hstate]") as "Hr"; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   (* apply IH *)
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                   iFrame "#"; auto.
                   - iPureIntro. intros r1.
                     destruct (decide (dst = r1)); subst;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                   - iIntros (r1 Hne).
                     destruct (decide (dst = r1)); subst; rewrite /RegLocate;
                       [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     iSpecialize ("Hreg" $! r1 Hne).
                     destruct (r !! r1); auto.
                }
              }
              { (* failure to increment PC *)
                destruct (decide (a = a0));[subst|].
                { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                  iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                  { apply andb_true_iff in Hwb as [Hle Hge].
                    split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                  { destruct p0; inversion Hwa; auto. }
                  rewrite /read_write_cond.
                  iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                  iApply (wp_store_fail_reg_PC_2 with "[$HPC $Ha $Hdst]"); eauto.
                  { destruct g; auto. rewrite orb_false_l in Hconds'. right.
                    destruct p0; auto; inversion Hconds'. }
                  { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value. iIntros. discriminate.
                }
                { iDestruct (region_open_prepare with "Hr") as "Hr".
                  iDestruct ("Hreg" $! dst n) as "#Hvdst".
                  rewrite /RegLocate Hsomedst.
                  iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                  { destruct p0; inversion Hwa; auto. }
                  destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                  iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                  { apply andb_true_iff in Hwb as [Hle Hge].
                    split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                  { destruct p0; inversion Hwa; auto. }
                  iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                  { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                  iApply (wp_store_fail_reg_PC_2 with "[$HPC $Ha $Hdst Ha0]"); eauto.
                  { destruct g; auto. rewrite orb_false_l in Hconds'. right.
                    destruct p0; auto; inversion Hconds'. }
                  { destruct (a =? a0)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value. iIntros. discriminate.
                }
              }
            }
            { (* condition failure *)
              revert Hconds'. rewrite orb_false_iff =>Hlocal.
              destruct Hlocal as [Hg Hp0].
              iApply (wp_store_fail3' with "[$HPC $Ha $Hdst]"); eauto;
                [destruct g|destruct p0|destruct p0|];auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
            }
          ** case_eq (negb (isLocal l) || match p0 with
                                          | RWL | RWLX => true
                                          | _ => false end); intros Hconds'.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write from r0 into a0 *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! r0 _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond.
                     iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same' with "[$HPC $Ha $Hdst]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hstate ]") as "Hr"; eauto. iFrame "#".
                     { iSplitR; [auto|].
                       destruct (decide (ρ = Temporary ∧ pwl p'' = true)); iAlways; simpl.
                       - iIntros (W0 W1) "% HIW0".
                           by iApply interp_monotone.
                       - iIntros (W0 W1) "% HIW0".
                         destruct l.
                         * by iApply interp_monotone_nl.
                         * rewrite orb_false_l in Hconds'.
                           iAssert (⌜ρ = Temporary⌝)%I as "%".
                           {
                             iDestruct ( writeLocalAllowed_valid_cap_implies with "Hdstv" ) as "%"; eauto.
                             iPureIntro. destruct H3. rewrite Hstd in H4. inversion H4.
                             apply (f_equal (countable.decode (A:=region_type))) in H6.
                             do 2 rewrite countable.decode_encode in H6. by inversion H6.

                           }

                           assert (pwl p'' = true).
                           { destruct p0; try congruence; unfold PermFlows in Hfl'; unfold PermFlowsTo in Hfl'.
                             - destruct p''; try congruence. all:eauto.
                             - destruct p''; last by eauto. all:congruence.
                           }

                           assert ( ρ = Temporary ∧ pwl p'' = true) by (split;auto).
                             by apply n1 in H5.
                             (*Note that there is no need to reprove Interp here anymore, as we get it for free from Hdstv*)
                     }


                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! r0 n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                     { destruct p0; inversion Hwa; auto. }
                     destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                     { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                     iApply (wp_store_success_reg_same with "[$HPC $Ha $Hdst $Ha0]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.

                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Ha2a1 $Hstate' $Hvdst]") as "Hr"; eauto.
                     { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                     iSplit; auto.
                     (* To close the region, we need to reestablish monotonicity for the new value (interp was automatic from Hvdst above) *)
                     iApply interp_monotone_generalW; eauto.

                     iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Hstate]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                     iFrame "#"; auto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                 }
                 { (* failure to increment *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! r0 _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond.
                     iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                     iApply (wp_store_fail_same_None with "[$HPC $Ha $Hdst]"); eauto.
                     { destruct l; auto. rewrite orb_false_l in Hconds'. right.
                       destruct p0; auto; inversion Hconds'. }
                     { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   }
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! r0 n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                     { destruct p0; inversion Hwa; auto. }
                     destruct H3 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                     { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                     iApply (wp_store_fail_same_None with "[$HPC $Ha $Hdst Ha0]"); eauto.
                     { destruct l; auto. rewrite orb_false_l in Hconds'. right.
                       destruct p0; auto; inversion Hconds'. }
                     { destruct (a =? a0)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   }
                 }
             *** (* locality failure *)
               revert Hconds'. rewrite orb_false_iff =>Hlocal.
               destruct Hlocal as [Hg Hp0].
               iApply (wp_store_fail3_same with "[$HPC $Ha $Hdst]"); eauto;
                 [destruct l|destruct p0|destruct p0|];auto.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value. iIntros. discriminate.
          ** destruct (Hsome r0) as [wsrc Hsomesrc].
             assert (delete PC r !! r0 = Some wsrc).
             { rewrite lookup_delete_ne; auto. }
             iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
               as "[Hsrc Hmap]"; [rewrite lookup_delete_ne; eauto|].
             destruct wsrc.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write from r0 into a0 *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond.
                     iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hstate]") as "Hr"; eauto. iFrame "#".
                     { iSplitR; [auto|]. iSplitL.

                       {destruct (decide (ρ = Temporary ∧ pwl p'' = true)); iAlways; simpl.
                        - iIntros (W0 W1) "% HIW0".
                            by iApply interp_monotone.
                        - iIntros (W0 W1) "% HIW0".
                            by iApply interp_monotone_nl.
                       }
                       iNext. simpl. by rewrite (fixpoint_interp1_eq _ (inl _)).
                     }

                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst.
                       + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                       + destruct (decide (dst = r1)); subst.
                         * rewrite lookup_insert. eauto.
                         * do 2 (rewrite lookup_insert_ne;auto).
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                          rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|rewrite lookup_insert;auto|
                          do 2 (rewrite lookup_insert_ne;auto)].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! dst n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                     { destruct p0; inversion Hwa; auto. }
                     destruct H4 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                     { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                     iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Ha2a1 $Hstate']") as "Hr"; eauto.
                     { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                     iSplit; auto. iSplit.
                     (* To close the region, we need to reestablish interp and monotonicity for the new value *)
                     iApply interp_monotone_generalZ; eauto.
                     {  iNext. simpl. by rewrite (fixpoint_interp1_eq _ (inl z)) /=. }


                     iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Hstate]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                     - iPureIntro. intros r1.
                       destruct (decide (r0 = r1)); subst.
                       + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                       + destruct (decide (dst = r1)); subst.
                         * rewrite lookup_insert. eauto.
                         * do 2 (rewrite lookup_insert_ne;auto).
                     - iIntros (r1 Hne).
                       destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                         [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                          rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                          rewrite (fixpoint_interp1_eq _ (inl _));eauto|rewrite lookup_insert;auto|
                          do 2 (rewrite lookup_insert_ne;auto)].
                       iSpecialize ("Hreg" $! r1 Hne).
                       destruct (r !! r1); auto.
                   }
                 }
                 { (* failed to increment PC *)
                   destruct (decide (a = a0));[subst|].
                   { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond.
                     iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                     iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc]"); eauto.
                     { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   }
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! dst n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                     { destruct p0; inversion Hwa; auto. }
                     destruct H4 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                     { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                     iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc Ha0]"); eauto.
                     { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   }
                 }
             *** case_eq (negb (isLocalWord (inr c)) || match p0 with
                                                        | RWL | RWLX => true
                                                        | _ => false end); intros Hconds'.
                 **** destruct (a + 1)%a eqn:Hnext.
                      { (* successful write from r0 into a0 *)
                        destruct (decide (a = a0));[subst|].
                        { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                          iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond.
                          iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                          iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                          { destruct c,p1,p1,p1,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc.
                          iDestruct (region_close with "[$Hr $Ha $Hstate]") as "Hr"; auto. iFrame "#".
                          {
                            destruct c,p1,p1,p1.
                            iSplitR; [auto|]. iSplitL.
                            {destruct (decide (ρ = Temporary ∧ pwl p'' = true)); iAlways; simpl.
                             - iIntros (W0 W1) "% HIW0".
                                 by iApply interp_monotone.
                             - iIntros (W0 W1) "% HIW0".
                               destruct l0.
                               * by iApply interp_monotone_nl.
                               * rewrite orb_false_l in Hconds'.

                                 iAssert (⌜ρ = Temporary⌝)%I as "%".
                                 {
                                   iDestruct ( writeLocalAllowed_valid_cap_implies with "Hdstv" ) as "%"; eauto.
                                   iPureIntro. destruct H4. rewrite Hstd in H5. inversion H5.
                                   apply (f_equal (countable.decode (A:=region_type))) in H7.
                                   do 2 rewrite countable.decode_encode in H7. by inversion H7.

                                 }

                                 assert (pwl p'' = true).
                                 { destruct p0; try congruence; unfold PermFlows in Hfl'; unfold PermFlowsTo in Hfl'.
                                   - destruct p''; try congruence. all:eauto.
                                   - destruct p''; last by eauto. all:congruence.
                                 }

                                 assert ( ρ = Temporary ∧ pwl p'' = true) by (split;auto).
                                   by apply n2 in H6.
                            }
                            (*Note that there is no need to reprove Interp here anymore, as we get it for free from Hc*)
                            iNext. by simpl.
                          }

                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                          - iPureIntro. intros r1.
                            destruct (decide (r0 = r1)); subst.
                            + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                            + destruct (decide (dst = r1)); subst.
                              * rewrite lookup_insert. eauto.
                              * do 2 (rewrite lookup_insert_ne;auto).
                          - iIntros (r1 Hne).
                            destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                              [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                               rewrite (fixpoint_interp1_eq _ (inl _));eauto|
                               rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                               rewrite (fixpoint_interp1_eq _ (inr _));eauto|rewrite lookup_insert;auto|
                               do 2 (rewrite lookup_insert_ne;auto)].
                            iSpecialize ("Hreg" $! r1 Hne).
                            destruct (r !! r1); auto.
                        }
                        { iDestruct (region_open_prepare with "Hr") as "Hr".
                          iDestruct ("Hreg" $! dst n) as "#Hvdst".
                          rewrite /RegLocate Hsomedst.
                          iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                          { destruct p0; inversion Hwa; auto. }
                          destruct H4 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                          iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                          iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                          { destruct c,p2,p2,p2,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc.
                          iDestruct (region_close_next with "[$Hr $Ha0 $Ha2a1 $Hstate' $Hc]") as "Hr"; eauto.
                          { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                          iSplit; auto.
                          (* To close the region, we need to reestablish monotonicity for the new value (interp was automatic from Hvdst above) *)
                          destruct c,p2,p2,p2; iApply interp_monotone_generalW; eauto.
                          iDestruct (region_open_prepare with "Hr") as "Hr".
                          iDestruct (region_close with "[$Hr $Ha $Hmono $Hstate]") as "Hr"; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                          - iPureIntro. intros r1.
                            destruct (decide (r0 = r1)); subst.
                            + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                            + destruct (decide (dst = r1)); subst.
                              * rewrite lookup_insert. eauto.
                              * do 2 (rewrite lookup_insert_ne;auto).
                          - iIntros (r1 Hne).
                            destruct (decide (r0 = r1)),(decide (dst = r1)); subst; rewrite /RegLocate;
                              [rewrite lookup_insert_ne;auto;rewrite lookup_insert;eauto;
                               rewrite (fixpoint_interp1_eq _ (inr c));eauto|
                               rewrite lookup_insert_ne;auto;rewrite lookup_insert;
                               rewrite (fixpoint_interp1_eq _ (inr c));eauto|rewrite lookup_insert;auto|
                               do 2 (rewrite lookup_insert_ne;auto)].
                            iSpecialize ("Hreg" $! r1 Hne).
                            destruct (r !! r1); auto.
                        }
                      }
                      { (* failed to increment PC *)
                        destruct (decide (a = a0));[subst|].
                        { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                          iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond.
                          iDestruct (rel_agree a0 p' p'' with "[$Hinva $Harel']") as "[-> _]".
                          iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc]"); eauto.
                          { destruct c,p1,p1,p1,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value. iIntros. discriminate.
                        }
                        { iDestruct (region_open_prepare with "Hr") as "Hr".
                          iDestruct ("Hreg" $! dst n) as "#Hvdst".
                          rewrite /RegLocate Hsomedst.
                          iDestruct (readAllowed_valid_cap_implies with "Hvdst") as "%"; eauto.
                          { destruct p0; inversion Hwa; auto. }
                          destruct H4 as [Hregion' [ρ' [Hstd' Hnotrevoked'] ] ].
                          iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; [apply Zle_is_le_bool | apply Zlt_is_lt_bool]; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          iDestruct (region_open_next _ _ _ a0 p1 ρ' with "[$Ha2a1 $Hr $Hsts]") as (wa0) "(Hsts & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)"; eauto.
                          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
                          iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc Ha0]"); eauto.
                          { destruct c,p2,p2,p2,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|auto]. }
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value. iIntros. discriminate.
                        }
                      }
                 **** (* locality failure *)
                   apply orb_false_iff in Hconds'.
                   destruct c,p1,p1,p1.
                   destruct Hconds' as [Hl0 Hp0].
                   iApply (wp_store_fail3 with "[$HPC $Hdst $Hsrc $Ha]"); eauto.
                   { by apply negb_false_iff. }
                   { destruct p0; auto; inversion Hp0. }
                   { destruct p0; auto; inversion Hp0. }
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value. iIntros. discriminate.
      + (* write failure, either wrong permission or not within range *)
        iApply (wp_store_fail1 with "[$HPC $Ha $Hdst]"); eauto.
        { by apply andb_false_iff in Hconds. }
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate.
        Unshelve. all:auto.
  Qed.

End fundamental.
