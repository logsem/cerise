From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.

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

         
  Lemma store_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
        (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (src : Z + RegName) :
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = Store dst src
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (fs, fr)) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ ▷ future_mono (λ Wv : prodO WORLD (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2)
    -∗ ▷ ((fixpoint interp1) (fs, fr)) w
    -∗ sts_full fs fr
    -∗ na_own logrel_nais ⊤
    -∗ open_region a (fs, fr)
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (fs' : STS_states) (fr' : STS_rels),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full fs' fr' ∗ region (fs', fr') }} }}.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    (* for the successful writes from PC, we want to show that 
         the region can be closed again *)
    iAssert (((fixpoint interp1) (fs, fr)) (inr ((p,g),b,e,a)))%I
        as "#HPCw".
    { rewrite (fixpoint_interp1_eq _ (inr _)) /=.
      destruct Hp as [-> | [-> | ->] ];
      (iExists _,_,_,_; iSplitR;[eauto|];
       iExists p';do 2 (iSplit; auto);
       iAlways;iIntros (a' r' W' Hin) "Hfuture";
       iNext; destruct W' as [fs' fr'];
       iExists _,_; do 2 (iSplitR; [auto|]);
       iIntros "(#[Hfull Hreg'] & Hmap & Hr & Hsts & Hna) /=";
       iExists _,_,_,_,_; iSplit;[eauto|];
       iApply ("IH" with "Hfull Hreg' Hmap Hr Hsts Hna"); auto).
    }
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
            [by destruct Hp as [-> | ->]|].
          iNext. iIntros "[HPC Ha]".
          iApply wp_pure_step_later; auto; iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
          { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inl _)) /=. eauto. }
          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
            as "Hmap"; [by rewrite lookup_delete|].
          rewrite insert_delete. 
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; auto. 
        }
        { (* failure to increment PC *)
          iApply (wp_store_fail_z_PC_1 with "[$HPC $Ha]"); eauto.
          { split; [destruct Hp as [-> | ->]; auto|].
            destruct Hbae as [Hb He]. 
            apply andb_true_iff; split; apply Zle_is_le_bool; auto. 
          }
          iNext. iIntros (_).
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        }
      + destruct (Hsome r0) as [wdst Hsomedst].
        destruct (reg_eq_dec r0 PC).
        * simplify_eq.
          destruct Hp as [-> | ->].
          ** destruct (isLocal g) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               iApply (wp_store_fail_PC_PC3 with "[$HPC $Ha]"); eauto.
               { destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
                   { split; auto. destruct Hbae as [Hb He]. 
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros "[HPC Ha]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
                   { iSplitR;[auto|simpl].
                     rewrite (fixpoint_interp1_eq _ (inr _)) /=. eauto. }
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|].
                   rewrite insert_delete. 
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                     iFrame "#"; auto. 
                 }
                 { (* failure to increment PC *)
                   destruct g; inversion Hlocal; auto.
                   iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
                   { split;auto. destruct Hbae as [Hb He]. 
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC_same with "[$HPC $Ha]"); eauto.
               { split; auto. destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros "[HPC Ha]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
               { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inr _)) /=. eauto. }
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|].
               rewrite insert_delete. 
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                 iFrame "#"; auto. 
             }
             { (* failure to increment PC *)
               iApply (wp_store_fail_PC_PC_1 with "[$HPC $Ha]"); eauto.
               { split;auto. destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.                   
             }
        * iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
            as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
          destruct Hp as [-> | ->]. 
          ** destruct (isLocalWord wdst) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               destruct wdst; first inversion Hlocal. destruct c,p,p,p.
               iApply (wp_store_fail_PC3 with "[$HPC $Ha $Hdst]"); eauto.
               { destruct Hbae as [Hb He]. 
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
               iNext. iIntros (_).
               iApply wp_pure_step_later; auto. iNext.
               iApply wp_value. iIntros. discriminate.
             *** destruct (a + 1)%a eqn:Hnext.
                 { (* successful write into a: word is not local *)
                   iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
                   iNext. iIntros "[HPC [Ha Hr0 ]]".
                   iApply wp_pure_step_later; auto; iNext.
                   iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
                   { iSplitR;[auto|simpl]. iSpecialize ("Hreg" $! r0 n). 
                     by rewrite /RegLocate Hsomedst. }
                   iDestruct ((big_sepM_insert) with "[$Hmap $Hr0]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                     iFrame "#"; auto.
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
                     apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
                   iNext. iIntros (_).
                   iApply wp_pure_step_later; auto. iNext.
                   iApply wp_value. iIntros. discriminate.       
                 }
          ** destruct (a + 1)%a eqn:Hnext.
             { (* successful write into a: perm is local allowed *)
               iApply (wp_store_success_reg_PC with "[$HPC $Ha $Hdst]"); eauto.
               iNext. iIntros "[HPC [Ha Hdst]]".
               iApply wp_pure_step_later; auto; iNext.
               iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
               { iSplitR;[auto|simpl]. iSpecialize ("Hreg" $! r0 n). 
                   by rewrite /RegLocate Hsomedst. }
               iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                 iFrame "#"; auto.
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
                 apply andb_true_iff; split; apply Zle_is_le_bool; auto. }
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
        destruct src.
        * destruct (a + 1)%a eqn:Hnext.
          { (* successful write into a0 *)
            destruct (decide (a = a0));[subst|].
            { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond. 
              iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]". 
              iApply (wp_store_success_same with "[$HPC $Ha $Hdst]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto. iNext.
              (* close the region *)
              iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr".
              { iSplitR;[auto|simpl]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
              iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              (* apply IH *)
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                as (wa0) "(Hr & Ha0 & % & _)";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
              iApply (wp_store_success_z with "[$HPC $Hdst $Ha $Ha0]"); eauto.
              iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
              iApply wp_pure_step_later; auto. iNext.
              (* close the region *)
              iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..].
              { iSplitR;[auto|simpl]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
              iDestruct (region_open_prepare with "Hr") as "Hr". 
              iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
              iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
               rewrite -delete_insert_ne; auto.
               iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                 as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
              (* apply IH *)
               iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
            - iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              rewrite /read_write_cond. 
              iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]". 
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst]"); eauto.
              { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
            - iDestruct (region_open_prepare with "Hr") as "Hr".
              iDestruct ("Hreg" $! dst n) as "#Hvdst".
              rewrite /RegLocate Hsomedst.
              iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
              { apply andb_true_iff in Hwb as [Hle Hge].
                split; apply Zle_is_le_bool; auto. }
              { destruct p0; inversion Hwa; auto. }
              iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                as (wa0) "(Hr & Ha0 & % & _)";
                [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
              iApply (wp_store_fail_z2 with "[$Ha $HPC $Hdst Ha0]"); eauto.
              { destruct (a0 =? a)%a eqn:Hcontr;[by apply Z.eqb_eq,z_of_eq in Hcontr|].
                iFrame. auto. }
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros. discriminate.
          } 
        * destruct (reg_eq_dec PC r0),(reg_eq_dec dst r0);
            first congruence; subst. 
          ** case_eq (negb (isLocal g) || match p0 with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'.
             { destruct (a + 1)%a eqn:Hnext.
               { (* successful write from PC into a0 *)               
                 destruct (decide (a = a0));[subst|].
                 { iDestruct ("Hreg" $! dst _) as "Hdstv". rewrite /RegLocate Hsomedst.
                   iDestruct (read_allowed_inv _ a0 with "Hdstv") as (p'' Hfl') "#Harel'".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   rewrite /read_write_cond. 
                   iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                   iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst]"); eauto;
                     (destruct (a0 =? a0)%a eqn:Hcontr;
                       [auto|by apply Z.eqb_neq in Hcontr]).
                   { destruct g; auto. right.
                     rewrite orb_false_l in Hconds'.
                     destruct p0; auto; inversion Hconds'. }
                   iNext. iIntros "(HPC & Ha & Hdst & _)".
                   iApply wp_pure_step_later; auto. iNext.
                   (* close the region *)
                   iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   (* apply IH *)
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
                   iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                     as (wa0) "(Hr & Ha0 & % & _)";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                   iApply (wp_store_success_reg' with "[$HPC $Ha $Hdst Ha0]"); eauto;
                     (destruct (a0 =? a)%a eqn:Hcontr;
                      [by apply Z.eqb_eq, z_of_eq in Hcontr|auto]).
                   { destruct g; auto. right. rewrite orb_false_l in Hconds'.
                     destruct p0;auto;inversion Hconds'. }
                   iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                   iApply wp_pure_step_later; auto. iNext.
                   (* close the region *)
                   iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..];auto.
                   iDestruct (region_open_prepare with "Hr") as "Hr". 
                   iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   rewrite -delete_insert_ne; auto.
                   iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                     as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                   (* apply IH *)
                   iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   rewrite /read_write_cond. 
                   iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
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
                   iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                     as (wa0) "(Hr & Ha0 & % & _)";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
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
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same' with "[$HPC $Ha $Hdst]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Hdstv]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! r0 n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                       as (wa0) "(Hr & Ha0 & % & _)";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                     iApply (wp_store_success_reg_same with "[$HPC $Ha $Hdst $Ha0]"); eauto.
                     { destruct l; auto. revert Hconds'. rewrite orb_false_l =>Hp0.
                       right. destruct p0; inversion Hp0; auto. }
                     iNext. iIntros "(HPC & Ha & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
                     iDestruct (region_open_prepare with "Hr") as "Hr". 
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
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
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
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
                   iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                   { apply andb_true_iff in Hwb as [Hle Hge].
                     split; apply Zle_is_le_bool; auto. }
                   { destruct p0; inversion Hwa; auto. }
                   iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                     as (wa0) "(Hr & Ha0 & % & _)";
                     [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
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
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Harel']") as "Hr".
                     { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                       iFrame "#"; auto.
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
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                       as (wa0) "(Hr & Ha0 & % & _)";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                     iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                     iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                     iApply wp_pure_step_later; auto. iNext.
                     (* close the region *)
                     iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
                     { rewrite (fixpoint_interp1_eq _ (inl _)). eauto. }
                     iDestruct (region_open_prepare with "Hr") as "Hr". 
                     iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     rewrite -delete_insert_ne; auto.
                     iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     do 2 (rewrite -delete_insert_ne; auto).
                     iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                       as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                     (* apply IH *)
                     iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                       iFrame "#"; auto.
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
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     rewrite /read_write_cond. 
                     iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                     iApply (wp_store_fail_None with "[$HPC $Ha $Hdst $Hsrc]"); eauto.
                     { destruct (a0 =? a0)%a eqn:Hcontr;[auto|by apply Z.eqb_neq in Hcontr]. }
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value. iIntros. discriminate.
                   } 
                   { iDestruct (region_open_prepare with "Hr") as "Hr".
                     iDestruct ("Hreg" $! dst n) as "#Hvdst".
                     rewrite /RegLocate Hsomedst.
                     iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                     { apply andb_true_iff in Hwb as [Hle Hge].
                       split; apply Zle_is_le_bool; auto. }
                     { destruct p0; inversion Hwa; auto. }
                     iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                       as (wa0) "(Hr & Ha0 & % & _)";
                       [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
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
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond. 
                          iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
                          iApply (wp_store_success_reg_same_a with "[$HPC $Ha $Hsrc $Hdst]"); eauto.
                          { destruct c,p1,p1,p1,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc. 
                          iDestruct (region_close with "[$Hr $Ha $Hmono $Harel']") as "Hr"; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                            iFrame "#"; auto.
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
                          iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                            as (wa0) "(Hr & Ha0 & % & _)";
                            [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
                          iApply (wp_store_success_reg with "[$HPC $Ha $Ha0 $Hsrc $Hdst]"); eauto.
                          { destruct c,p2,p2,p2,l0; auto. rewrite orb_false_l in Hconds'. right.
                            destruct p0; auto; inversion Hconds'. }
                          iNext. iIntros "(HPC & Ha & Hsrc & Hdst & Ha0)".
                          iApply wp_pure_step_later; auto. iNext.
                          (* close the region *)
                          iDestruct (region_close_next with "[$Hr $Ha0 $Hmono $Ha2a1]") as "Hr";
                            [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|..]; auto.
                          { iSplitR; eauto. iSpecialize ("Hreg" $! r0 _). rewrite Hsomesrc. auto. }
                          iDestruct (region_open_prepare with "Hr") as "Hr". 
                          iDestruct (region_close with "[$Hr $Ha $Hmono $Harel]") as "Hr"; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hsrc]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_insert) with "[$Hmap $Hdst]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          do 2 (rewrite -delete_insert_ne; auto).
                          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
                            as "Hmap"; [by rewrite lookup_delete|rewrite insert_delete].
                          (* apply IH *)
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                            iFrame "#"; auto.
                          - iPureIntro. intros r1.
                            destruct (decide (r0 = r1)); subst.
                            + rewrite lookup_insert_ne; auto. rewrite lookup_insert; eauto.
                            + destruct (decide (dst = r1)); subst.
                              * rewrite lookup_insert. eauto.
                              * do 2 (rewrite lookup_insert_ne;auto).
                          - iIntros (r1 Hne).
                            iDestruct ("Hreg" $! r0 _) as "Hc". rewrite Hsomesrc. 
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
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          rewrite /read_write_cond. 
                          iDestruct (rel_agree a0 p' p'' with "[$Harel $Harel']") as "[-> _]".
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
                          iDestruct (read_allowed_inv _ a0 with "Hvdst") as (p1 Hfl') "#Ha2a1".
                          { apply andb_true_iff in Hwb as [Hle Hge].
                            split; apply Zle_is_le_bool; auto. }
                          { destruct p0; inversion Hwa; auto. }
                          iDestruct (region_open_next _ _ _ a0 with "[$Hr $Ha2a1]")
                            as (wa0) "(Hr & Ha0 & % & _)";
                            [apply not_elem_of_cons;split;auto;apply not_elem_of_nil|].
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
        Unshelve. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
        auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
        auto. auto. auto. 
  Qed. 
   
End fundamental.