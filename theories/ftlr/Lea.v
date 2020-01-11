From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base.

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

  Lemma interp_cap_preserved W p l a2 a1 a0 a3 (Hne: p <> cap_lang.E):
    (fixpoint interp1) W (inr (p, l, a2, a1, a0)) -∗
    (fixpoint interp1) W (inr (p, l, a2, a1, a3)).
  Proof.
    repeat rewrite fixpoint_interp1_eq. simpl. iIntros "HA".
    destruct p; auto; congruence.
  Qed.

  Lemma lea_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName):
    ftlr_instr W r p p' g b e a w (cap_lang.Lea dst r0) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (a + z)%a; intros.
        * case_eq (a0 + 1)%a; intros.
          { iApply (wp_lea_success_z_PC with "[HPC Ha]"); eauto;
              [destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto|..]. 
            iFrame.
            iNext. iIntros "(HPC & Ha)".
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_pure_step_later; auto.
            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            iApply ("IH" with "[%] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. }
          { iApply (wp_lea_failPC1' with "[HPC Ha]"); eauto;
              [destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto|..]. 
            iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
        * iApply (wp_lea_failPC1 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (Hsome r0) as [wr0 Hsomer0].
        destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          repeat rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + case_eq (a + z)%a; intros.
            * case_eq (a0 + 1)%a; intros.
              { iApply (wp_lea_success_reg_PC with "[HPC Ha Hr0]"); eauto;
                  [destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto|..]. iFrame.
                 iNext. iIntros "(HPC & Ha & Hr0)".
                 iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iApply wp_pure_step_later; auto.
                 iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                 iApply ("IH" with "[%] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 { intros x. simpl.
                   destruct (decide (x = r0));
                     [subst;rewrite lookup_insert;eauto|
                     rewrite lookup_insert_ne;auto]. }
                 { iIntros (r1 Hr1).
                   destruct (decide (r1 = r0)); rewrite /RegLocate; 
                     [subst;rewrite lookup_insert;eauto|
                      rewrite lookup_insert_ne;auto].
                   - do 2 rewrite fixpoint_interp1_eq. eauto.
                   - iApply "Hreg"; auto. 
                 }
              }
              { iApply (wp_lea_failPCreg1' with "[HPC Ha Hr0]"); eauto;
                  [destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto|..]. iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate. }
     * destruct (Hsome dst) as [wdst Hsomedst].
       iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
       rewrite lookup_delete_ne; eauto.
       destruct wdst.
       { iApply (wp_lea_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
         iNext. iIntros. iApply wp_pure_step_later; auto.
         iNext. iApply wp_value; auto. iIntros; discriminate. }
       { destruct c, p0, p0, p0.
         destruct (perm_eq_dec p0 cap_lang.E).
         - subst p0. destruct r0.
           + iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_fail3 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
         - destruct r0.
           + case_eq (a0 + z)%a; intros.
             * case_eq (a + 1)%a; intros.
               { iApply (wp_lea_success_z with "[HPC Ha Hdst]"); eauto; [iFrame|].
                 iNext. iIntros "(HPC & Ha & Hdst)".
                 iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 repeat rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iApply wp_pure_step_later; auto.
                 iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                 iAssert ((interp_registers _ (<[dst:=inr (p0, l, a2, a1, a3)]> r)))%I
                   as "#[Hfull' Hreg']".
                 { iSplitL.
                   - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                   - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                     + subst r2. rewrite /RegLocate lookup_insert.
                       iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                       simpl. iApply (interp_cap_preserved with "HA"); auto.
                     + rewrite /RegLocate lookup_insert_ne; auto.
                       iApply "Hreg"; auto. }
                 iApply ("IH" with "[$Hfull'] [$Hreg'] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. }
               { iApply (wp_lea_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + destruct (Hsome r0) as [wr0 Hsomer0].
             destruct (reg_eq_dec PC r0).
             * subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
             * destruct (reg_eq_dec dst r0).
               { subst r0. iApply (wp_lea_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
               { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                 repeat rewrite lookup_delete_ne; eauto.
                 destruct wr0.
                 - case_eq (a0 + z)%a; intros.
                   * case_eq (a + 1)%a; intros.
                     { revert H4; intro H4.
                       iApply (wp_lea_success_reg with "[$HPC $Ha $Hdst $Hr0]"); eauto.
                       iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                       iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                       iApply wp_pure_step_later; auto.
                       iAssert ((interp_registers _ (<[dst:=inr (p0, l, a2, a1, a3)]> (<[r0:=inl z]> r))))%I
                         as "#[Hfull' Hreg']".
                       { iSplitL.
                         - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                           destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                         - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                           + subst r2. rewrite /RegLocate lookup_insert.
                             iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                             simpl. iApply (interp_cap_preserved with "HA"); auto.
                           + rewrite /RegLocate lookup_insert_ne; auto.
                             destruct (reg_eq_dec r0 r2).
                             * subst r2; rewrite lookup_insert. simpl.
                               repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                             * rewrite lookup_insert_ne; auto.
                               iApply "Hreg"; auto. }
                       iApply ("IH" with "[$Hfull'] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto. }
                     { iApply (wp_lea_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                       iNext. iIntros. iApply wp_pure_step_later; auto.
                       iNext. iApply wp_value; auto. iIntros; discriminate. }
                   * iApply (wp_lea_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value; auto. iIntros; discriminate.
                 - iApply (wp_lea_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value; auto. iIntros; discriminate. } }
  Qed.
       
End fundamental.