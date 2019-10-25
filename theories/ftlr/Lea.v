From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

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

  
  Lemma interp_cap_preserved W p l a2 a1 a0 a3 (Hne: p <> cap_lang.E):
    (fixpoint interp1) W (inr (p, l, a2, a1, a0)) -∗
    (fixpoint interp1) W (inr (p, l, a2, a1, a3)).
  Proof.
    repeat rewrite fixpoint_interp1_eq. simpl. iIntros "HA".
    destruct p; auto; congruence.
  Qed.

  Lemma lea_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (r0 : Z + RegName) :
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = cap_lang.Lea dst r0
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
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r0.
      { case_eq (a + z)%a; intros.
        * case_eq (a0 + 1)%a; intros.
          { iApply (wp_lea_success_z_PC with "[HPC Ha]"); eauto;
              [destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; auto|..]. 
            iFrame.
            iNext. iIntros "(HPC & Ha)".
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); eauto. }
          { iApply (wp_lea_failPC1' with "[HPC Ha]"); eauto;
              [destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; auto|..]. 
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
                  [destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; auto|..]. iFrame.
                 iNext. iIntros "(HPC & Ha & Hr0)".
                 iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
                 iApply wp_pure_step_later; auto.
                 iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                   iFrame "#"; eauto.
                 { iPureIntro. intros x. simpl.
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
                  [destruct Hp as [Hp | [Hp | Hp] ]; rewrite Hp; auto|..]. iFrame.
                iNext. iIntros.  iApply wp_pure_step_later; auto.
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
                 iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
                 iApply wp_pure_step_later; auto.
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
                 iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                   iFrame "#"; eauto.
               }
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
                       iDestruct (region_close with "[$Hr $Ha]") as "Hr";[iFrame "#"; auto|].
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
                       iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]");
                         iFrame "#"; eauto. }
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