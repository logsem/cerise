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

  (*
  Lemma leb_addr_spec:
    forall a1 a2,
      reflect (le_addr a1 a2) (leb_addr a1 a2).
  Proof.
    intros. rewrite /leb_addr /le_addr.
    apply Z.leb_spec0.
  Qed.    

  Lemma isWithin_implies a0 a1 b e:
    isWithin a0 a1 b e = true ->
    (b <= a0 /\ a1 <= e)%a.
  Proof.
    rewrite /isWithin.
    intros. repeat (apply andb_true_iff in H3; destruct H3).
    generalize (proj2 (reflect_iff _ _ (leb_addr_spec _ _)) H6).
    generalize (proj2 (reflect_iff _ _ (leb_addr_spec _ _)) H4).
    auto.
  Qed.

  Lemma le_addr_implies a1 a2:
    (a1 <= a2)%a ->
    exists n, (a1 + n)%a = Some a2.
  Proof.
    intros. exists (a2 - a1)%Z.
    apply addr_conv.
  Qed.

  (* This should be moved to region.v *)
  Lemma region_addrs_first a0 e:
    (a0 <= e)%a ->
    a0 :: match (a0 + 1)%a with
        | Some y => region_addrs y e
        | None => []
          end = region_addrs a0 e.
  Proof.
    intros. unfold region_addrs.
    destruct (Z_le_dec a0 e).
    - case_eq (a0 + 1)%a; intros.
      + destruct (Z_le_dec a e).
        * simpl. rewrite H4 /=.
          replace (Z.abs_nat (e - a0)) with (S (Z.abs_nat (e - a))); simpl; auto.
          unfold incr_addr in H4; destruct a0.
          simpl in H4. destruct (Z_le_dec (z + 1)%Z MemNum); try congruence.
          inv H4. simpl. simpl in l0.
          lia.
        * assert (a0 = e).
          { unfold incr_addr in H4. destruct (Z_le_dec (a0 + 1)%Z MemNum); try congruence.
            inv H4. simpl in n.
            apply z_of_eq. lia. }
          { subst a0.
            unfold region_size. rewrite Z.sub_diag. simpl.
            reflexivity. }
      + generalize (incr_addr_one_none a0 H4). intros; subst a0.
        generalize (top_le_eq _ l). intros; subst e.
        simpl. auto.
    - elim n. unfold le_addr in *.
      eapply Z.le_trans; eauto. lia.
  Qed.

  (* This should be move to region.v *)
  Lemma isWithin_region_addrs_decomposition a0 a1 b e:
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%a ->
    region_addrs b e = region_addrs b (get_addr_from_option_addr (a0 + -1)%a) ++
                       region_addrs a0 a1 ++
                       match (a1 + 1)%a with
                       | Some y => region_addrs y e
                       | None => []
                       end.
  Proof.
    intros (Hba0 & Ha1e & Ha0a1).
    erewrite (region_addrs_decomposition b a0 e).
    f_equal.
    - rewrite region_addrs_first; [|unfold le_addr in *; eapply Z.le_trans; eauto].
      case_eq (a1 + 1)%a; intros.
      + destruct (Z_le_dec a e).
        * erewrite (region_addrs_decomposition a0 a e).
          { f_equal.
            - unfold incr_addr in H3. destruct (Z_le_dec (a1 + 1)%Z MemNum); try congruence.
              inv H3. unfold incr_addr. simpl.
              destruct (Z_le_dec (a1 + 1 + -1)%Z MemNum); simpl.
              + f_equal. apply z_of_eq; simpl. lia.
              + lia.
            - apply region_addrs_first. unfold le_addr; auto. }
          unfold le_addr; split; auto.
          eapply Z.le_trans; eauto.
          unfold incr_addr in H3. destruct (Z_le_dec (a1 + 1)%Z MemNum); try congruence.
          inv H3. simpl. lia.
        * assert (a1 = e).
          { apply z_of_eq. unfold le_addr in *.
            unfold incr_addr in H3. destruct (Z_le_dec (a1 + 1)%Z MemNum); try congruence.
            inv H3; simpl in n. omega. }
          subst a1.
          replace (region_addrs a e) with ([]: list Addr).
          { rewrite app_nil_r; auto. }
          rewrite /region_addrs. destruct (Z_le_dec a e); auto.
          elim n; auto.
      + generalize (incr_addr_one_none _ H3). intro; subst a1.
        rewrite app_nil_r.
        generalize (top_le_eq _ Ha1e). intro; subst e.
        auto.
    - split; auto. unfold le_addr in *.
      eapply Z.le_trans; eauto.
  Qed.

  Lemma within_in_range:
    forall a b b' e e',
      (b <= b')%a ->
      (e' <= e)%a ->
      in_range a b' e' ->
      in_range a b e.
  Proof.
    intros. destruct H5. unfold in_range.
    unfold le_addr in *. unfold lt_addr in *.
    lia.
  Qed.

  Lemma subseg_interp_preserved:
    forall p l b b' e e' a
      (* RWX case *)
      (fundamental_RWX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ M r)%I)
      (* (* RWLX case *) *)
      (fundamental_RWLX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ M r)%I),
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      □ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
            full_map a0
         -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r0))
         -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
         -∗ Exact_w wγ a7
         -∗ sts_full a3 a4
         -∗ na_own logrel_nais ⊤
         -∗ ⌜a7.1.1 = a3⌝
         → ⌜a7.1.2 = a4⌝
         → □ (∃ p : Perm, ⌜PermFlows RX p⌝
                           ∧ ([∗ list] a8 ∈ region_addrs a5 a6, 
                              na_inv logrel_nais (logN.@a8)
                                     (∃ w0 : leibnizO Word, a8 ↦ₐ[p] w0 ∗ ▷ interp w0)))
             -∗ ⟦ [a3, a4] ⟧ₒ) -∗
      (fixpoint interp1) (inr (p, l, b, e, a)) -∗
      (fixpoint interp1) (inr (p, l, b', e', a)).
  Proof.
    intros. iIntros "#IH Hinterp".
    repeat (rewrite fixpoint_interp1_eq).
    destruct p; simpl; auto; try congruence.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% H]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% H]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% H]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% [H H']]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H3 H4]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
      + iModIntro.
        rewrite /exec_cond.
        iIntros. iNext. rewrite /interp_expr /=.
        iExists _,_. iSplitR; auto. iSplitR; auto.
        iIntros "[[Hfull Hreg] [Hmap [Hex [Hsts Hown]]]]".
        iExists _, _, _, _, _. iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hex] [Hsts] [Hown]"); eauto.
        rewrite /read_write_cond. iAlways.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H3 H4]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% [H H']]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros. iNext. iApply fundamental_RWX.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
    - iDestruct "Hinterp" as (gx bx ex ax) "[% H]".
      iDestruct "H" as (p) "[% [H H']]".
      inv H6. iExists gx, b', e', ax.
      iSplitR; auto.
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros. iNext. iApply fundamental_RWLX.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs. destruct (Z_le_dec b' e'); auto; lia.
  Qed.

  Lemma RX_Subseg_case:
    ∀ r a g M fs fr b e p' w dst (r1 r2: Z + RegName)
      (* RWX case *)
      (fundamental_RWX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWX,g),b,e,a) ⟧ₑ M r)%I)
      (* (* RWLX case *) *)
      (fundamental_RWLX : ∀ b e g a M r,
          ((∃ p, ⌜PermFlows RWLX p⌝ ∧
                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
           ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ M r)%I)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = cap_lang.Subseg dst r1 r2)
      (Heq : fs = M.1.1 ∧ fr = M.1.2),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
            full_map a0
         -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r0))
         -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
         -∗ Exact_w wγ a7
         -∗ sts_full a3 a4
         -∗ na_own logrel_nais ⊤
         -∗ ⌜a7.1.1 = a3⌝
         → ⌜a7.1.2 = a4⌝
         → □ (∃ p : Perm, ⌜PermFlows RX p⌝
                           ∧ ([∗ list] a8 ∈ region_addrs a5 a6, 
                              na_inv logrel_nais (logN.@a8)
                                     (∃ w0 : leibnizO Word, a8 ↦ₐ[p] w0 ∗ ▷ interp w0)))
         -∗ ⟦ [a3, a4] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ ▷ interp w0))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
        -∗ □ ▷ ▷ interp w
        -∗ Exact_w wγ M
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
              ∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais ⊤)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais ⊤
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros r a g M fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval". 
    iIntros "HM Hsts Ha Hown Hcls HPC Hmap".
    destruct Heq as [Heq1 Heq2].
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct r1.
      { case_eq (z_to_addr z); intros.
        - destruct r2.
          + case_eq (z_to_addr z0); intros.
            * case_eq (isWithin a0 a1 b e); intros.
              { case_eq (a+1)%a; intros.
                - iApply (wp_subseg_success_pc_lr with "[HPC Ha]"); eauto; iFrame.
                  rewrite H7 /=. iNext. iIntros "[HPC Ha]".
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                  { iFrame. iNext. iExists _. iFrame. auto. }
                  iApply wp_pure_step_later; auto.
                  iApply ("IH" with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                  iNext. iModIntro. iExists p'; iSplitR; auto.
                  generalize (isWithin_implies _ _ _ _ H6). intros [A B].
                  destruct (Z_le_dec a0 a1).
                  + rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                    iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                    iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                    iFrame "#".
                  + replace (region_addrs a0 a1) with (nil: list Addr).
                    rewrite big_sepL_nil. auto.
                    unfold region_addrs. destruct (Z_le_dec a0 a1); auto; lia.
                - iApply (wp_subseg_success_pc_lr with "[HPC Ha]"); eauto; iFrame.
                  rewrite H7 /=. iNext. iIntros "[HPC Ha]".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value. iNext. iIntros "%". discriminate. }
              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha]"); iFrame; try (iSplitR; auto).
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (reg_eq_dec PC r0).
            * subst r0.
              iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
              destruct wr0.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * iApply (wp_subseg_success_pc_l with "[HPC Ha Hr0]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                      { iFrame. iNext. iExists _. iFrame. auto. }
                      iApply wp_pure_step_later; auto.
                      iApply ("IH" $! (<[r0:=inl z0]> r) _ _ _ _ a0 a1 with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                      { iIntros (x). iPureIntro. destruct (reg_eq_dec r0 x).
                        - subst x; rewrite lookup_insert. eauto.
                        - rewrite lookup_insert_ne; auto. }
                      { iIntros (r1) "%". destruct (reg_eq_dec r0 r1).
                        - subst r0. rewrite /RegLocate lookup_insert.
                          repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                        - rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                      iNext. iModIntro. iExists p'; iSplitR; auto.
                      generalize (isWithin_implies _ _ _ _ H6). intros [A B].
                      destruct (Z_le_dec a0 a1).
                      { rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". }
                      { replace (region_addrs a0 a1) with (nil: list Addr).
                        rewrite big_sepL_nil. auto.
                        unfold region_addrs. destruct (Z_le_dec a0 a1); auto; lia. }
                    * iApply (wp_subseg_success_pc_l with "[HPC Ha Hr0]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iApply wp_pure_step_later; auto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
        - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha]"); iFrame; auto.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
          destruct wr0.
          + case_eq (z_to_addr z); intros.
            * destruct r2.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * iApply (wp_subseg_success_pc_r _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hr0]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                      { iFrame. iNext. iExists _. iFrame. auto. }
                      iApply wp_pure_step_later; auto.
                      iApply ("IH" $! (<[r0:=inl z]> r) _ _ _ _ a0 a1 with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                      { iIntros (x). iPureIntro. destruct (reg_eq_dec r0 x).
                        - subst x; rewrite lookup_insert. eauto.
                        - rewrite lookup_insert_ne; auto. }
                      { iIntros (r1) "%". destruct (reg_eq_dec r0 r1).
                        - subst r0. rewrite /RegLocate lookup_insert.
                          repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                        - rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                      iNext. iModIntro. iExists p'; iSplitR; auto.
                      generalize (isWithin_implies _ _ _ _ H6). intros [A B].
                      destruct (Z_le_dec a0 a1).
                      { rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". }
                      { replace (region_addrs a0 a1) with (nil: list Addr).
                        rewrite big_sepL_nil. auto.
                        unfold region_addrs. destruct (Z_le_dec a0 a1); auto; lia. }
                    * iApply (wp_subseg_success_pc_r _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hr0]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iApply wp_pure_step_later; auto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { destruct (reg_eq_dec PC r1).
                - subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - destruct (reg_eq_dec r0 r1).
                  + subst r1. case_eq (isWithin a0 a0 b e); intros.
                    * case_eq (a+1)%a; intros.
                      { iApply (wp_subseg_success_pc_same with "[HPC Ha Hr0]"); eauto; iFrame.
                        rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                        iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite <- delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                        { iFrame. iNext. iExists _. iFrame. auto. }
                        iApply wp_pure_step_later; auto.
                        iApply ("IH" $! (<[r0:=inl z]> r) _ _ _ _ a0 a0 with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                        { iIntros (x). iPureIntro. destruct (reg_eq_dec r0 x).
                          - subst x; rewrite lookup_insert. eauto.
                          - rewrite lookup_insert_ne; auto. }
                        { iIntros (r1) "%". destruct (reg_eq_dec r0 r1).
                          - subst r0. rewrite /RegLocate lookup_insert.
                            repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                          - rewrite /RegLocate lookup_insert_ne; auto.
                            iApply "Hreg". auto. }
                        iNext. iModIntro. iExists p'; iSplitR; auto.
                        generalize (isWithin_implies _ _ _ _ H5). intros [A B].
                        rewrite (isWithin_region_addrs_decomposition a0 a0 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". repeat (split; auto). unfold le_addr; lia. }
                      { iApply (wp_subseg_success_pc_same with "[HPC Ha Hr0]"); eauto; iFrame.
                        rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                        iApply wp_pure_step_later; auto.
                        iApply wp_value. iNext. iIntros "%". discriminate. }
                    * iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H4 H5 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence. auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + destruct (H3 r1) as [wr1 Hsomer1].
                    iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                    destruct wr1.
                    * case_eq (z_to_addr z0); intros.
                      { case_eq (isWithin a0 a1 b e); intros.
                        - case_eq (a+1)%a; intros.
                          + iApply (wp_subseg_success_pc _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hr0 Hr1]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hr1]]]".
                            iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; auto.
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; auto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                            { iFrame. iNext. iExists _. iFrame. auto. }
                            iApply wp_pure_step_later; auto.
                            iApply ("IH" $! (<[r0:=inl z]> (<[r1:=inl z0]> r)) _ _ _ _ a0 a1 with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                            { iIntros (x). iPureIntro. destruct (reg_eq_dec r0 x).
                              - subst x; rewrite lookup_insert. eauto.
                              - destruct (reg_eq_dec r1 x).
                                + rewrite lookup_insert_ne; auto.
                                  subst x; rewrite lookup_insert. eauto.
                                + repeat rewrite lookup_insert_ne; auto. }
                            { iIntros (x) "%". destruct (reg_eq_dec r0 x).
                              - subst r0. rewrite /RegLocate lookup_insert.
                                repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                              - rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r1 x).
                                + subst x. rewrite lookup_insert.
                                  repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                                + rewrite lookup_insert_ne; auto.
                                  iApply "Hreg". auto. }
                            iNext. iModIntro. iExists p'; iSplitR; auto.
                            generalize (isWithin_implies _ _ _ _ H6). intros [A B].
                            destruct (Z_le_dec a0 a1).
                            * rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                              iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                              iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                              iFrame "#".
                            * replace (region_addrs a0 a1) with (nil: list Addr).
                              rewrite big_sepL_nil. auto.
                              unfold region_addrs. destruct (Z_le_dec a0 a1); auto; lia.
                          + iApply (wp_subseg_success_pc _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hr0 Hr1]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hr1]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                        - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0 Hr1]"); iFrame; try (iSplitL; auto). destruct (reg_eq_dec r0 r1); try congruence; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                      { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr1]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr1]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC dst); eauto|].
      destruct wdst.
      { iApply (wp_subseg_fail_dst_z _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hdst]"); iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c,p,p,p. destruct r1.
        - case_eq (z_to_addr z); intros.
          + destruct r2.
            * case_eq (z_to_addr z0); intros.
              { case_eq (isWithin a3 a4 a2 a1); intros.
                - case_eq (a+1)%a; intros.
                  + destruct (perm_eq_dec p E).
                    * subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                      iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                    * iApply (wp_subseg_success_lr with "[HPC Ha Hdst]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hdst]]".
                      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; eauto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                      { iFrame. iNext. iExists _. iFrame. auto. }
                      iApply wp_pure_step_later; auto.
                      iApply ("IH" $! (<[dst:=inr (p, l, a3, a4, a0)]> r) with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                      { iIntros (x). iPureIntro.
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite lookup_insert. eauto.
                        - rewrite lookup_insert_ne; auto. }
                      { iIntros (x) "%".
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite /RegLocate lookup_insert.
                          iDestruct ("Hreg" $! dst a6) as "Hdst".
                          rewrite Hsomedst. apply isWithin_implies in H6. destruct H6.
                          iApply (subseg_interp_preserved with "[Hdst IH]"); eauto.
                        - rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                  + destruct (perm_eq_dec p E).
                    * subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                      iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                    * iApply (wp_subseg_success_lr with "[HPC Ha Hdst]"); eauto; iFrame.
                      rewrite H7 /=. iNext. iIntros "[HPC [Ha Hdst]]".
                      iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * destruct (reg_eq_dec PC r0).
              { subst r0. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
              { destruct (reg_eq_dec dst r0).
                - subst r0. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hdst]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                  destruct wr0.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - destruct (perm_eq_dec p E).
                          + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_l with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                            { iFrame. iNext. iExists _. iFrame. auto. }
                            iApply wp_pure_step_later; auto.
                            iApply ("IH" $! (<[dst:=inr (p, l, a3, a4, a0)]> (<[r0:=inl z0]> r)) with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                      { iIntros (x). iPureIntro.
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite lookup_insert. eauto.
                        - rewrite lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 x).
                          + subst x. rewrite lookup_insert. eauto.
                          + rewrite lookup_insert_ne; auto. }
                      { iIntros (x) "%".
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite /RegLocate lookup_insert.
                          iDestruct ("Hreg" $! dst a6) as "Hdst".
                          rewrite Hsomedst. apply isWithin_implies in H6. destruct H6.
                          iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                        - rewrite /RegLocate lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 x).
                          + subst x. rewrite lookup_insert.
                            repeat (rewrite fixpoint_interp1_eq); eauto.
                          + rewrite lookup_insert_ne; auto.
                            iApply "Hreg". auto. }
                        - destruct (perm_eq_dec p E).
                          + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_l with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
          + iApply (wp_subseg_fail_convert1 with "[HPC Ha]"); eauto; iFrame; auto.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate.
        - destruct (reg_eq_dec PC r0).
          + subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hdst]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
              destruct wr0.
              { case_eq (z_to_addr z); intros.
                - destruct r2.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - destruct (perm_eq_dec p E).
                          + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                            { iFrame. iNext. iExists _. iFrame. auto. }
                            iApply wp_pure_step_later; auto.
                            iApply ("IH" $! (<[dst:=inr (p, l, a3, a4, a0)]> (<[r0:=inl z]> r)) with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                            { iIntros (x). iPureIntro.
                              destruct (reg_eq_dec dst x).
                              - subst x. rewrite lookup_insert. eauto.
                              - rewrite lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 x).
                                + subst x. rewrite lookup_insert. eauto.
                                + rewrite lookup_insert_ne; auto. }
                            { iIntros (x) "%".
                              destruct (reg_eq_dec dst x).
                              - subst x. rewrite /RegLocate lookup_insert.
                                iDestruct ("Hreg" $! dst a6) as "Hdst".
                                rewrite Hsomedst. apply isWithin_implies in H6. destruct H6.
                                iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                              - rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 x).
                                + subst x. rewrite lookup_insert.
                                  repeat (rewrite fixpoint_interp1_eq); eauto.
                                + rewrite lookup_insert_ne; auto.
                                  iApply "Hreg". auto. }
                        - destruct (perm_eq_dec p E).
                          + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + destruct (reg_eq_dec PC r1).
                    * subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                    * destruct (reg_eq_dec dst r1).
                      { subst r1. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hdst]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                      { destruct (reg_eq_dec r0 r1).
                        - subst r1. case_eq (isWithin a3 a3 a2 a1); intros.
                          + case_eq (a+1)%a; intros.
                            * destruct (perm_eq_dec p E).
                              { subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_success_same with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                                rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                repeat rewrite <- delete_insert_ne; auto.
                                iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                repeat rewrite <- delete_insert_ne; auto.
                                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                                { iFrame. iNext. iExists _. iFrame. auto. }
                                iApply wp_pure_step_later; auto.
                                iApply ("IH" $! (<[dst:=inr (p, l, a3, a3, a0)]> (<[r0:=inl z]> r)) with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                                { iIntros (x). iPureIntro. destruct (reg_eq_dec dst x).
                                  - subst x. rewrite lookup_insert. eauto.
                                  - rewrite lookup_insert_ne; auto.
                                    destruct (reg_eq_dec r0 x).
                                    + subst x; rewrite lookup_insert. eauto.
                                    + rewrite lookup_insert_ne; auto. }
                                { iIntros (x) "%". destruct (reg_eq_dec dst x).
                                  - subst x. rewrite /RegLocate lookup_insert.
                                    iDestruct ("Hreg" $! dst a5) as "Hdst".
                                    rewrite Hsomedst. apply isWithin_implies in H5. destruct H5.
                                    iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                                  - rewrite /RegLocate lookup_insert_ne; auto.
                                    destruct (reg_eq_dec r0 x).
                                    + subst r0. rewrite /RegLocate lookup_insert.
                                      repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                                    + rewrite /RegLocate lookup_insert_ne; auto.
                                      iApply "Hreg". auto. } }
                            * destruct (perm_eq_dec p E).
                              { subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_success_same with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                                rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                                iApply wp_pure_step_later; auto.
                                iApply wp_value. iNext. iIntros "%".
                                discriminate. }
                          + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H4 H5 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence; auto.
                            destruct (reg_eq_dec PC dst); try congruence; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate.
                        - destruct (H3 r1) as [wr1 Hsomer1].
                          iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                          destruct wr1.
                          + case_eq (z_to_addr z0); intros.
                            * case_eq (isWithin a3 a4 a2 a1); intros.
                              { case_eq (a+1)%a; intros.
                                - destruct (perm_eq_dec p E).
                                  + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                    iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                    iApply wp_value. iNext. iIntros "%". discriminate.
                                  + iApply (wp_subseg_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hdst Hr0 Hr1]"); eauto; iFrame.
                                    rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 [Hr1 Hdst]]]]".
                                    iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                    repeat rewrite <- delete_insert_ne; eauto.
                                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                    repeat rewrite <- delete_insert_ne; eauto.
                                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                    rewrite <- delete_insert_ne; eauto.
                                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                    iMod ("Hcls" with "[Ha Hown]") as "Hcls'"; auto.
                                    { iFrame. iNext. iExists _. iFrame. auto. }
                                    iApply wp_pure_step_later; auto.
                                    iApply ("IH" $! (<[dst:=inr (p, l, a3, a4, a0)]> (<[r0:=inl z]> (<[r1:=inl z0]> r))) with "[] [] [Hmap] [HM] [Hsts] [Hcls']"); auto.
                                    { iIntros (x). iPureIntro.
                                      destruct (reg_eq_dec dst x).
                                      - subst x. rewrite lookup_insert. eauto.
                                      - rewrite lookup_insert_ne; auto.
                                        destruct (reg_eq_dec r0 x).
                                        + subst x. rewrite lookup_insert. eauto.
                                        + rewrite lookup_insert_ne; auto.
                                          destruct (reg_eq_dec r1 x).
                                          * subst x. rewrite lookup_insert. eauto.
                                          * rewrite lookup_insert_ne; auto. }
                                    { iIntros (x) "%".
                                      destruct (reg_eq_dec dst x).
                                      - subst x. rewrite /RegLocate lookup_insert.
                                        iDestruct ("Hreg" $! dst a6) as "Hdst".
                                        rewrite Hsomedst. apply isWithin_implies in H6. destruct H6.
                                        iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                                      - rewrite /RegLocate lookup_insert_ne; auto.
                                        destruct (reg_eq_dec r0 x).
                                        + subst x. rewrite lookup_insert.
                                          repeat (rewrite fixpoint_interp1_eq); eauto.
                                        + rewrite lookup_insert_ne; auto.
                                          destruct (reg_eq_dec r1 x).
                                          * subst x. rewrite lookup_insert.
                                            repeat (rewrite fixpoint_interp1_eq); eauto.
                                          * rewrite lookup_insert_ne; auto.
                                            iApply "Hreg". auto. }
                                - destruct (perm_eq_dec p E).
                                  + subst p. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                    iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                    iApply wp_value. iNext. iIntros "%". discriminate.
                                  + iApply (wp_subseg_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hdst Hr0 Hr1]"); eauto; iFrame.
                                    rewrite H7 /=. iNext. iIntros "[HPC [Ha [Hr0 [Hr1 Hdst]]]]".
                                    iApply wp_pure_step_later; auto.
                                    iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 H5 H6 with "[HPC Ha Hr0 Hr1 Hdst]"); iFrame. iSplitL "Hr1". destruct (reg_eq_dec r0 r1); try congruence; auto.
                                destruct (reg_eq_dec PC dst); try congruence; auto.
                                iNext. iIntros. iApply wp_pure_step_later; auto.
                                iNext. iApply wp_value; auto. iIntros; discriminate. }
                            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H5 with "[HPC Ha Hr0 Hr1]"); iFrame; auto.
                              iNext. iIntros. iApply wp_pure_step_later; auto.
                              iNext. iApply wp_value; auto. iIntros; discriminate.
                          + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr1]"); iFrame; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. } }
      Unshelve.
      assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption.
  Qed.*)

End fundamental.