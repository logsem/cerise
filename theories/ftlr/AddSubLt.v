From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

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

  Lemma add_sub_lt_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r1 r2: Z + RegName): 
      p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Local)
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → (if pwl p then region_state_pwl W a else region_state_nwl W a g)
    → region_std W a
    → std_sta W !! countable.encode a = Some (countable.encode ρ)
    → ρ ≠ Revoked 
    → p' ≠ O
    → (cap_lang.decode w = cap_lang.Add dst r1 r2 \/
       cap_lang.decode w = Sub dst r1 r2 \/
       cap_lang.decode w = Lt dst r1 r2)
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
             full_map a1
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) a0) (a1 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1)
          -∗ region a0
          -∗ sts_full_world sts_std a0
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a2 = RX ∨ a2 = RWX ∨ (a2 = RWLX /\ a3 = Local)⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a2 p'0⌝
                                ∧ ([∗ list] a7 ∈ region_addrs a4 a5, read_write_cond a7 p'0 interp                                                                     
                                                                     ∧ ⌜if pwl a2
                                                                        then region_state_pwl a0 a7
                                                                        else region_state_nwl a0 a7 a3⌝
                                                                     ∧ ⌜region_std a0 a7⌝))
                 -∗ interp_conf a0)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp
                                        ∧ ⌜if pwl p
                                           then region_state_pwl W a0
                                           else region_state_nwl W a0 g⌝
                                        ∧ ⌜region_std W a0⌝)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ (▷ if decide (ρ = Temporary ∧ pwl p' = true)
        then future_pub_mono (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2) w
        else future_priv_mono (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2) w)
    -∗ ▷ ((fixpoint interp1) W) w
    -∗ sts_full_world sts_std W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std (countable.encode a) ρ
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (W' : WORLD),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv_world W W'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full_world sts_std W' ∗ region W' }} }}.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec dst PC).
    * subst dst.
      destruct r1; destruct r2.
      { iApply (wp_add_sub_lt_success with "[Ha HPC]"); eauto.
        - destruct (reg_eq_dec PC PC); auto; try congruence. iFrame. eauto.
        - iNext. destruct (reg_eq_dec PC PC); try congruence.
          iIntros "(_ & Ha & _ & _ & HPC)".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iApply wp_value. iNext. iIntros. congruence. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate a0.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + iApply (wp_add_sub_lt_success with "[Ha HPC Hr0]"); eauto.
            * destruct (reg_eq_dec PC PC); auto; try congruence.
              destruct (reg_eq_dec r0 PC); iFrame; eauto.
            * iNext. destruct (reg_eq_dec PC PC); try congruence.
              destruct (reg_eq_dec r0 PC); try congruence.
              iIntros "(_ & Ha & _ & Hr0 & HPC)".
              iApply wp_pure_step_later; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply wp_value. iNext. iIntros. discriminate a0.
          + iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr0]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + iApply (wp_add_sub_lt_success with "[Ha HPC Hr0]"); eauto.
            * destruct (reg_eq_dec PC PC); auto; try congruence.
              destruct (reg_eq_dec r0 PC); iFrame; eauto.
            * iNext. destruct (reg_eq_dec PC PC); try congruence.
              destruct (reg_eq_dec r0 PC); try congruence.
              iIntros "(_ & Ha & Hr0 & _ & HPC)".
              iApply wp_pure_step_later; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply wp_value. iNext; iIntros; discriminate.
          + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (reg_eq_dec PC r1).
          + subst r1. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate.
          + destruct (Hsome r0) as [wr0 Hsomer0].
            destruct (Hsome r1) as [wr1 Hsomer1].
            iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            rewrite lookup_delete_ne; eauto.
            destruct (reg_eq_dec r0 r1).
            * subst r1. destruct wr0.
              { iApply (wp_add_sub_lt_success_same with "[Ha HPC Hr0]"); eauto.
                - destruct (reg_eq_dec PC PC); auto; try congruence.
                  destruct (reg_eq_dec r0 PC); iFrame; eauto.
                - iNext. destruct (reg_eq_dec r0 PC); try congruence.
                  destruct (reg_eq_dec PC PC); try congruence.
                  iIntros "(_ & Ha & Hr0 & HPC)".
                  iApply wp_pure_step_later; auto.
                  iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  repeat rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply wp_value. iNext; iIntros; discriminate. } 
              { iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iApply wp_pure_step_later; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iApply wp_value. iNext; iIntros; discriminate. } 
            * iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
              repeat rewrite lookup_delete_ne; eauto.
              destruct wr0.
              { destruct wr1.
                - iApply (wp_add_sub_lt_success with "[Ha HPC Hr0 Hr1]"); eauto.
                  + destruct (reg_eq_dec PC PC); auto; try congruence.
                    destruct (reg_eq_dec r0 PC); iFrame; eauto.
                    destruct (reg_eq_dec r1 PC); auto.
                  + simpl. destruct (reg_eq_dec r0 PC); try congruence.
                    destruct (reg_eq_dec r1 PC); try congruence.
                    destruct (reg_eq_dec PC PC); try congruence.
                    iNext. iIntros "(_ & Ha & Hr0 & Hr1 & HPC)".
                    iApply wp_pure_step_later; auto.
                    iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_value. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hr1)".
                  iApply wp_pure_step_later; auto.
                  iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  repeat rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply wp_value. iNext; iIntros; discriminate. }
              { iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iApply wp_pure_step_later; auto.
                iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iApply wp_value. iNext; iIntros; discriminate. } }
    * destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
      rewrite lookup_delete_ne; eauto.
      destruct r1; destruct r2.
      { iApply (wp_add_sub_lt_success with "[Ha Hdst HPC]"); eauto.
        - destruct (reg_eq_dec dst PC); eauto; iFrame; eauto.
        - iNext. destruct (reg_eq_dec dst PC); try congruence.
          iIntros "(HPC & Ha & _ & _ & Hdst)".
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          assert (PureExec True 1 (Seq (cap_lang.of_val match (a + 1)%a with | Some _ => NextIV | None => FailedV end)) match (a + 1)%a with | Some _ => Seq (Instr Executable) | None => Instr Failed end).
          { destruct (a+1)%a; auto. apply pure_seq_done. apply pure_seq_failed. }
          iApply (wp_pure_step_later); auto. iNext.
          iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                             | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                             | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                             | Sub _ _ _ => inl (z - z0)%Z
                                             | _ => inl 0%Z
                                             end]> r)))%I
            as "#[Hfull' Hreg']".
          { iSplitR.
            - iIntros (r0). 
              destruct (Hsome r0) as [c Hsomec].
              iPureIntro.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0 Hnepc) "/=".
              destruct (Hsome r0) as [c Hsomec].
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                destruct (cap_lang.decode w); simpl; eauto.
              + rewrite /RegLocate lookup_insert_ne; auto.
                iDestruct ("Hreg" $! (r0)) as "Hv". iApply "Hv". auto. }
          destruct (a+1)%a.
          -- iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
             iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          -- iApply wp_value. iIntros. discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          destruct (reg_eq_dec dst r0).
          + subst r0. destruct wdst.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec dst dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 iIntros "(HPC & Ha & _ & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                    iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                       | Sub _ _ _ => inl (z - z0)%Z
                                                       | _ => inl 0%Z
                                                       end]> r)))%I
                      as "#[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r0). 
                        destruct (Hsome r0) as [c Hsomex].
                        iPureIntro.
                        destruct (decide (dst = r0)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r0 Hnepc) "/=".
                        destruct (Hsome r0) as [c Hsomec].
                        destruct (decide (dst = r0)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          iDestruct ("Hreg" $! (r0)) as "Hv". iApply "Hv". auto. }
                    iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            repeat rewrite lookup_delete_ne; eauto.
            destruct wr0.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec r0 dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 destruct (reg_eq_dec r0 dst); try congruence.
                 iIntros "(HPC & Ha & _ & Hr0 & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                    iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                       | Sub _ _ _ => inl (z - z0)%Z
                                                       | _ => inl 0%Z
                                                       end]> (<[r0:=inl z0]> r))))%I
                      as "#[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r1).
                        destruct (Hsome r1) as [c Hsomec].
                        iPureIntro.
                        destruct (decide (dst = r1)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        destruct (reg_eq_dec r0 r1); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r1 Hnepc) "/=".
                        destruct (Hsome r1) as [c Hsomec].
                        destruct (decide (dst = r1)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 r1); simplify_eq.
                          * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                          * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                    iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          destruct (reg_eq_dec dst r0).
          + subst r0. destruct wdst.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec dst dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 iIntros "(HPC & Ha & _ & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                    iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                       | Sub _ _ _ => inl (z0 - z)%Z
                                                       | _ => inl 0%Z
                                                       end]> r)))%I
                      as "#[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r0). 
                        destruct (Hsome r0) as [c Hsomec].
                        iPureIntro.
                        destruct (decide (dst = r0)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r0 Hnepc) "/=".
                        destruct (Hsome r0) as [c Hsomec].
                        destruct (decide (dst = r0)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                    iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            repeat rewrite lookup_delete_ne; eauto.
            destruct wr0.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec r0 dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 destruct (reg_eq_dec r0 dst); try congruence.
                 iIntros "(HPC & Ha & Hr0 & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                    iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                       | Sub _ _ _ => inl (z0 - z)%Z
                                                       | _ => inl 0%Z
                                                       end]> (<[r0:=inl z0]> r))))%I
                      as "#[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r1).
                        destruct (Hsome r1) as [c Hsomec].
                        iPureIntro.
                        destruct (decide (dst = r1)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        destruct (reg_eq_dec r0 r1); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r1 Hnepc) "/=".
                        destruct (Hsome r1) as [c Hsomec].
                        destruct (decide (dst = r1)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 r1); simplify_eq.
                          * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                          * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                    iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (reg_eq_dec PC r1).
          + subst r1. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
            * iFrame.
            * iNext. iIntros "(HPC & Ha)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate.
          + destruct (Hsome r0) as [wr0 Hsomer0].
            destruct (Hsome r1) as [wr1 Hsomer1].
            destruct (reg_eq_dec dst r0).
            * subst r0. destruct (reg_eq_dec dst r1).
              { subst r1. destruct wdst.
                - iApply (wp_add_sub_lt_success_same with "[Ha HPC Hdst]"); eauto.
                  + simpl; iFrame. destruct (reg_eq_dec dst dst); auto; congruence.
                  + iNext. destruct (reg_eq_dec dst PC); try congruence.
                    iIntros "(HPC & Ha & _ & Hdst)".
                    case_eq (a+1)%a; intros.
                    * iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iApply wp_pure_step_later; auto. iNext.
                      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                      iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                         | Lt _ _ _ => inl (Z.b2z (z <? z)%Z)
                                                         | cap_lang.Add _ _ _ => inl (z + z)%Z
                                                         | Sub _ _ _ => inl (z - z)%Z
                                                         | _ => inl 0%Z
                                                         end]> r)))%I
                        as "#[Hfull' Hreg']".
                      { iSplitR.
                        - iIntros (r1).
                          destruct (Hsome r1) as [c Hsomec].
                          iPureIntro.
                          destruct (decide (dst = r1)); simplify_eq;
                            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        - iIntros (r1 Hnepc) "/=".
                          destruct (Hsome r1) as [c Hsomec].
                          destruct (decide (dst = r1)); simplify_eq.
                          + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                            destruct (cap_lang.decode w); simpl; eauto.
                          + rewrite /RegLocate lookup_insert_ne; auto.
                            iApply "Hreg". auto. }
                      iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                    * iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wdst.
                - destruct wr1.
                  + iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr1]"); eauto.
                    * iFrame. destruct (reg_eq_dec dst dst); try congruence; auto.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r1 dst); try congruence.
                      iIntros "(HPC & Ha & _ & Hr1 & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                        iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                           | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                           | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                           | Sub _ _ _ => inl (z - z0)%Z
                                                           | _ => inl 0%Z
                                                           end]> (<[r1:=inl z0]> r))))%I
                          as "#[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r2).
                            destruct (Hsome r2) as [c Hsomec].
                            iPureIntro.
                            destruct (decide (dst = r2)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r1 r2); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r2 Hnepc) "/=".
                            destruct (Hsome r2) as [c Hsomec].
                            destruct (decide (dst = r2)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r1 r2); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                      }
                      iApply wp_pure_step_later; auto.
                      iApply wp_value; auto. iNext; iIntros; discriminate.
                  + iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr1)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
            * iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              repeat rewrite lookup_delete_ne; eauto.
              destruct (reg_eq_dec dst r1).
              { subst r1. destruct wdst.
                - destruct wr0.
                  + iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
                    * simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                      destruct (reg_eq_dec dst dst); auto; congruence.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r0 dst); try congruence.
                      iIntros "(HPC & Ha & Hr0 & _ & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                        iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                           | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                           | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                           | Sub _ _ _ => inl (z0 - z)%Z
                                                           | _ => inl 0%Z
                                                           end]> (<[r0:=inl z0]> r))))%I
                          as "#[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r1).
                            destruct (Hsome r1) as [c Hsomec].
                            iPureIntro.
                            destruct (decide (dst = r1)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r0 r1); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r1 Hnepc) "/=".
                            destruct (Hsome r1) as [c Hsomec].
                            destruct (decide (dst = r1)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r0 r1); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                      }
                      { iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
              { destruct (reg_eq_dec r0 r1).
                - subst r1. destruct wr0.
                  + iApply (wp_add_sub_lt_success_same with "[Ha HPC Hdst Hr0]"); eauto.
                    * simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                      destruct (reg_eq_dec dst PC); auto; congruence.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r0 dst); try congruence.
                      iIntros "(HPC & Ha & Hr0 & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                        iAssert ((interp_registers _ (<[dst:= match cap_lang.decode w with
                                                            | Lt _ _ _ => inl (Z.b2z (z <? z)%Z)
                                                            | cap_lang.Add _ _ _ => inl (z + z)%Z
                                                            | Sub _ _ _ => inl (z - z)%Z
                                                            | _ => inl 0%Z
                                                            end]> (<[r0:=inl z]> r))))%I
                          as "#[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r1).
                            destruct (Hsome r1) as [c Hsomec].
                            iPureIntro.
                            destruct (decide (dst = r1)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r0 r1); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r1 Hnepc) "/=".
                            destruct (Hsome r1) as [c Hsomec].
                            destruct (decide (dst = r1)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r0 r1); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                      }
                      { iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
                  repeat rewrite lookup_delete_ne; eauto.
                  destruct wr0.
                  + destruct wr1.
                    * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0 Hr1]"); eauto.
                      { simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                        destruct (reg_eq_dec r1 dst); destruct (reg_eq_dec dst PC); try congruence; auto. }
                      { iNext. destruct (reg_eq_dec dst PC); try congruence.
                        destruct (reg_eq_dec r0 dst); try congruence.
                        destruct (reg_eq_dec r1 dst); try congruence.
                        iIntros "(HPC & Ha & Hr0 & Hr1 & Hdst)".
                        case_eq (a+1)%a; intros.
                        - iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          iApply wp_pure_step_later; auto. iNext.
                          iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                          iAssert ((interp_registers _ (<[dst:=match cap_lang.decode w with
                                                             | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                             | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                             | Sub _ _ _ => inl (z - z0)%Z
                                                             | _ => inl 0%Z
                                                             end]> (<[r0:=inl z]> (<[r1:=inl z0]> r)))))%I
                            as "#[Hfull' Hreg']".
                          { iSplitR.
                            - iIntros (r2).
                              destruct (Hsome r2) as [c Hsomec].
                              iPureIntro.
                              destruct (decide (dst = r2)); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                              destruct (reg_eq_dec r0 r2); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                              destruct (reg_eq_dec r1 r2); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            - iIntros (r2 Hnepc) "/=".
                              destruct (Hsome r2) as [c Hsomec].
                              destruct (decide (dst = r2)); simplify_eq.
                              + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                                destruct (cap_lang.decode w); simpl; eauto.
                              + rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 r2); simplify_eq.
                                * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                                * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec r1 r2); simplify_eq.
                                  -- rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                                  -- rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                        - iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                      iNext. iIntros "(HPC & Ha & Hr1)". iApply wp_pure_step_later; auto.
                      iApply wp_value; eauto. iNext; iIntros; discriminate.
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate. } }
      Unshelve. exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z).
      exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z).
  Qed.

End fundamental.