From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine Require Import addr_reg.
From cap_machine.rules Require Import rules_Subseg.

(* TODO: Move into logrel.v *)
Instance future_world_persistent (Σ: gFunctors) g W W': Persistent (@future_world Σ g W W').
Proof.
  unfold future_world. destruct g; apply bi.pure_persistent.
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

  (* TODO: This should be move to region.v *)
  Lemma region_split b a e :
    (b <= a /\ a <= e)%a ->
    region_addrs b e = region_addrs b a ++ region_addrs a e.
  Proof.
    intros [? ?].
    rewrite /region_addrs.
    rewrite (region_addrs_aux_decomposition (region_size b e) b (region_size b a)).
    2: unfold region_size; solve_addr.
    do 2 f_equal; unfold region_size; solve_addr.
  Qed.

  (* TODO: This should be move to region.v *)
  Lemma isWithin_region_addrs_decomposition a0 a1 b e:
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%a ->
    region_addrs b e = region_addrs b a0 ++
                       region_addrs a0 a1 ++
                       region_addrs a1 e.
  Proof with try (unfold region_size; solve_addr).
    intros (Hba0 & Ha1e & Ha0a1).
    rewrite (region_split b a0 e)... f_equal.
    rewrite (region_split a0 a1 e)...
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

  Lemma subseg_interp_preserved W p l b b' e e' a :
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      □ ▷ (∀ (a7 : leibnizO (STS * STS)) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
             (a11 a12 a13 : Addr),
              full_map a8
                       -∗ (∀ r1 : RegName,
                              ⌜r1 ≠ PC⌝
                              → ((fixpoint interp1) a7)
                                  match a8 !! r1 with
                                  | Some w0 => w0
                                  | None => inl 0%Z
                                  end)
                       -∗ registers_mapsto (<[PC:=inr (a9, a10, a11, a12, a13)]> a8)
                       -∗ region a7
                       -∗ sts_full_world sts_std a7
                       -∗ na_own logrel_nais ⊤
                       -∗ ⌜a9 = RX ∨ a9 = RWX ∨ a9 = RWLX ∧ a10 = Local⌝
              → □ (∃ p'0 : Perm,
                      ⌜PermFlows a9 p'0⌝
                      ∧ ([∗ list] a14 ∈ region_addrs a11 a12, 
                         read_write_cond a14 p'0 interp
                         ∧ ⌜if pwl a9
                            then region_state_pwl a7 a14
                            else region_state_nwl a7 a14 a10⌝
                                 ∧ ⌜region_std a7 a14⌝)) -∗ 
                  interp_conf a7) -∗
      (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
      (fixpoint interp1) W (inr (p, l, b', e', a)).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    repeat (rewrite fixpoint_interp1_eq).
    destruct p; simpl; auto; try congruence.
    - iDestruct "Hinterp" as (p Hfl) "H".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% H]".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - destruct l; auto.
      iDestruct "Hinterp" as (p) "[% H]".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% [H H']]".
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
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro.
        rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hregion [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hregion] [Hsts] [Hown]"); eauto.
        rewrite /read_write_cond. iAlways.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H3 H4]".
          simpl. destruct l; simpl; iDestruct "Hfuture" as %Hfuture.
          { iApply (big_sepL_mono with "H3"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H5). auto.
            - eapply related_sts_rel_std; eauto. }
          { iApply (big_sepL_mono with "H3"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H5); eauto.
            - eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% [H H']]".
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
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hex [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hex] [Hsts] [Hown]"); eauto.
        iAlways. iExists p; iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          simpl. destruct l; simpl; iDestruct "Hfuture" as %Hfuture.
          { iApply (big_sepL_mono with "H4"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H5). auto.
            - eapply related_sts_rel_std; eauto. }
          { iApply (big_sepL_mono with "H4"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H5); eauto.
            - eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - destruct l; auto. iDestruct "Hinterp" as (p) "[% [H H']]".
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
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hex [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hex] [Hsts] [Hown]"); eauto.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          simpl. iDestruct "Hfuture" as %Hfuture.
          iApply (big_sepL_mono with "H4"). intros.
          simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
          iPureIntro. split.
          { eapply region_state_pwl_monotone; eauto. }
          { eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
          Unshelve. assumption. assumption. assumption. assumption.
  Qed.

  Lemma subseg_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName):
    ftlr_instr W r p p' g b e a w (Subseg dst r1 r2) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst.
      destruct r1.
      { case_eq (z_to_addr z); intros.
        - destruct r2.
          + case_eq (z_to_addr z0); intros.
            * case_eq (isWithin a0 a1 b e); intros.
              { case_eq (a+1)%a; intros.
                - iApply (wp_subseg_success_pc_lr with "[$HPC $Ha]"); eauto.
                  { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                  rewrite H6 /=. iNext. iIntros "[HPC Ha]".
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply wp_pure_step_later; auto.
                  iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                  iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                  iNext. iModIntro. iExists p'; iSplitR; auto. 
                  generalize (isWithin_implies _ _ _ _ H5). intros [A B].
                  destruct (Z_le_dec a0 a1).
                  + rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                    rewrite fixpoint_interp1_eq /=.
                    iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                    iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                    iFrame "#".
                  + replace (region_addrs a0 a1) with (nil: list Addr).
                    rewrite big_sepL_nil. auto.
                    unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
                - iApply (wp_subseg_success_pc_lr with "[$HPC $Ha]"); eauto.
                  { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                  rewrite H6 /=. iNext. iIntros "[HPC Ha]".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value. iNext. iIntros "%". discriminate. }
              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha]"); iFrame; try (iSplitR; auto).
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + destruct (reg_eq_dec PC r0).
            * subst r0.
              iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            * destruct (Hsome r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
              destruct wr0.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * iApply (wp_subseg_success_pc_l with "[$HPC $Ha $Hr0]"); eauto.
                      { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iApply wp_pure_step_later; auto.
                      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                      iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                      destruct (Z_le_dec a0 a1).
                      { rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". }
                      { replace (region_addrs a0 a1) with (nil: list Addr).
                        rewrite big_sepL_nil. auto.
                        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia. }
                    * iApply (wp_subseg_success_pc_l with "[$HPC $Ha $Hr0]"); eauto.
                      { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iApply wp_pure_step_later; auto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
        - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 with "[HPC Ha]"); iFrame; auto.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha]"); iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value; auto. iIntros; discriminate.
        - destruct (Hsome r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
          destruct wr0.
          + case_eq (z_to_addr z); intros.
            * destruct r2.
              { case_eq (z_to_addr z0); intros.
                - case_eq (isWithin a0 a1 b e); intros.
                  + case_eq (a+1)%a; intros.
                    * iApply (wp_subseg_success_pc_r with "[$HPC $Ha $Hr0]"); eauto.
                      { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iApply wp_pure_step_later; auto.
                      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                      iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                      destruct (Z_le_dec a0 a1).
                      { rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". }
                      { replace (region_addrs a0 a1) with (nil: list Addr).
                        rewrite big_sepL_nil. auto.
                        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia. }
                    * iApply (wp_subseg_success_pc_r _ _ _ _ _ _ _ _ z z0 with "[$HPC $Ha $Hr0]"); eauto.
                      { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                      iApply wp_pure_step_later; auto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                  + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[$HPC $Ha $Hr0]"); try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4
                            with "[$HPC $Ha Hr0]"); auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { destruct (reg_eq_dec PC r1).
                - subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ _ Hi _ i
                                      with "[$HPC $Ha]"). 
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                - destruct (reg_eq_dec r0 r1).
                  + subst r1. case_eq (isWithin a0 a0 b e); intros.
                    * case_eq (a+1)%a; intros.
                      { iApply (wp_subseg_success_pc_same with "[$HPC $Ha $Hr0]"); eauto.
                        { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                        rewrite H5 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                        iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite <- delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto.
                        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                        iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                        { iIntros (x). iPureIntro. destruct (reg_eq_dec r0 x).
                          - subst x; rewrite lookup_insert. eauto.
                          - rewrite lookup_insert_ne; auto. }
                        { iIntros (r1) "%". destruct (reg_eq_dec r0 r1).
                          - subst r0. rewrite /RegLocate lookup_insert.
                            repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                          - rewrite /RegLocate lookup_insert_ne; auto.
                            iApply "Hreg". auto. }
                        iNext. iModIntro. iExists p'; iSplitR; auto.
                        generalize (isWithin_implies _ _ _ _ H4). intros [A B].
                        rewrite (isWithin_region_addrs_decomposition a0 a0 b e); auto.
                        iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                        iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                        iFrame "#". repeat (split; auto). unfold le_addr; lia. }
                      { iApply (wp_subseg_success_pc_same with "[$HPC $Ha $Hr0]"); eauto.
                        { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                        rewrite H5 /=. iNext. iIntros "[HPC [Ha Hr0]]".
                        iApply wp_pure_step_later; auto.
                        iApply wp_value. iNext. iIntros "%". discriminate. }
                    * iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H3 H4 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence. auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                  + destruct (Hsome r1) as [wr1 Hsomer1].
                    iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                    destruct wr1.
                    * case_eq (z_to_addr z0); intros.
                      { case_eq (isWithin a0 a1 b e); intros.
                        - case_eq (a+1)%a; intros.
                          + iApply (wp_subseg_success_pc _ _ _ _ _ _ _ _ _ z z0 with
                                        "[$HPC $Ha $Hr0 $Hr1]"); eauto.
                            { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hr1]]]".
                            iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; auto.
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; auto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                             iApply wp_pure_step_later; auto.
                             iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                             iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                             generalize (isWithin_implies _ _ _ _ H5). intros [A B].
                             destruct (Z_le_dec a0 a1).
                            * rewrite (isWithin_region_addrs_decomposition a0 a1 b e); auto.
                              iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
                              iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
                              iFrame "#".
                            * replace (region_addrs a0 a1) with (nil: list Addr).
                              rewrite big_sepL_nil. auto.
                              unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
                          + iApply (wp_subseg_success_pc _ _ _ _ _ _ _ _ _ z z0
                                      with "[$HPC $Ha $Hr0 $Hr1]"); eauto.
                            { destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; rewrite Hp; auto. }
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hr1]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                        - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hr0 Hr1]"); iFrame; try (iSplitL; auto). destruct (reg_eq_dec r0 r1); try congruence; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                      { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr1]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr1]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 with "[HPC Ha Hr0]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
          + iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
    * destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC dst); eauto|].
      destruct wdst.
      { iApply (wp_subseg_fail_dst_z _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hdst]"); iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value; auto. iIntros; discriminate. }
      { destruct c,p0,p0,p0. destruct r1.
        - case_eq (z_to_addr z); intros.
          + destruct r2.
            * case_eq (z_to_addr z0); intros.
              { case_eq (isWithin a3 a4 a2 a1); intros.
                - case_eq (a+1)%a; intros.
                  + destruct (perm_eq_dec p0 E).
                    * subst p0. iApply (wp_subseg_fail_dst_E with "[$HPC $Ha $Hdst]"); eauto.
                      iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                    * iApply (wp_subseg_success_lr with "[$HPC $Ha $Hdst]"); eauto. 
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hdst]]".
                      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      rewrite <- delete_insert_ne; eauto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iApply wp_pure_step_later; auto.
                      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                      iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                      { iIntros (x). iPureIntro.
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite lookup_insert. eauto.
                        - rewrite lookup_insert_ne; auto. }
                      { iIntros (x) "%".
                        destruct (reg_eq_dec dst x).
                        - subst x. rewrite /RegLocate lookup_insert.
                          iDestruct ("Hreg" $! dst a6) as "Hdst".
                          rewrite Hsomedst. apply isWithin_implies in H5. destruct H5.
                          iApply (subseg_interp_preserved with "[Hdst IH]"); eauto.
                        - rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                  + destruct (perm_eq_dec p0 E).
                    * subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                      iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                    * iApply (wp_subseg_success_lr with "[HPC Ha Hdst]"); eauto; iFrame.
                      rewrite H6 /=. iNext. iIntros "[HPC [Ha Hdst]]".
                      iApply wp_pure_step_later; eauto.
                      iApply wp_value. iNext. iIntros "%". discriminate.
                - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha]"); iFrame; auto.
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
                - destruct (Hsome r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                  destruct wr0.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - destruct (perm_eq_dec p0 E).
                          + subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_l with "[$HPC $Ha $Hdst $Hr0]"); eauto. 
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            iApply wp_pure_step_later; auto.
                            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                                rewrite Hsomedst. apply isWithin_implies in H5. destruct H5.
                                iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                              - rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 x).
                                + subst x. rewrite lookup_insert.
                                  repeat (rewrite fixpoint_interp1_eq); eauto.
                                + rewrite lookup_insert_ne; auto.
                                  iApply "Hreg". auto. }
                        - destruct (perm_eq_dec p0 E).
                          + subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_l with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0]"); iFrame; auto.
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
            * destruct (Hsome r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
              destruct wr0.
              { case_eq (z_to_addr z); intros.
                - destruct r2.
                  + case_eq (z_to_addr z0); intros.
                    * case_eq (isWithin a3 a4 a2 a1); intros.
                      { case_eq (a+1)%a; intros.
                        - destruct (perm_eq_dec p0 E).
                          + subst p0. iApply (wp_subseg_fail_dst_E with "[$HPC $Ha $Hdst]"); eauto.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0
                                      with "[$HPC $Ha $Hdst $Hr0]"); eauto.
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            repeat rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            rewrite <- delete_insert_ne; eauto.
                            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                            iApply wp_pure_step_later; auto.
                            iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                                rewrite Hsomedst. apply isWithin_implies in H5. destruct H5.
                                iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                              - rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 x).
                                + subst x. rewrite lookup_insert.
                                  repeat (rewrite fixpoint_interp1_eq); eauto.
                                + rewrite lookup_insert_ne; auto.
                                  iApply "Hreg". auto. }
                        - destruct (perm_eq_dec p0 E).
                          + subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                            iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                            iApply wp_value. iNext. iIntros "%". discriminate.
                          + iApply (wp_subseg_success_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ z z0 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                            rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                            iApply wp_pure_step_later; auto.
                            iApply wp_value. iNext. iIntros "%". discriminate. }
                      { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0]"); iFrame; auto.
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
                            * destruct (perm_eq_dec p0 E).
                              { subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_success_same with "[$HPC $Ha $Hdst $Hr0]"); eauto.
                                rewrite H5 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                repeat rewrite <- delete_insert_ne; auto.
                                iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                repeat rewrite <- delete_insert_ne; auto.
                                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                                iApply wp_pure_step_later; auto.
                                iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                                iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
                                { iIntros (x). iPureIntro. destruct (reg_eq_dec dst x).
                                  - subst x. rewrite lookup_insert. eauto.
                                  - rewrite lookup_insert_ne; auto.
                                    destruct (reg_eq_dec r0 x).
                                    + subst x; rewrite lookup_insert. eauto.
                                    + rewrite lookup_insert_ne; auto. }
                                { iIntros (x) "%". destruct (reg_eq_dec dst x).
                                  - subst x. rewrite /RegLocate lookup_insert.
                                    iDestruct ("Hreg" $! dst a5) as "Hdst".
                                    rewrite Hsomedst. apply isWithin_implies in H4. destruct H4.
                                    iApply (subseg_interp_preserved with "[IH Hdst]"); eauto.
                                  - rewrite /RegLocate lookup_insert_ne; auto.
                                    destruct (reg_eq_dec r0 x).
                                    + subst r0. rewrite /RegLocate lookup_insert.
                                      repeat (rewrite fixpoint_interp1_eq). simpl; eauto.
                                    + rewrite /RegLocate lookup_insert_ne; auto.
                                      iApply "Hreg". auto. } }
                            * destruct (perm_eq_dec p0 E).
                              { subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_success_same with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                                rewrite H5 /=. iNext. iIntros "[HPC [Ha [Hr0 Hdst]]]".
                                iApply wp_pure_step_later; auto.
                                iApply wp_value. iNext. iIntros "%".
                                discriminate. }
                          + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H3 H4 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence; auto.
                            destruct (reg_eq_dec PC dst); try congruence; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate.
                        - destruct (Hsome r1) as [wr1 Hsomer1].
                          iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                          destruct wr1.
                          + case_eq (z_to_addr z0); intros.
                            * case_eq (isWithin a3 a4 a2 a1); intros.
                              { case_eq (a+1)%a; intros.
                                - destruct (perm_eq_dec p0 E).
                                  + subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                    iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                    iApply wp_value. iNext. iIntros "%". discriminate.
                                  + iApply (wp_subseg_success with "[$HPC $Ha $Hdst $Hr0 $Hr1]"); eauto. 
                                    rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 [Hr1 Hdst]]]]".
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
                                    iApply wp_pure_step_later; auto.
                                    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
                                    iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
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
                                        rewrite Hsomedst. apply isWithin_implies in H5. destruct H5.
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
                                - destruct (perm_eq_dec p0 E).
                                  + subst p0. iApply (wp_subseg_fail_dst_E with "[HPC Ha Hdst]"); eauto; iFrame.
                                    iNext. iIntros. simpl. iApply wp_pure_step_later; eauto.
                                    iApply wp_value. iNext. iIntros "%". discriminate.
                                  + iApply (wp_subseg_success with "[$HPC $Ha $Hdst $Hr0 $Hr1]"); eauto. 
                                    rewrite H6 /=. iNext. iIntros "[HPC [Ha [Hr0 [Hr1 Hdst]]]]".
                                    iApply wp_pure_step_later; auto.
                                    iApply wp_value. iNext. iIntros "%". discriminate. }
                              { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 H4 H5 with "[HPC Ha Hr0 Hr1 Hdst]"); iFrame. iSplitL "Hr1". destruct (reg_eq_dec r0 r1); try congruence; auto.
                                destruct (reg_eq_dec PC dst); try congruence; auto.
                                iNext. iIntros. iApply wp_pure_step_later; auto.
                                iNext. iApply wp_value; auto. iIntros; discriminate. }
                            * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H4 with "[HPC Ha Hr0 Hr1]"); iFrame; auto.
                              iNext. iIntros. iApply wp_pure_step_later; auto.
                              iNext. iApply wp_value; auto. iIntros; discriminate.
                          + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr1]"); iFrame; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i H3 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate. }
              { iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ _ Hi _ i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. } }
      Unshelve. all: assumption.
  Qed.

End fundamental.
