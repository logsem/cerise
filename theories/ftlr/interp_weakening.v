From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone region.
From cap_machine Require Import addr_reg.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ (a7 : WORLD) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
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
                     -∗ sts_full_world a7
                     -∗ na_own logrel_nais ⊤
                     -∗ ⌜a9 = RX ∨ a9 = RWX ∨ a9 = RWLX ∧ a10 = Local⌝
            → □ ([∗ list] a14 ∈ region_addrs a11 a12,
                 ∃ p'0 : Perm,
                   ⌜PermFlows a9 p'0⌝
                      ∗ read_write_cond a14 p'0 interp
                       ∧ ⌜if pwl a9
                          then region_state_pwl a7 a14
                          else region_state_nwl a7 a14 a10⌝) -∗ 
                interp_conf a7))%I.

  (* TODO: move to region.v *)
  Lemma region_addrs_empty b e:
    (e <= b)%a ->
    region_addrs b e = nil.
  Proof.
    intros. rewrite /region_addrs /region_size /=.
    replace (Z.to_nat (e - b)) with 0 by solve_addr.
    reflexivity.
  Qed.

  (* TODO: Move in monotone ? *)
  Lemma region_state_nwl_future W W' l l' p a:
    LocalityFlowsTo l' l ->
    (if pwlU p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if pwlU p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜region_state_nwl W' a l'⌝.
  Proof.
    intros Hlflows Hloc. iIntros "Hfuture %".
    destruct l'; simpl; iDestruct "Hfuture" as "%"; iPureIntro.
    - assert (l = Global) as -> by (destruct l; simpl in Hlflows; tauto).
      destruct (pwlU p) eqn:HpwlU; try congruence.
      eapply region_state_nwl_monotone_nl; eauto.
    - destruct (pwlU p).
      + subst l. left. eapply region_state_pwl_monotone; eauto.
      + generalize (region_state_nwl_monotone _ _ _ _ H a0).
        destruct l; auto.
  Qed.

  Lemma region_state_future W W' l l' p p' a:
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (if pwlU p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if pwlU p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜if pwlU p' then region_state_pwl W' a else region_state_nwl W' a l'⌝.
  Proof.
    intros Hpflows Hlflows Hloc. iIntros "Hfuture %".
    case_eq (pwlU p'); intros.
    - assert (pwlU p = true) as Hpwl.
      { destruct p, p'; simpl in H; try congruence; simpl in Hpflows; try tauto. }
      rewrite Hpwl in a0, Hloc. subst l.
      destruct l'; simpl in Hlflows; try tauto.
      simpl; iDestruct "Hfuture" as "%"; iPureIntro.
      eapply region_state_pwl_monotone; eauto.
    - iApply (region_state_nwl_future with "Hfuture"); eauto.
  Qed.

  (* TODO: Move somewhere ?*)
  Lemma PermFlowsToPermFlows p p':
    PermFlowsTo p p' <-> PermFlows p p'.
  Proof.
    rewrite /PermFlows; split; intros; auto.
    destruct (Is_true_reflect (PermFlowsTo p p')); auto.
  Qed.

  Lemma localityflowsto_futureworld l l' W W':
    LocalityFlowsTo l' l ->
    (@future_world Σ l' W W' -∗
     @future_world Σ l W W').
  Proof.
    intros; destruct l, l'; auto.
    rewrite /future_world; iIntros "%".
    iPureIntro. eapply related_sts_pub_priv_world; auto.
  Qed.

  Lemma promote_perm_flows_monotone p p':
    PermFlowsTo p p' ->
    PermFlowsTo (promote_perm p) (promote_perm p').
  Proof.
    destruct p, p'; simpl; tauto.
  Qed.

  Lemma promote_perm_flows p:
    PermFlowsTo p (promote_perm p).
  Proof.
    destruct p; simpl; tauto.
  Qed.

  Lemma promote_perm_pwl p:
    pwl (promote_perm p) = pwlU p.
  Proof.
    destruct p; reflexivity.
  Qed.

  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma interp_weakening W p p' l l' b b' e e' a a'
        (HU: if isU p then (a' <= a)%a else True):
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      LocalityFlowsTo l' l ->
      IH -∗
      (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
      (fixpoint interp1) W (inr (p', l', b', e', a')).
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (perm_eq_dec p' O); auto.
    destruct (perm_eq_dec p O).
    { subst p; destruct p'; simpl in Hp; try tauto. }
    destruct (perm_eq_dec p E); try congruence.
    iDestruct "HA" as "[#A [% #C]]".
    destruct (perm_eq_dec p' E).
    { (* p' = E *) subst p'. iAlways.
      assert (HisU: isU p = false).
      { destruct p; simpl in Hp; simpl; auto; tauto. }
      rewrite !HisU /enter_cond /interp_expr /=.
      iIntros (r W') "#Hfuture". iNext.
      iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      iSplitR; auto. rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iAlways. simpl. destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' Hflows) "[#X %]".
        assert (Hflows': PermFlows RX p'').
        { eapply PermFlows_trans; eauto.
          destruct p; simpl in *; auto; try congruence; try tauto; reflexivity. }
        iExists p''; iSplitR; eauto.
        repeat iSplitR; auto.
        iApply (region_state_nwl_future with "Hfuture"); eauto.
      - rewrite (region_addrs_empty b' e'); auto. solve_addr. }
    iSplit.
    { destruct (isU p') eqn:HisU'.
      { destruct (isU p) eqn:HisU.
        - destruct l; destruct l'; simpl.
          + destruct (Addr_le_dec b' e').
            { rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              assert (Hpfl2: PermFlows p' p'').
              { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
                eapply promote_perm_flows. }
              iExists p''; iSplitR; auto.
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              + assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
                rewrite HP in H0. iPureIntro. auto.
              + iApply (region_state_nwl_future W W Global Global); eauto.
                simpl. iPureIntro. eapply related_sts_priv_refl_world. }
            { rewrite (region_addrs_empty b' e'); auto. solve_addr. }
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              assert (Hpfl2: PermFlows p' p'').
              { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
                eapply promote_perm_flows. }
              iExists p''; iSplitR; auto.
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
                rewrite HP in H0. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Global Local); eauto.
                simpl. iPureIntro. eapply related_sts_pub_refl_world. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          + simpl in Hl. elim Hl.
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              assert (Hpfl2: PermFlows p' p'').
              { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
                eapply promote_perm_flows. }
              iExists p''; iSplitR; auto.
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
                rewrite HP in H0. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Local Local); eauto.
                simpl; iPureIntro. eapply related_sts_pub_refl_world. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
        - simpl. destruct l'; simpl.
          { destruct (Addr_le_dec b' e').
            + rewrite (isWithin_region_addrs_decomposition b' e' b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              assert (Hpfl2: PermFlows p' p'').
              { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
                eapply promote_perm_flows. }
              iExists p''; iSplitR; auto.
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
                rewrite HP in H0. iPureIntro. auto.
              * iApply (region_state_nwl_future W W l Global); eauto.
                simpl; iPureIntro. eapply related_sts_priv_refl_world.
            + rewrite (region_addrs_empty b' e'); auto. solve_addr. }
          { destruct (Addr_le_dec b' (min a' e')).
            + rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              assert (Hpfl2: PermFlows p' p'').
              { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
                eapply promote_perm_flows. }
              iExists p''; iSplitR; auto.
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
                rewrite HP in H0. iPureIntro. auto.
              * iApply (region_state_nwl_future W W l Local); eauto.
                simpl; iPureIntro; eapply related_sts_pub_refl_world.
            + rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } }
      assert (HisU: isU p = false).
      { destruct p', p; simpl in *; try tauto; try congruence. }
      rewrite !HisU. simpl.
      destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' Hflows) "[#X %]".
        assert (Hpfl: PermFlows (promote_perm p') p'').
        { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
        assert (Hpfl2: PermFlows p' p'').
        { eapply PermFlows_trans; eauto. eapply PermFlowsToPermFlows.
          eapply promote_perm_flows. }
        iExists p''; iSplitR; auto.
        repeat iSplit; auto.
        case_eq (pwlU p'); intros.
        + assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
          rewrite HP in H0. iPureIntro. auto.
        + iApply region_state_nwl_future; eauto.
          destruct l'; iPureIntro.
          * eapply related_sts_priv_refl_world.
          * eapply related_sts_pub_refl_world.
      - rewrite (region_addrs_empty b' e'); auto. solve_addr. }
    iSplit.
    { case_eq (pwlU p'); intros; auto.
      assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
      rewrite HP in H; subst l. destruct l'; simpl in Hl; try tauto. auto. }
    { case_eq (pwlU p'); intros; auto.
      - assert (pwlU p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
        rewrite HP in H; subst l. destruct l'; simpl in Hl; try tauto.
        destruct (isU p') eqn:HisU'; auto. simpl.
        destruct (isU p) eqn:HisU; simpl.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite HP. destruct (Addr_lt_dec (max b' a') (max b a)).
            { destruct (Addr_le_dec (max b a) e').
              - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
                rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr.
                rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr].
                assert (Heq: min a e = max b a) by solve_addr. rewrite Heq.
                rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". iFrame "#". 
                repeat iSplit;auto.
                + iApply (big_sepL_impl with "A2"); auto.
                  iAlways; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as (p'' Hflows) "[#X %]".
                  assert (Hpfl: PermFlows (promote_perm p') p'').
                  { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                  iExists _. iSplit;eauto. iFrame "#". iPureIntro. left; auto.
                + iApply (big_sepL_impl with "C2"); auto.
                  iAlways; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as (p'' Hflows) "[#X %]".
                  assert (Hpfl: PermFlows (promote_perm p') p'').
                  { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                  iExists _. iSplit;eauto. 
              - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iApply (big_sepL_impl with "A2"); auto.
                iAlways; iIntros (k x Hx) "Hw".
                iDestruct "Hw" as (p'' Hflows) "[#X %]".
                assert (Hpfl: PermFlows (promote_perm p') p'').
                { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                iExists _. iSplit;eauto. 
                iFrame "#". iPureIntro. left; auto. }
            { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
              iApply (big_sepL_impl with "C2"); auto.
              iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              iExists _. iSplit;eauto. 
            }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite HP. rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr.
            rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
            iApply (big_sepL_impl with "A2"); auto.
            iAlways; iIntros (k x Hx) "Hw".
            iDestruct "Hw" as (p'' Hflows) "[#X %]".
            assert (Hpfl: PermFlows (promote_perm p') p'').
            { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
            iExists _. iSplit;eauto. 
            iFrame "#". iPureIntro. left; auto.
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
      - destruct (isU p') eqn:HisU'; simpl; auto.
        destruct (isLocal l') eqn:Hl'; auto.
        destruct (isU p && isLocal l) eqn:X.
        + destruct (Addr_le_dec (max b' a') e').
          * destruct (Addr_lt_dec (max b' a') (max b a)).
            { destruct (Addr_le_dec (max b a) e').
              - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
                rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr.
                rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr].
                assert (Heq: min a e = max b a) by solve_addr. rewrite Heq.
                rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iSplitR.
                + iApply (big_sepL_impl with "A2"); auto.
                  iAlways; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as (p'' Hflows) "[#X %]".
                  assert (Hpfl: PermFlows (promote_perm p') p'').
                  { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                  iExists _. iSplit;eauto. 
                  iFrame "#". iPureIntro. destruct (pwlU p).
                  { left; auto. }
                  { destruct l; simpl in H1; auto.
                    - right; left; auto.
                    - destruct H1; [left|right;left]; auto. }
                + iSplitL; auto. iApply (big_sepL_impl with "C2"); auto.
                  iAlways; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as (p'' Hflows) "[#X %]".
                  assert (Hpfl: PermFlows (promote_perm p') p'').
                  { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                  iExists _. iSplit;eauto. iFrame "X". 
                  iPureIntro; 
                  destruct p; simpl in H1; auto; destruct H1; rewrite /region_state_U; auto.
              - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iApply (big_sepL_impl with "A2"); auto.
                iAlways; iIntros (k x Hx) "Hw".
                iDestruct "Hw" as (p'' Hflows) "[#X %]".
                assert (Hpfl: PermFlows (promote_perm p') p'').
                { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
                iExists _. iSplit;eauto.
                iFrame "#". iPureIntro. destruct (pwlU p).
                + left; auto.
                + destruct l; simpl in H1; auto.
                  * right; left; auto.
                  * destruct H1; [left|right;left]; auto. }
            { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". auto.
              iApply (big_sepL_impl with "C2"); auto.
              iAlways; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as (p'' Hflows) "[#X %]".
              assert (Hpfl: PermFlows (promote_perm p') p'').
              { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
              iExists _. iSplit;eauto. iFrame "#".
              iPureIntro; 
              destruct p; simpl in H1; auto; destruct H1; rewrite /region_state_U; auto. }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr.
            rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
            iApply (big_sepL_impl with "A2"); auto.
            iAlways; iIntros (k x Hx) "Hw".
            iDestruct "Hw" as (p'' Hflows) "[#X %]".
            assert (Hpfl: PermFlows (promote_perm p') p'').
            { eapply PermFlowsToPermFlows. eapply PermFlowsToTransitive; eauto. eapply promote_perm_flows_monotone; eauto. }
            iExists _. iSplit;eauto.
            iFrame "#". iPureIntro. destruct (pwlU p).
            { left; auto. }
            { destruct l; simpl in H1; auto.
              - right; left; auto.
              - destruct H1; [left|right;left]; auto. }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. }
  Qed.

End fundamental.
