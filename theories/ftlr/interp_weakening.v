From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone region.
From cap_machine Require Import addr_reg.

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

  Lemma interp1_eq interp (W: WORLD) p l b e a:
    ((interp1 interp W (inr (p, l, b, e, a))) ≡
             (if perm_eq_dec p O then True else
             if perm_eq_dec p E then □ enter_cond W b e a l interp else
               (∃ p', ⌜PermFlows p p'⌝ ∗
                ([∗ list] a ∈ (region_addrs b e),
                 (read_write_cond a p' interp) ∧
                 ⌜if pwl p then region_state_pwl W a else region_state_nwl W a l⌝ ∧ ⌜region_std W a⌝) ∗
                (□ match p with RX | RWX | RWLX => exec_cond W b e l p interp | _ => True end) ∗
                (⌜if pwl p then l = Local else True⌝)))%I).
  Proof.
    iSplit.
    { iIntros "HA".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      destruct p; simpl; try congruence; auto; try (iDestruct "HA" as (p') "[HA HB]"; eauto; fail); try (iDestruct "HA" as (p') "(HA & HB & HC)"; eauto; fail); destruct l; auto.
      - iDestruct "HA" as (p') "[HA HB]"; eauto.
      - iDestruct "HA" as (p') "[HA [HB HC]]"; eauto. }
    { iIntros "A".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      iDestruct "A" as (p') "(A & B & C & %)".
      destruct p; simpl in *; try congruence; subst; eauto. }
  Qed.

  Definition IH: iProp Σ :=
    (□ ▷ (∀ (a7 : leibnizO (STS * STS)) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
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

  (* TODO: Move somewhere *)
  Lemma region_std_future W W' l x:
    (@future_world Σ l W W' -∗
    ⌜region_std W x⌝ -∗
    ⌜region_std W' x⌝)%I.
  Proof.
    iIntros "A B"; rewrite !/region_std.
    destruct l; simpl; iDestruct "A" as "%"; iDestruct "B" as "%".
    - iPureIntro; eapply related_sts_rel_std; eauto.
    - iPureIntro; eapply rel_is_std_i_monotone; eauto.
  Qed.

  (* TODO: Move in monotone ? *)
  Lemma region_state_nwl_future W W' l l' p a:
    LocalityFlowsTo l' l ->
    (if pwl p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜region_std W a⌝ -∗
    ⌜if pwl p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜region_state_nwl W' a l'⌝.
  Proof.
    intros Hlflows Hloc. iIntros "Hfuture % %".
    destruct l'; simpl; iDestruct "Hfuture" as "%"; iPureIntro.
    - assert (l = Global) as -> by (destruct l; simpl in Hlflows; tauto).
      destruct (pwl p); try congruence.
      eapply region_state_nwl_monotone_nl; eauto.
    - destruct (pwl p).
      + subst l. left. eapply region_state_pwl_monotone; eauto.
      + generalize (region_state_nwl_monotone _ _ _ _ a0 H3 a1).
        destruct l; auto.
  Qed.

  Lemma region_state_future W W' l l' p p' a:
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (if pwl p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜region_std W a⌝ -∗
    ⌜if pwl p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜if pwl p' then region_state_pwl W' a else region_state_nwl W' a l'⌝.
  Proof.
    intros Hpflows Hlflows Hloc. iIntros "Hfuture % %".
    case_eq (pwl p'); intros.
    - assert (pwl p = true) as Hpwl.
      { destruct p, p'; simpl in H3; try congruence; simpl in Hpflows; try tauto. }
      rewrite Hpwl in a1, Hloc. subst l.
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

  (* TODO: move to sts.v ?*)
  Lemma related_sts_pub_world_refl W:
    related_sts_pub_world W W.
  Proof.
    split; eapply related_sts_pub_refl.
  Qed.

  (* TODO: move to sts.v ?*)
  Lemma related_sts_priv_world_refl W:
    related_sts_priv_world W W.
  Proof.
    split; eapply related_sts_priv_refl.
  Qed.

  Lemma interp_weakening W p p' l l' b b' e e' a a':
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
    iDestruct "HA" as (p'') "[% [#A [#B %]]]".
    destruct (perm_eq_dec p' E).
    { (* p' = E *) subst p'. iAlways.
      rewrite /enter_cond /interp_expr /=.
      iIntros (r W') "#Hfuture". iNext.
      iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      iSplitR; auto. rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iAlways. simpl. assert (Hflows: PermFlows RX p'').
      { eapply PermFlows_trans; eauto.
        destruct p; simpl in *; auto; try congruence; try tauto; reflexivity. }
      iExists p''; iSplitR; eauto. destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "[#X [% %]]".
        repeat iSplitR; auto.
        + iApply (region_state_nwl_future with "Hfuture"); eauto.
        + iApply (region_std_future with "Hfuture"); eauto.
      - rewrite (region_addrs_empty b' e'); auto. solve_addr. }
    assert (Hpfl: PermFlows p' p'') by (eapply PermFlows_trans; eauto; eapply PermFlowsToPermFlows; eauto).
    iExists p''; iSplitR; auto. iSplit.
    { destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k x Hx) "[#X [% %]]".
        repeat iSplit; auto.
        case_eq (pwl p'); intros.
        + assert (pwl p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
          rewrite HP in H5. iPureIntro. auto.
        + iApply region_state_nwl_future; eauto.
          destruct l'; iPureIntro.
          * eapply related_sts_priv_world_refl.
          * eapply related_sts_pub_world_refl.
      - rewrite (region_addrs_empty b' e'); auto. solve_addr. }
    iSplit.
    { iModIntro. assert ((p' = RX \/ p' = RWX \/ p' = RWLX) \/ (p' <> RX /\ p' <> RWX /\ p' <> RWLX)) as Hp'.
      { destruct p'; auto; right; repeat split; auto; try congruence. }
      destruct Hp' as [Hp' | Hp'].
      - assert (Hpis: p = RX \/ p = RWX \/ p = RWLX).
        { destruct Hp' as [-> | [-> | ->] ]; destruct p; simpl in Hp; try tauto. }
        iAssert (exec_cond W b' e' l' p' (fixpoint interp1)) as "C".
        { (* iAssert (exec_cond W b e l p (fixpoint interp1)) as "C".
          { destruct Hpis as [-> | [-> | ->] ]; auto. } *)
          rewrite /exec_cond /interp_expr /=. iClear "B".
          iIntros (x r W' Hin) " #Hfuture". iNext.
          iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
          iSplitR; auto. rewrite /interp_conf.
          iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
          - destruct Hp' as [-> | [-> | ->] ]; auto. iPureIntro; right; right.
            split; auto.
            destruct l'; auto. destruct p; simpl in Hp; try tauto.
            simpl in H4. subst l; simpl in Hl. tauto.
          - iAlways. iExists p''; iSplit; auto. destruct (Addr_le_dec b' e').
            + rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iAlways; iIntros (k y Hy) "[#Y [% %]]".
              repeat iSplitR; auto.
              * iApply (region_state_future with "Hfuture"); eauto.
              * iApply (region_std_future with "Hfuture"); eauto.
            + rewrite (region_addrs_empty b' e'); auto. solve_addr. }
        destruct p'; auto.
      - destruct Hp' as [Hp1 [Hp2 Hp3] ].
        destruct p'; auto; try congruence. }
    case_eq (pwl p'); intros; auto.
    assert (pwl p = true) as HP by (destruct p, p'; simpl in Hp; inv Hp; simpl in *; auto; try congruence).
    rewrite HP in H4; subst l. destruct l'; simpl in Hl; auto.
  Qed.

End fundamental.