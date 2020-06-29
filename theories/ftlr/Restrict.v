From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone interp_weakening.
From cap_machine.rules Require Import rules_Restrict.

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

  Lemma locality_eq_dec:
    forall (l1 l2: Locality), {l1 = l2} + {l1 <> l2}.
  Proof.
    destruct l1, l2; auto.
  Qed.

  Lemma PermPairFlows_interp_preserved W p p' l l' b e a :
    p <> E ->
    PermPairFlowsTo (p', l') (p, l) = true →
    □ ▷ (∀ (a7 : WORLD) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
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
                    ⌜PermFlows a9 p'0⌝ ∗
                       read_write_cond a14 p'0 interp
                       ∧ ⌜if pwl a9
                          then region_state_pwl a7 a14
                          else region_state_nwl a7 a14 a10⌝) -∗ 
                interp_conf a7) -∗
    (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
    (fixpoint interp1) W (inr (p', l', b, e, a)).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)).
    simpl in H, H0. iApply (interp_weakening with "IH HA"); eauto; try solve_addr.
    - destruct (isU p); solve_addr.
    - rewrite <- H. auto.
    - rewrite <- H0. auto.
  Qed.

  Lemma match_perm_with_E_rewrite:
    forall (A: Type) p (a1 a2: A),
      match p with
      | E => a1
      | _ => a2
      end = if (perm_eq_dec p E) then a1 else a2.
  Proof.
    intros. destruct (perm_eq_dec p E); destruct p; auto; congruence.
  Qed.

  Lemma restrict_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName):
    ftlr_instr W r p p' g b e a w (Restrict dst r0) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.

      assert (HPCr0: match r0 with inl _ => True | inr r0 => PC <> r0 end).
      { destruct r0; auto.
        intro; subst r0.
        rewrite /= lookup_insert in H1. inv H1. }

      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert.
        repeat rewrite insert_insert in HPC.
        rewrite lookup_insert in HPC. inv HPC.
        rewrite lookup_insert in H. inv H.
        rewrite H4 in H2. iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[..|specialize (Hnotstatic g)];contradiction. }
        destruct (PermFlowsTo RX p'') eqn:Hpft.
        { assert (Hpg: p'' = RX ∨ p'' = RWX ∨ p'' = RWLX ∧ g'' = Local).
          { destruct p''; simpl in Hpft; eauto; try discriminate.
            destruct (andb_true_eq _ _ ltac:(symmetry in H2;exact H2)).
            simpl in H2, H3. destruct p0; simpl in H2; try discriminate.
            destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; try discriminate.
            subst g0; destruct g''; simpl in H3; auto; discriminate. }
          rewrite H4. iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
          iAlways. iApply (big_sepL_mono with "Hinv"); simpl; intros.
          iIntros "H". iDestruct "H" as (? ?) "[H %]". iExists H3. iSplitR; auto.
          { destruct (andb_true_eq _ _ ltac:(symmetry in H2; exact H2)).
            iPureIntro. eapply PermFlows_trans with p0; auto. symmetry; exact H7. }
          iSplitL;auto. 
          iPureIntro. 
          destruct (andb_true_eq _ _ ltac:(symmetry in H2; exact H2)); simpl in *.
          destruct (locality_eq_dec g'' g0).
          * subst g0. destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; destruct Hpg as [Hp' | [ Hp' | [Hp' Hg' ] ] ]; subst; simpl in *; simpl; try congruence; auto.
          * destruct g''; destruct g0; simpl in *; try congruence.
            destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; destruct Hpg as [Hp' | [ Hp' | [Hp' Hg' ] ] ]; subst; simpl in *; simpl; try congruence; auto. }
        { iApply (wp_bind (fill [SeqCtx])).
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
         rewrite H4.
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; eauto; discriminate|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. } }

      rewrite lookup_insert_ne in HPC; auto.
      rewrite lookup_insert in HPC. inv HPC.
      rewrite lookup_insert_ne in H; auto.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[..|specialize (Hnotstatic g)];contradiction. }
      iApply ("IH" $! _ (<[dst:=_]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
      - intros; simpl. repeat (rewrite lookup_insert_is_Some'; right); eauto.
      - iIntros (ri Hri). rewrite /RegLocate.
        destruct (decide (ri = dst)).
        + subst ri. rewrite lookup_insert.
          destruct (decodePermPair n) as (p1 & g1).
          iDestruct ("Hreg" $! dst Hri) as "Hdst".
          rewrite H. iApply PermPairFlows_interp_preserved; eauto.
        + repeat rewrite lookup_insert_ne; auto.
          iApply "Hreg"; auto. }
  Qed.

End fundamental.
