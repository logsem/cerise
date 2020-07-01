From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_PromoteU.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma promote_interp W p g b e a (Hp: p <> E):
    IH -∗
    ((fixpoint interp1) W) (inr (p, g, b, e, a)) -∗
    ((fixpoint interp1) W) (inr (promote_perm p, g, b, min a e, a)).
  Proof.
    iIntros "#IH A". destruct (isU p) eqn:HisU.
    - rewrite !fixpoint_interp1_eq /=. destruct p; simpl in *; try congruence; auto.
      + destruct g.
        * (* iDestruct "A" as (p) "[% A]". *)
          (* iExists p; iSplit; [auto|]. *)
          iApply (big_sepL_submseteq with "A").
          destruct (Addr_le_dec b (min a e)).
          { rewrite (region_addrs_split b (min a e) e); [|solve_addr].
            eapply submseteq_inserts_r. auto. }
          { rewrite region_addrs_empty; [|solve_addr].
            eapply submseteq_nil_l. }
        * iDestruct "A" as "[A B]". auto.
      + destruct g; auto. iDestruct "A" as "[A B]". auto.
      + destruct g.
        * iDestruct "A" as "#A".
          iApply (big_sepL_submseteq with "A").
          destruct (Addr_le_dec b (min a e)).
          { rewrite (region_addrs_split b (min a e) e); [|solve_addr].
            eapply submseteq_inserts_r. auto. }
          { rewrite region_addrs_empty; [|solve_addr].
            eapply submseteq_nil_l. }
        * iDestruct "A" as "[#A #B]". auto.
      + destruct g; auto. iDestruct "A" as "[A B]". auto.
    - iApply (interp_weakening with "IH"); eauto; try solve_addr.
      + rewrite HisU; auto.
      + destruct p; simpl in HisU; simpl; auto; congruence.
      + destruct g; auto.
  Qed.

  Lemma promoteU_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName):
    ftlr_instr W r p p' g b e a w (PromoteU dst) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_PromoteU with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;congruence. }
      iApply ("IH" $! _ (<[dst:=inr (promote_perm p0, g0, b0, min a0 e0, a0)]> (<[PC:=_]> r)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
      { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri Hri). rewrite /(RegLocate _ ri) //; auto.
        destruct (reg_eq_dec dst ri).
        - subst ri. rewrite lookup_insert.
          destruct (reg_eq_dec dst PC); try congruence.
          iDestruct ("Hreg" $! dst n) as "H".
          rewrite lookup_insert_ne in H0; auto.
          rewrite /RegLocate H0. iApply (promote_interp with "IH H"); auto.
        - rewrite !lookup_insert_ne; auto.
          iApply "Hreg". auto. }
      { assert (x = p /\ x0 = g) as [-> ->].
        { destruct (reg_eq_dec PC dst).
          - subst dst. rewrite !lookup_insert in H0 H1. inv H0; inv H1.
            split; auto. destruct Hp as [-> | [-> | [-> ->] ] ]; auto.
          - rewrite lookup_insert_ne in H1; auto.
            rewrite lookup_insert in H1; inv H1; auto. }
        auto. }
      { iModIntro. destruct (reg_eq_dec PC dst).
        - subst dst. rewrite !lookup_insert in H0 H1. inv H1. inv H0.
          assert (promote_perm p0 = p0) as -> by (destruct Hp as [-> | [-> | [-> ->] ] ]; auto).
          rewrite (isWithin_region_addrs_decomposition x1 (min x3 e0) x1 e0); try solve_addr.
          rewrite !big_sepL_app. iDestruct "Hinv" as "[A1 [A2 A3]]". auto.
        - rewrite lookup_insert_ne in H1; auto. rewrite lookup_insert in H1.
          inv H1. auto. } }
  Qed.

 End fundamental.
