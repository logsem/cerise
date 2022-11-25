From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Restrict.

Section fundamental.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MachineParameters}.
  
  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved p p' b e a :
    p <> E ->
    PermFlowsTo p' p = true →
    (□ ▷ (∀ i a0 a1 a2 a3 a4,
             full_map a0 i

          -∗ (∀ (r1 : RegName) v, ⌜(i, r1) ≠ (i, PC)⌝ → ⌜a0 !! (i, r1) = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[(i, PC):=WCap a1 a2 a3 a4]> a0)
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf i)) -∗
    (fixpoint interp1) (WCap p b e a) -∗
    (fixpoint interp1) (WCap p' b e a).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    iApply (interp_weakening with "IH HA"); eauto; try solve_addr.
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

  Lemma restrict_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r0 : Z + RegName)
        (i: CoreN) (P:D):
    ftlr_instr r p b e a w (Restrict dst r0) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    apply forall_and_distr in Hsome ; destruct Hsome as [Hsome Hnone].
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto.
      set_solver. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iNext.
      iIntros "_".
      iApply wp_value; auto. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro]. 
      iNext. 
      assert (HPCr0: match r0 with inl _ => True | inr r0 => PC <> r0 end).
      { destruct r0; auto.
        intro; subst r0. simplify_map_eq. }

      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert.
        simplify_map_eq by simplify_pair_eq.

        destruct (PermFlowsTo RX (decodePerm n)) eqn:Hpft.
        { assert (Hpg: (decodePerm n) = RX ∨ (decodePerm n) = RWX).
          { destruct (decodePerm n); simpl in Hpft; eauto; try discriminate. }
          iIntros "_".
          iApply ("IH" $! i r with "[%] [] [Hmap]");auto.
          iModIntro. rewrite !fixpoint_interp1_eq /=.
          destruct Hpg as [Heq | Heq];destruct Hp as [Heq' | Heq'];rewrite Heq Heq';try iFrame "Hinv".
          - iApply (big_sepL_mono with "Hinv").
            iIntros (k y _) "H". iDestruct "H" as (P') "(H1 & H2 & H3)". iExists P'. iFrame. 
          - rewrite Heq Heq' in H3. inversion H3. 
        }
        { iIntros "_".
          iApply (wp_bind (fill [SeqCtx]) _ _ (_,_)).
          iDestruct ((big_sepM_delete _ _ (i, PC)) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct (decodePerm n); simpl in Hpft; eauto; discriminate|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext ; iIntros "_".
          iApply wp_value.
          iIntros. discriminate. } }
      
      simplify_map_eq.
      iIntros "_".
      iApply ("IH" $! i (<[(i, dst):=_]> _) with "[%] [] [Hmap]"); eauto.
      - intros; simpl.
        split.
        repeat (rewrite lookup_insert_is_Some'; right); eauto.
        intros j Hneq. repeat (rewrite lookup_insert_ne ; simplify_pair_eq).
        by apply Hnone.
      - iIntros ( ri v Hri Hvs).
        destruct (decide ((i, ri) = (i, dst))).
        + simplify_map_eq by simplify_pair_eq.
          iDestruct ("Hreg" $! dst _ Hri H0) as "Hdst".
          iApply PermPairFlows_interp_preserved; eauto.
        + repeat rewrite lookup_insert_ne in Hvs; simplify_pair_eq ; auto.
          iApply "Hreg"; auto. all: by apply pair_neq_inv'.
      - iModIntro.
        simplify_map_eq by simplify_pair_eq.
        rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". }
  Qed.


End fundamental.
