From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import addr_reg region.
From cap_machine.rules Require Import rules_base rules_Subseg.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma within_in_range:
    forall a b b' e e',
      (b <= b')%a ->
      (e' <= e)%a ->
      in_range a b' e' ->
      in_range a b e.
  Proof.
    intros * ? ? [? ?]. split; solve_addr.
  Qed.

  Lemma subseg_interp_preserved p b b' e e' a :
      p <> E ->

      (b <= b')%a ->
      (e' <= e)%a ->
      (□ ▷ (∀ i a0 a1 a2 a3 a4,
             full_map a0 i
          -∗ (∀ (j: CoreN) (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜a0 !! (j, r1) = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[(i, PC):=WCap a1 a2 a3 a4]> a0)
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf i)) -∗
      (fixpoint interp1) (WCap p b e a) -∗
      (fixpoint interp1) (WCap p b' e' a).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    destruct p; reflexivity.
  Qed.
  
  Lemma subseg_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r1 r2 : Z + RegName)
        (i:CoreN ) (P:D):
    ftlr_instr r p b e a w (Subseg dst r1 r2) i P.
  Proof.
    intros Hp Hsome i' Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /regs_of_core /subseteq /map_subseteq /set_subseteq_instance. intros rr ?.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. set_solver. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro;iNext].
      iApply wp_value; auto. }
    {
      apply incrementPC_Some_inv in H5 as (p''&b''&e''&a''& ? & HPC & Z & Hregs').
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro;iNext].
      destruct (reg_eq_dec PC dst).
      { subst dst. repeat (rewrite insert_insert in HPC). simplify_map_eq by simplify_pair_eq.
        rewrite !insert_insert.
        iApply ("IH" $! i r with "[%] [] [Hmap]"); try iClear "IH"; eauto.
        iModIntro.
        generalize (isWithin_implies _ _ _ _ H4). intros [A B].
        destruct (Z_le_dec b'' e'').
        + rewrite !fixpoint_interp1_eq. destruct Hp as [-> | ->].
        - iSimpl in "Hinv". rewrite (isWithin_finz_seq_between_decomposition b'' e'' b0 e0); auto.
          iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
          iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
          iFrame "#".
        - iSimpl in "Hinv". rewrite (isWithin_finz_seq_between_decomposition b'' e'' b0 e0); auto.
          iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
          iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
          iFrame "#".
          + rewrite !fixpoint_interp1_eq /=.
            (destruct Hp as [-> | ->]; replace (finz.seq_between b'' e'') with (nil: list Addr);
             try rewrite big_sepL_nil); auto;
            unfold finz.seq_between, finz.dist;rewrite Z_to_nat_nonpos //; lia. }
      { simplify_map_eq.
        iApply ("IH" $! i (<[(i, dst):=_]> _) with "[%] [] [Hmap]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); simplify_pair_eq ; auto; right; split ; auto; simplify_pair_eq.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); simplify_pair_eq ; auto; right; split ; auto; simplify_pair_eq.
        - iIntros (j ri v Hri Hvs).
          destruct (decide ((j, ri) = (i, dst))).
          + simplify_pair_eq. rewrite lookup_insert in Hvs. inv Hvs.
            simplify_map_eq by simplify_pair_eq.
            iDestruct ("Hreg" $! i dst _ Hri H0) as "Hdst".
            generalize (isWithin_implies _ _ _ _ H4). intros [A B].
            iApply subseg_interp_preserved; eauto.
          + repeat rewrite lookup_insert_ne in Hvs; auto ; simplify_pair_eq.
            iApply "Hreg"; auto.
        - rewrite !fixpoint_interp1_eq /=.
            simplify_map_eq by simplify_pair_eq.
          destruct Hp as [-> | ->]; try iFrame "Hinv". } }
  Qed.

End fundamental.
