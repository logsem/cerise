From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import addr_reg region.
From cap_machine.rules Require Import rules_base rules_Subseg.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
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
      (□ ▷ (∀ a0 a1 a2 a3 a4,
             full_map a0
          -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜a0 !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[PC:=WCap a1 a2 a3 a4]> a0)
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf)) -∗
      (fixpoint interp1) (WCap p b e a) -∗
      (fixpoint interp1) (WCap p b' e' a).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    destruct p; reflexivity.
  Qed.
  
  Lemma subseg_case (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (dst : RegName) (r1 r2 : Z + RegName) (P:D):
    ftlr_instr r p b e a w (Subseg dst r1 r2) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #[Hread Hwrite] Hown Ha HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro;iNext].
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha HP]");[iExists w;iFrame|iModIntro;iNext].
      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert in HPC |- *. simplify_map_eq.
        iApply ("IH" $! r with "[%] [] [Hmap] [$Hown]"); try iClear "IH"; eauto.
        iModIntro. 
        generalize (isWithin_implies _ _ _ _ H4). intros [A B].
        destruct (Z_le_dec b'' e'').
        + rewrite !fixpoint_interp1_eq. destruct Hp as [-> | ->].
          - iSimpl in "Hinv". rewrite (isWithin_region_addrs_decomposition b'' e'' b0 e0); auto.
            iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
            iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
            iFrame "#".
          - iSimpl in "Hinv". rewrite (isWithin_region_addrs_decomposition b'' e'' b0 e0); auto.
            iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
            iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
            iFrame "#".
        + rewrite !fixpoint_interp1_eq /=.
          (destruct Hp as [-> | ->]; replace (region_addrs b'' e'') with (nil: list Addr);
          try rewrite big_sepL_nil); auto; 
          unfold region_addrs, region_size;rewrite Z_to_nat_nonpos //; lia. }
      { simplify_map_eq.
        iApply ("IH" $! (<[dst:=_]> _) with "[%] [] [Hmap] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri v Hri Hvs).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite lookup_insert in Hvs. inv Hvs.
            iDestruct ("Hreg" $! dst _ Hri H0) as "Hdst".
            generalize (isWithin_implies _ _ _ _ H4). intros [A B]. 
            iApply subseg_interp_preserved; eauto.
          + repeat rewrite lookup_insert_ne in Hvs; auto.
            iApply "Hreg"; auto.
        - rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iFrame "Hinv". } }
  Qed.

End fundamental.
