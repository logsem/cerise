From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import addr_reg region.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ a0 a1 a2 a3 a4,
             full_map a0
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a1, a2, a3, a4)]> a0)
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (inr (a1, a2, a3, a4)) -∗ interp_conf))%I.

 
  (* TODO: Move somewhere ?*)
  Lemma PermFlowsToPermFlows p p':
    PermFlowsTo p p' <-> PermFlows p p'.
  Proof.
    rewrite /PermFlows; split; intros; auto.
    destruct (Is_true_reflect (PermFlowsTo p p')); auto.
  Qed.

  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma interp_weakening p p' b b' e e' a a':
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      IH -∗
      (fixpoint interp1) (inr (p, b, e, a)) -∗
      (fixpoint interp1) (inr (p', b', e', a')).
  Proof.
    intros HpnotE Hb He Hp. iIntros "#IH #HA".
    destruct (decide (b' <= e')%a).
    2: { rewrite !fixpoint_interp1_eq. destruct p'; try done; try (by iClear "HA"; rewrite /= !region_addrs_empty;[|solve_addr]).
         iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)". iSplit;auto.
         iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
         iClear "HA". by rewrite !fixpoint_interp1_eq /= !region_addrs_empty;[|solve_addr]. 
    }  
    destruct p'.
    - rewrite !fixpoint_interp1_eq. done.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. 
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      iApply (big_sepL_mono with "A2").
      iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq. iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)". iSplit;auto.
      iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
      destruct p; inversion Hp; try contradiction.
      + rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]"; iFrame "#".
      + rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]". 
        iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. 
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_region_addrs_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
  Qed.
  

End fundamental.
