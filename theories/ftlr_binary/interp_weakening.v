From cap_machine Require Export logrel_binary.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary region.
From cap_machine Require Import addr_reg.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ (a0 : Reg * Reg) (a1 : Perm) (a2 a3 a4 : Addr),
             full_map a0
                      -∗ (∀ (r0 : RegName) v1 v2, (⌜r0 ≠ PC⌝  → ⌜a0.1 !! r0 = Some v1⌝ → ⌜a0.2 !! r0 = Some v2⌝ → interp (v1, v2)))
                      -∗ registers_mapsto (<[PC:=WCap a1 a2 a3 a4]> a0.1)
                      -∗ spec_registers_mapsto (<[PC:=WCap a1 a2 a3 a4]> a0.2)
                      -∗ na_own logrel_nais ⊤
                      -∗ ⤇ Seq (Instr Executable)
                      -∗ □ spec_ctx
                      -∗ □ interp (WCap a1 a2 a3 a4, WCap a1 a2 a3 a4) -∗ interp_conf))%I.

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
      spec_ctx -∗
      (fixpoint interp1) (WCap p b e a, WCap p b e a) -∗
      (fixpoint interp1) (WCap p' b' e' a', WCap p' b' e' a').
  Proof.
    intros HpnotE Hb He Hp. iIntros "#IH #Hspec #HA".
    destruct (decide (b' <= e')%a).
    2: { rewrite !fixpoint_interp1_eq. destruct p'; try done; try (by iClear "HA"; rewrite /= !finz_seq_between_empty; try solve_addr).
         iSplit; auto. iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hsregs & Hna & Hs)". iSplit;auto.
         iApply ("IH" with "Hfull Hreg Hregs Hsregs Hna Hs"); auto. iModIntro.
         iClear "HA". by rewrite !fixpoint_interp1_eq /= !finz_seq_between_empty; try solve_addr.
    }
    destruct p'.
    - rewrite !fixpoint_interp1_eq. done.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]";iFrame "#";auto.
      + iSplitR; auto. iApply (big_sepL_mono with "A3").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
      + iSplitR; auto. iApply (big_sepL_mono with "A3").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]";iSplitR; auto; iFrame "#".
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]";iSplitR; auto; iFrame "#".
      iApply (big_sepL_mono with "A3").
      iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq. iSplitR; auto. iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hsregs & Hna & Hs)". iSplit;auto.
      iApply ("IH" with "Hfull Hreg Hregs Hsregs Hna Hs"); auto. iModIntro.
      destruct p; inversion Hp; try contradiction.
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]"; iFrame "#". auto.
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]".
        iSplitR; auto. iApply (big_sepL_mono with "A3").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 [A3 A4]]]";iFrame "#". auto.
  Qed.

End fundamental.
