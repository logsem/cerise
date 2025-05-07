From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import addr_reg region.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ lregs' p' b' e' a' v',
             full_map lregs'
          -∗ (∀ (r1 : RegName) (lv : LWord),
              ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
          -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
          -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (LCap p' b' e' a' v') -∗ interp_conf))%I.

  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma interp_weakening p p' b b' e e' a a' v:
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      IH -∗
      (fixpoint interp1) (LCap p b e a v) -∗
      (fixpoint interp1) (LCap p' b' e' a' v).
  Proof.
    intros HpnotE Hb He Hp. iIntros "#IH #HA".
    destruct (decide (b' <= e')%a).
    2: { rewrite !fixpoint_interp1_eq. destruct p'; try done
      ; try (by iClear "HA"; rewrite /= !finz_seq_between_empty;[|solve_addr]).
         iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)".
         iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
         iClear "HA". by rewrite !fixpoint_interp1_eq /= !finz_seq_between_empty;[|solve_addr].
    }
    destruct p'.
    - by rewrite !fixpoint_interp1_eq.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (Hreserved P) "(H1 & H2 & H3 & H4)"; iFrame "%". iExists P; iFrame.
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (Hreserved P) "(H1 & H2 & H3 & H4)"; iFrame "%". iExists P; iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      iApply (big_sepL_mono with "A2").
      iIntros (k y Hsome) "H". iDestruct "H" as (Hreserved P) "(H1 & H2 & H3 & H4)"; iFrame "%". iExists P; iFrame.
    - rewrite !fixpoint_interp1_eq. iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)".
      iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
      destruct p; inversion Hp; try contradiction.
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]"; iFrame "#".
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]".
        iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (Hreserved P) "(H1 & H2 & H3 & H4)"; iFrame "%". iExists P; iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
  Qed.

  Lemma safe_to_unseal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal (fixpoint interp1) b e -∗
    safe_to_unseal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal (fixpoint interp1) b e -∗
    safe_to_seal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_attest_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_attest b e -∗
    safe_to_attest b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_attest.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Ltac destruct_sealperm p :=
     let b := fresh "b" in
     let b1 := fresh "b1" in
     destruct p as [b b1]; destruct b, b1.
  Lemma permit_seal_flowsto p' p:
    SealPermFlowsTo p' p = true -> permit_seal p' = true → permit_seal p = true.
  Proof.  destruct_sealperm p; destruct_sealperm p'; done. Qed.
  Lemma permit_unseal_flowsto p' p:
    SealPermFlowsTo p' p = true -> permit_unseal p' = true → permit_unseal p = true.
  Proof.  destruct_sealperm p; destruct_sealperm p'; done. Qed.

  Lemma interp_weakening_ot p p' b b' e e' a a':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    SealPermFlowsTo p' p = true ->
    (fixpoint interp1) (LSealRange p b e a) -∗
    (fixpoint interp1) (LSealRange p' b' e' a').
  Proof.
    intros Hb He Hp. iIntros "#HA".
    rewrite !fixpoint_interp1_eq. cbn.
    destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
    all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as
          ->; auto | ]; iDestruct "HA" as "[Hs [ Hus Hattest] ]".
    all: iSplitL "Hs";
      [try iApply (safe_to_seal_weakening with "Hs") |]; auto.
    all: iSplitL "Hs"; [
        try iApply (safe_to_unseal_weakening with "Hus")|
      ]; auto.
    cbn.
    iApply (safe_to_attest_weakening with "Hattest"); auto.
  Qed.

End fundamental.
