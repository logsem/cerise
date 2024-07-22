From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import addr_reg region proofmode register_tactics.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ a0 a1 a2 a3 a4,
             full_map a0
          -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜a0 !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[PC:=WCap a1 a2 a3 a4]> a0)
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf))%I.

  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma interp_weakening p p' b b' e e' a a':
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      IH -∗
      (fixpoint interp1) (WCap p b e a) -∗
      (fixpoint interp1) (WCap p' b' e' a').
  Proof.
    intros Hb He Hp. iIntros "#IH #HA".
    destruct (decide (b' <= e')%a).
    2: { rewrite !fixpoint_interp1_eq. destruct p'; try done; try (by iClear "HA"; rewrite /= !finz_seq_between_empty;[|solve_addr]).
    }
    destruct p'.
    - rewrite !fixpoint_interp1_eq. done.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      iApply (big_sepL_mono with "A2").
      iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
  Qed.

  Lemma sealing_preserves_interp sb p0 b0 e0 a0:
        permit_seal p0 = true →
        withinBounds b0 e0 a0 = true →
        IH -∗
        fixpoint interp1 (WSealable sb) -∗
        fixpoint interp1 (WSealRange p0 b0 e0 a0) -∗
        fixpoint interp1 (WSealed a0 sb).
  Proof.
    iIntros (Hpseal Hwb) "#IH #HVsb #HVsr".
    rewrite (fixpoint_interp1_eq (WSealRange _ _ _ _)) (fixpoint_interp1_eq (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[% [HsealP HWcond]]".
    iExists P.
    repeat iSplitR; auto.
    by iApply "HWcond".
    destruct (decide (a0 = otype_sentry)) as [Hot|Hot] ; subst; last done.
    iIntros (r).
    iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)".
    destruct sb as [p b e a |]; cycle 1.
    + (* PC contains sealrange, it is trivially safe *)
      wp_instr.
      iEval (rewrite /registers_mapsto) in "Hregs".
      iExtract "Hregs" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto; first (intro Hcontra; inversion Hcontra).
      iNext ; iIntros "HPC".
      wp_pure; wp_end.
      iIntros "%" ; done.
    + iApply ("IH" with "Hfull Hreg Hregs Hna"); auto.
  Qed.

  Lemma sealing_preserves_interp_sentry sb:
        IH -∗
        seal_pred otype_sentry (fixpoint interp1) -∗
        fixpoint interp1 (WSealable sb) -∗
        fixpoint interp1 (WSealed otype_sentry sb).
  Proof.
    iIntros "#IH #Hsentry_pred #HVsb".
    rewrite (fixpoint_interp1_eq (WSealed _ _)) /= /interp_sb.
    iExists (fixpoint interp1).
    iSplit.
    { iPureIntro; intro; apply interp_persistent. }
    iSplit; first done.
    iSplit; first done.
    iIntros (r).
    iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)".
    destruct sb as [p b e a |]; cycle 1.
    + (* PC contains sealrange, it is trivially safe *)
      wp_instr.
      iEval (rewrite /registers_mapsto) in "Hregs".
      iExtract "Hregs" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto; first (intro Hcontra; inversion Hcontra).
      iNext ; iIntros "HPC".
      wp_pure; wp_end.
      iIntros "%" ; done.
    + iApply ("IH" with "Hfull Hreg Hregs Hna"); auto.
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
    (fixpoint interp1) (WSealRange p b e a) -∗
    (fixpoint interp1) (WSealRange p' b' e' a').
  Proof.
  intros Hb He Hp. iIntros "#HA".
  rewrite !fixpoint_interp1_eq. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as
        ->; auto | ]; iDestruct "HA" as "[Hs [Hus Hj]]".
  all: destruct (permit_call b' e') as [Hjump|Hjump].
  all: iSplitL "Hs"; [try iApply (safe_to_seal_weakening with "Hs") | iSplitL "Hus" ; try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  all: destruct (permit_call b e) as [Hjump'|Hjump']; solve_addr.
  Qed.

End fundamental.
