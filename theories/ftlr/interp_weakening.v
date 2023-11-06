From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import addr_reg region register_tactics.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH : iProp Σ :=
    (□ ▷ (∀ regs' p' b' e' a' widc',
             full_map regs'
          -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r ≠ idc⌝ → ⌜regs' !! r = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[idc:=widc']> (<[PC:=WCap p' b' e' a']> regs'))
          -∗ na_own logrel_nais ⊤
          -∗ □ (fixpoint interp1) (WCap p' b' e' a')
          -∗ □ (fixpoint interp1) widc'
          -∗ interp_conf))%I.


  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma interp_weakening p p' b b' e e' a a' widc:
      p <> E ->
      p <> IE ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      IH -∗
      (fixpoint interp1) widc -∗
      (fixpoint interp1) (WCap p b e a) -∗
      (fixpoint interp1) (WCap p' b' e' a').
  Proof.
    intros HpnotE HpnotIE Hb He Hp. iIntros "#IH #Hidc #HA".
    destruct (decide (b' <= e')%a).
    2: { rewrite !fixpoint_interp1_eq. destruct p'; try done
      ; try (by iClear "HA"; rewrite /= !finz_seq_between_empty;[|solve_addr]).
         + (* E-cap *)
           iIntros (r). iNext; iModIntro.
           iIntros (w') "#Hw'".
           iIntros "([Hfull Hreg] & Hregs & Hna)".
           iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
           iClear "HA". by rewrite !fixpoint_interp1_eq /= !finz_seq_between_empty;[|solve_addr].
         + (* IE-cap *)
           iIntros "[%Hwb _]".
           exfalso; apply n.
           apply Is_true_true_1 in Hwb.
           rewrite withinBounds_true_iff in Hwb.
           solve_addr.
    }
    destruct p'.
    - rewrite !fixpoint_interp1_eq; done.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3 & H4)". iExists P. iFrame.
      + iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3 & H4)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
    - rewrite !fixpoint_interp1_eq.
      destruct p;inversion Hp;
      (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]);
      rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#".
      iApply (big_sepL_mono with "A2").
      iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3 & H4)". iExists P. iFrame.
    - rewrite !fixpoint_interp1_eq. iIntros (r). iNext. iModIntro.
      iIntros (w') "#Hw'".
      iIntros "([Hfull Hreg] & Hregs & Hna)".
      iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro.
      destruct p; inversion Hp; try contradiction.
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]"; iFrame "#".
      + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
        rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]".
        iApply (big_sepL_mono with "A2").
        iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3 & H4)". iExists P. iFrame.
    - rewrite !(fixpoint_interp1_eq (WCap IE _ _ _)).
      iIntros "[%Hwb %Hwb']".
      apply Is_true_true_1 in Hwb, Hwb'.
      rewrite withinBounds_true_iff in Hwb; rewrite withinBounds_true_iff in Hwb'.
      assert (readAllowed p).
      { destruct p; inversion Hp; try contradiction; auto. }
      iDestruct (read_allowed_inv a' with "HA")
        as (Pa) "[Hinv_a [Hpers_Pa [Hconds_a _]] ]"; auto ; first solve_addr.
      iDestruct (read_allowed_inv (a'^+1)%a with "HA")
        as (Pa') "[Hinv_a' [Hpers_Pa' [Hconds_a' _]] ]"; auto ; first solve_addr.

      iExists Pa, Pa'; iFrame "#".
      iIntros (w1 w2 regs). iNext; iModIntro.
      iIntros "[HPw1 HPw2]".
      iAssert (interp w1)%I as "#Hw1"; first (by iApply "Hconds_a").
      iAssert (interp w2)%I as "#Hw2"; first (by iApply "Hconds_a'").
      iIntros "([Hfull Hreg] & Hregs & Hna)".

      (* Needed because IH disallows non-capability values *)
      destruct w1 as [ | [p1 b1 e1 a1 | ] | ]; cycle 1.
      iApply ("IH" with "Hfull Hreg Hregs Hna"); auto.

      all: rewrite /registers_mapsto; iExtract "Hregs" PC as "HPC".
      all: iApply (wp_bind (fill [SeqCtx]));
        iApply (wp_notCorrectPC with "HPC")
      ; [intros HFalse; inversion HFalse| ].
      all: repeat iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto.
      all: iNext; iIntros "_".
      all: iApply wp_value.
      all: iIntros; discriminate.
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
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Qed.


End fundamental.
