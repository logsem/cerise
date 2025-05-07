From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
  Context `{reservedaddresses : ReservedAddresses}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Seal_failure  (lregs: LReg) (dst: RegName) (src1 src2: RegName) : LReg → Prop :=
  | Seal_fail_sealr lw :
      lregs !! src1 = Some lw →
      is_sealrL lw = false →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_sealb lw :
      lregs !! src2 = Some lw →
      is_sealbL lw = false →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_bounds lw p b e a sb:
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      (permit_seal p = false ∨ withinBounds b e a = false) →
      Seal_failure lregs dst src1 src2 lregs
  | Seal_fail_incrPC p b e a sb :
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementLPC (<[ dst := LWSealed a sb ]> lregs) = None →
      Seal_failure lregs dst src1 src2 lregs.

  Inductive Seal_spec (lregs: LReg) (dst: RegName) (src1 src2: RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Seal_spec_success p b e a sb:
      lregs !! src1 = Some (LSealRange p b e a) →
      lregs !! src2 = Some (LWSealable sb) →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementLPC (<[ dst := LWSealed a sb ]> lregs) = Some lregs' →
      Seal_spec lregs dst src1 src2 lregs' NextIV
  | Seal_spec_failure :
      Seal_failure lregs dst src1 src2 lregs' →
      Seal_spec lregs dst src1 src2 lregs' FailedV.


  Definition exec_optL_Seal
    (lregs : LReg) (dst src_key src_val: RegName) : option LReg :=
    key ← lregs !! src_key;
    val ← lregs !! src_val;
    match key,val with
    | LSealRange p b e a, LWSealable sb =>
      if permit_seal p && withinBounds b e a
      then
        lregs' ← incrementLPC ( <[dst := (LWSealed a sb) ]> lregs) ;
        Some lregs'
      else None
    | _, _ => None
    end.

  Lemma wp_Seal Ep pc_p pc_b pc_e pc_a pc_v lw dst src_key src_val lregs :
    decodeInstrWL lw = Seal dst src_key src_val ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Seal dst src_key src_val) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Seal_spec lregs dst src_key src_val lregs' retv ⌝ ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    cbn in Dregs.
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hmap Hφ]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Seal lregs dst src_key src_val)).

    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (key) "Hσ %Hlrs_key %Hrs_key".

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (val) "Hσ %Hlrs_val %Hrs_val".

    destruct (is_sealrL key) eqn:Hkey; cycle 1.
    {
      destruct_lword key; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
      all: iPureIntro; econstructor; by eapply Seal_fail_sealr.
    }
    destruct_lword key; cbn in * ; simplify_eq.

    destruct (is_sealbL val) eqn:Hval; cycle 1.
    {
      destruct_lword val; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      all: iApply ("Hφ" with "[$Hpc_a $Hregs]").
      all: iPureIntro; econstructor; by eapply Seal_fail_sealb.
    }
    destruct val; cbn in * ; simplify_eq.

    destruct (decide (permit_seal p && withinBounds b e a = true)) as [Hseal|Hseal]
    ; [|apply not_true_is_false in Hseal] ; rewrite Hseal ;cycle 1;cbn.
    {
      apply andb_false_iff in Hseal.
      iModIntro.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro; constructor; by eapply Seal_fail_bounds.
    }

    apply andb_true_iff in Hseal; destruct Hseal as [ Hseal Hinbounds ].
    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LWSealed a sb) with "Hσ") as "Hσ".
    { now set_solver. }
    { intros.
      eapply seal_from_argumentL ; eauto.
    }


    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (k1 := fun x => Some x)).
    iApply wp_opt2_eqn_both.
    iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := LWSealed a sb]> lregs)).
    { now rewrite elem_of_dom (lookup_insert_dec HPC). }
    iFrame "Hσ".
    iSplit; cbn.
    - iIntros "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro; constructor ; by eapply Seal_fail_incrPC .
    - iIntros (lrt' rs') "Hσ %Hlis %His".
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      by eapply Seal_spec_success.
  Qed.

  (* after pruning impossible or impractical options, 5 wp rules remain *)

  Lemma wp_seal_success E pc_p pc_b pc_e pc_a pc_v lw lw' dst r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal dst r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ lw'
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWSealed a sb
          ∗ r1 ↦ᵣ LSealRange p b e a
          ∗ r2 ↦ᵣ LWSealable sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r1 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal r1 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LWSealed a sb
          ∗ r2 ↦ᵣ LWSealable sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r2 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a sb pc_a' :
    decodeInstrWL lw = Seal r2 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LWSealable sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LSealRange p b e a
          ∗ r2 ↦ᵣ LWSealed a sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ r2 PC) // insert_insert (insert_commute _ r1 r2) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  (* the 2 rules where r2=PC (and d=r1 or d≠r2) are also admissible *)

  Lemma wp_seal_PC E pc_p pc_b pc_e pc_a pc_v lw lw' dst r1 p b e a pc_a' :
    decodeInstrWL lw = Seal dst r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ lw'
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWSealed a (LSCap pc_p pc_b pc_e pc_a pc_v)
          ∗ r1 ↦ᵣ LSealRange p b e a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr1") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ dst PC) // insert_insert (insert_commute _ dst r1) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

 Lemma wp_seal_PC_eq E pc_p pc_b pc_e pc_a pc_v lw lw' r1 p b e a pc_a' :
    decodeInstrWL lw = Seal r1 r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LWSealed a (LSCap pc_p pc_b pc_e pc_a pc_v)
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ r1 PC) // !insert_insert.
      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
      match goal with H: _ ∨ _ |- _ => destruct H end.
      all: congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_nosb_r2 E pc_p pc_b pc_e pc_a pc_v lw r1 r2 p b e a lw2 pc_a' :
    decodeInstrWL lw = Seal r2 r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealbL lw2 = false →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ LSealRange p b e a
          ∗ ▷ r2 ↦ᵣ lw2 }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hfalse ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; last by iApply "Hφ".
    { by simplify_map_eq. }
  Qed.

End cap_lang_rules.
