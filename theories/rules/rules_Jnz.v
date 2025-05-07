From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Jnz_spec (lregs: LReg) (dst src: RegName) : LReg → cap_lang.val → Prop :=
  | Jnz_spec_failure lw:
      lregs !! src = Some lw →
      nonZeroL lw = false →
      incrementLPC lregs = None →
      Jnz_spec lregs dst src lregs FailedV
  | Jnz_spec_success1 lw lregs':
      lregs !! src = Some lw →
      nonZeroL lw = false →
      incrementLPC lregs = Some lregs' →
      Jnz_spec lregs dst src lregs' NextIV
  | Jnz_spec_success2 lw lw':
      lregs !! src = Some lw →
      lregs !! dst = Some lw' →
      nonZeroL lw = true →
      Jnz_spec lregs dst src (<[PC := updatePcPermL lw' ]> lregs) NextIV.

  Definition exec_optL_Jnz
    (lregs : LReg) (dst src: RegName) : option _ :=
      lwsrc ← lregs !! src;
      lwdst ← lregs !! dst;
      if nonZeroL lwsrc
      then
        Some (NextI, ( <[PC := (updatePcPermL lwdst) ]> lregs) )
      else
        lregs' ← incrementLPC lregs ; Some (NextI , lregs').

  Lemma nonZeroL_spec (lw : LWord) :
    nonZeroL lw = nonZero (lword_get_word lw).
  Proof.
    by rewrite /nonZeroL /nonZero ; destruct lw ; cbn.
  Qed.

  Lemma wp_Jnz Ep pc_p pc_b pc_e pc_a pc_v lw dst src lregs :
    decodeInstrWL lw = Jnz dst src ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Jnz dst src) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Jnz_spec lregs dst src lregs' retv ⌝ ∗
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

    iApply (wp_wp2 (φ1 := exec_optL_Jnz lregs dst src)).

    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (lwsrc) "Hσ %HsrcL %Hsrc".

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (lwdst) "Hσ %HdstL %Hdst".
    rewrite <- nonZeroL_spec.
    destruct (nonZeroL lwsrc) eqn:Hnz.
    + (* non zero *)
    iDestruct (update_state_interp_transient_from_regs_mod (dst:= PC) (lw2 := updatePcPermL lwdst) with "Hσ") as "Hσ".
    { rewrite elem_of_dom; eexists; eauto. }
    { intros.
      eapply is_cur_updatePcPermL; eauto.
    }
    iApply wp2_val; cbn.
    rewrite updatePcPermL_spec.
    iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
    cbn.
    iModIntro.
    change (language.to_val (Instr NextI)) with (Some NextIV); cbn.
    iApply ("Hφ" with "[$Hpc_a $Hregs]").
    iPureIntro; by eapply Jnz_spec_success2.

    + (* zero *)
      rewrite updatePC_incrementPC.
      iApply (wp_opt2_bind (k1 := fun x => Some (NextI, x))).
      iApply wp_opt2_eqn_both.
      iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := lregs)).
      { rewrite elem_of_dom; eexists; eauto. }
      iFrame "Hσ".
      iSplit; cbn.
      * iIntros "Hσ %Hin %Hlin".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; by eapply Jnz_spec_failure.
      * iIntros (lrt' rs') "Hσ %Hlis %His".
        cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
        iApply ("Hφ" with "[$Hpc_a $Hregs]").
        iPureIntro; by eapply Jnz_spec_success1.
  Qed.

  Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw1 lw2 :
    decodeInstrWL lw = Jnz r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lw2 ≠ LInt 0%Z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lw1
        ∗ ▷ r2 ↦ᵣ lw2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL lw1
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lw1
          ∗ r2 ↦ᵣ lw2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZeroL lw2 = true).
    { unfold nonZeroL, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

    destruct Hspec as [ | | ].
    { exfalso. simplify_map_eq. congruence. }
    { exfalso. simplify_map_eq. congruence. }
    { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmp2 E r2 pc_p pc_b pc_e pc_a pc_v lw lw2 :
    decodeInstrWL lw = Jnz r2 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lw2 ≠ LInt 0%Z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r2 ↦ᵣ lw2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL lw2
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ lw2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZeroL lw2 = true).
    { unfold nonZeroL, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

    destruct Hspec as [ | | ].
    { exfalso. simplify_map_eq. congruence. }
    { exfalso. simplify_map_eq. congruence. }
    { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC E pc_p pc_b pc_e pc_a pc_v lw  :
    decodeInstrWL lw = Jnz PC PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL (LCap pc_p pc_b pc_e pc_a pc_v)
          ∗ (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ].
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC1 E r2 pc_p pc_b pc_e pc_a pc_v lw lw2 :
    decodeInstrWL lw = Jnz PC r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lw2 ≠ LInt 0%Z →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r2 ↦ᵣ lw2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL (LCap pc_p pc_b pc_e pc_a pc_v)
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ lw2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZeroL lw2 = true).
    { unfold nonZeroL, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

    destruct Hspec as [ | | ].
    { exfalso. simplify_map_eq. congruence. }
    { exfalso. simplify_map_eq. congruence. }
    { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC2 E r1 pc_p pc_b pc_e pc_a pc_v lw lw1 :
    decodeInstrWL lw = Jnz r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lw1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPermL lw1
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lw1 }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ].
    { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_next E r1 r2 pc_p pc_b pc_e pc_a pc_v pc_a' lw lw1 :
    decodeInstrWL lw = Jnz r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lw1
        ∗ ▷ r2 ↦ᵣ LInt 0%Z }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lw1
          ∗ r2 ↦ᵣ LInt 0%Z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ]; try incrementLPC_inv; simplify_map_eq; eauto.
    { congruence. }
    { iApply "Hφ". iFrame. rewrite insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

End cap_lang_rules.
