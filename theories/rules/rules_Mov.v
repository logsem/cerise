From stdpp Require Import namespaces hlist pretty.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.proofmode Require Import coq_tactics ltac_tactics.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
  Context `{reservedaddresses : ReservedAddresses}.
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

  Inductive Mov_spec (lregs: LReg) (dst: RegName) (src: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Mov_spec_success lw:
      word_of_argumentL lregs src = Some lw →
      incrementLPC (<[ dst := lw ]> lregs) = Some lregs' →
      Mov_spec lregs dst src lregs' NextIV
  | Mov_spec_failure lw:
      word_of_argumentL lregs src = Some lw →
      incrementLPC (<[ dst := lw ]> lregs) = None →
      Mov_spec lregs dst src lregs' FailedV.

  Lemma wp_Mov Ep pc_p pc_b pc_e pc_a pc_v lw dst src lregs :
    decodeInstrWL lw = Mov dst src ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Mov dst src) ⊆ dom lregs →
    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Mov_spec lregs dst src lregs' retv ⌝ ∗
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

    iApply wp_wp2.
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }
    iApply (wp2_word_of_argument (lrt := lregs) (lw := lw) with "[$Hσ Hφ Hpc_a Hcred]"); first by set_solver.
    iIntros (lw2) "Hσ %Heqlw2 %Heqw2".

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (k1 := fun x => Some x)).
    iApply wp_opt2_eqn_both.
    iApply (wp2_opt_incrementPC (φ := σ1) (lr := lregs) (lrt := <[ dst := lw2]> lregs)).
    { now rewrite elem_of_dom (lookup_insert_dec HPC). }

    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := lw2) with "Hσ") as "Hσ".
    { set_solver. }
    { intros. now eapply (word_of_argumentL_cur Heqlw2). }
    iFrame "Hσ".
    iSplit. cbn.
    - iIntros "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply (Mov_spec_failure _ _ _ _ _ Heqlw2 Hlin).
    - iIntros (lrt' rs') "Hσ %Hlis %His".
      iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply (Mov_spec_success _ _ _ _ _ Heqlw2 Hlis).
  Qed.

  Lemma wp_move_success_z E pc_p pc_b pc_e pc_a pc_a' pc_v lw r1 lwr1 z :
    decodeInstrWL lw = Mov r1 (inl z) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg E pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 lwr1 rv lwrv :
    decodeInstrWL lw = Mov r1 (inr rv) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1
        ∗ ▷ rv ↦ᵣ lwrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lwrv
          ∗ rv ↦ᵣ lwrv }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_same E pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 lwr1 :
    decodeInstrWL lw = Mov r1 (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ lwr1 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_samePC E pc_p pc_b pc_e pc_a pc_v pc_a' lw :
    decodeInstrWL lw = Mov PC (inr PC) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_toPC E pc_p pc_b pc_e pc_a pc_v lw r1 p b e a v a':
    decodeInstrWL lw = Mov PC (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap p b e a' v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LCap p b e a v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_fromPC E pc_p pc_b pc_e pc_a pc_v pc_a' lw r1 lwr1 :
    decodeInstrWL lw = Mov r1 (inr PC) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ lwr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End cap_lang_rules.
