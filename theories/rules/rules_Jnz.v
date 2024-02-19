From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
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
  (*   iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ". *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
  (*   iDestruct "Hσ1" as "[Hr Hm]". *)
  (*   iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)
  (*   have ? := lookup_weaken _ _ _ _ HPC Hregs. *)
  (*   iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto. *)
  (*   iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
  (*   iNext. iIntros (e2 σ2 efs Hpstep). *)
  (*   apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
  (*   iIntros "_". *)
  (*   iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)

  (*   specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. *)
  (*   unfold regs_of in Hri, Dregs. *)
  (*   destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+. *)
  (*   destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. *)
  (*   unfold exec in Hstep; cbn in Hstep. *)

  (*   destruct (nonZero wsrc) eqn:Hnz; pose proof Hnz as H'nz; *)
  (*     cbn in Hstep; rewrite Hsrc Hdst /= Hnz in Hstep. *)
  (*   { inv Hstep. simplify_pair_eq. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 3; eauto. } *)

  (*   destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1. *)
  (*   { eapply incrementPC_fail_updatePC with (m:=mem) in HX. *)
  (*     eapply updatePC_fail_incl with (m':=mem) in HX; eauto. *)
  (*     rewrite HX in Hstep. inv Hstep. *)
  (*     iFrame. iApply "Hφ". iFrame. iPureIntro; econstructor; eauto. } *)

  (*   destruct (incrementPC_success_updatePC _ mem etable enumcur _ HX) *)
  (*     as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
  (*   eapply updatePC_success_incl with (m':=mem) in HuPC; eauto. rewrite HuPC in Hstep. *)
  (*   simplify_pair_eq. *)
  (*   iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*   iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto. *)
  (*   Unshelve. all: eassumption. *)
  (* Qed. *)
  Admitted.

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
