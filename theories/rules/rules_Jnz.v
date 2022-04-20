From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
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
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap (CoreN * RegName) Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Jnz_spec (i: CoreN) (regs: Reg) (dst src: RegName) : Reg → cap_lang.val → Prop :=
  | Jnz_spec_failure w:
      regs !! (i, src) = Some w →
      nonZero w = false →
      incrementPC regs i = None →
      Jnz_spec i regs dst src regs (i, FailedV)
  | Jnz_spec_success1 w regs':
      regs !! (i, src) = Some w →
      nonZero w = false →
      incrementPC regs i = Some regs' →
      Jnz_spec i regs dst src regs' (i, NextIV)
  | Jnz_spec_success2 w w':
      regs !! (i, src) = Some w →
      regs !! (i, dst) = Some w' →
      nonZero w = true →
      Jnz_spec i regs dst src (<[(i, PC) := updatePcPerm w' ]> regs) (i, NextIV).

  Lemma wp_Jnz Ep i pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Jnz dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of_core (Jnz dst src) i ⊆ dom _ regs →
    
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (i, Instr Executable) @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jnz_spec i regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri i src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri i dst) as [wdst [H'dst Hdst]]. by set_solver+.
    unfold exec in Hstep; cbn in Hstep.

    destruct (nonZero wsrc) eqn:Hnz; pose proof Hnz as H'nz;
      cbn in Hstep; rewrite Hsrc Hdst /= Hnz in Hstep.
    { inv Hstep. simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 3; eauto. }

    destruct (incrementPC regs i) eqn:HX; pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in HX.
      eapply updatePC_fail_incl with (m':=m) in HX; eauto.
      rewrite HX in Hstep. inv Hstep.
      iFrame. iApply "Hφ". iFrame. iPureIntro; econstructor; eauto. }

    destruct (incrementPC_success_updatePC _ i m _ HX)
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq.
    iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma wp_jnz_success_jmp E i r1 r2 pc_p pc_b pc_e pc_a w w1 w2 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ w1
        ∗ ▷ (i, r2) ↦ᵣ w2 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ w1
          ∗ (i, r2) ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmp2 E i r2 pc_p pc_b pc_e pc_a w w2 :
    decodeInstrW w = Jnz r2 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r2) ↦ᵣ w2 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ updatePcPerm w2
          ∗ pc_a ↦ₐ w
          ∗ (i, r2) ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC E i pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Jnz PC PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; [ by simplify_map_eq by simplify_pair_eq .. | ].
   { iApply "Hφ". iFrame. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
     iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC1 E i r2 pc_p pc_b pc_e pc_a w w2 :
    decodeInstrW w = Jnz PC r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    w2 ≠ WInt 0%Z →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r2) ↦ᵣ w2 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w
          ∗ (i, r2) ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { exfalso. simplify_map_eq by simplify_pair_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC2 E i r1 pc_p pc_b pc_e pc_a w w1 :
    decodeInstrW w = Jnz r1 PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ w1 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; [ by simplify_map_eq by simplify_pair_eq .. | ].
   { iApply "Hφ". iFrame. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_next E i r1 r2 pc_p pc_b pc_e pc_a pc_a' w w1 :
    decodeInstrW w = Jnz r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ w1
        ∗ ▷ (i, r2) ↦ᵣ WInt 0%Z }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ w1
          ∗ (i, r2) ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
   { congruence. }
   { iApply "Hφ". iFrame. rewrite insert_insert.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

End cap_lang_rules.
