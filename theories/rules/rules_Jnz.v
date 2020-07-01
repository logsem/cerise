From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Jnz_spec (regs: Reg) (dst src: RegName) : Reg → cap_lang.val → Prop :=
  | Jnz_spec_failure w:
      regs !! src = Some w →
      nonZero w = false →
      incrementPC regs = None →
      Jnz_spec regs dst src regs FailedV
  | Jnz_spec_success1 w regs':
      regs !! src = Some w →
      nonZero w = false →
      incrementPC regs = Some regs' →
      Jnz_spec regs dst src regs' NextIV
  | Jnz_spec_success2 w w':
      regs !! src = Some w →
      regs !! dst = Some w' →
      nonZero w = true →
      Jnz_spec regs dst src (<[PC := updatePcPerm w' ]> regs) NextIV.

  Lemma wp_Jnz Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src regs :
    decodeInstrW w = Jnz dst src ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of (Jnz dst src) ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jnz_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ[pc_p'] w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl. inversion Hvpc; naive_solver. }
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (nonZero wsrc) eqn:Hnz; pose proof Hnz as H'nz;
      cbn in Hstep; rewrite /RegLocate Hsrc Hdst Hnz in Hstep.
    { inv Hstep. simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 3; eauto. }

    destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in HX.
      eapply updatePC_fail_incl with (m':=m) in HX; eauto. simplify_pair_eq.
      inv Hstep. iFrame. iApply "Hφ". iFrame. iPureIntro; econstructor; eauto. }

    destruct (incrementPC_success_updatePC _ m _ HX)
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC; eauto. simplify_pair_eq.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_g pc_b pc_e pc_a w w1 w2 pc_p' :
    decodeInstrW w = Jnz r1 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq. congruence. }
   { exfalso. simplify_map_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmp2 E r2 pc_p pc_g pc_b pc_e pc_a w w2 pc_p' :
    decodeInstrW w = Jnz r2 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w2
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq. congruence. }
   { exfalso. simplify_map_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    decodeInstrW w = Jnz PC PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
          ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ].
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC1 E r2 pc_p pc_g pc_b pc_e pc_a w w2 pc_p' :
    decodeInstrW w = Jnz PC r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    w2 ≠ inl 0%Z →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (inr ((pc_p,pc_g),pc_b,pc_e,pc_a))
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero w2 = true).
    { unfold nonZero, Zneq_bool in *.
      repeat case_match; try congruence; subst. exfalso.
      apply Hne. f_equal. by apply Z.compare_eq. }

   destruct Hspec as [ | | ].
   { exfalso. simplify_map_eq. congruence. }
   { exfalso. simplify_map_eq. congruence. }
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_jmpPC2 E r1 pc_p pc_g pc_b pc_e pc_a w w1 pc_p' :
    decodeInstrW w = Jnz r1 PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w1
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ].
   { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_jnz_success_next E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_a' w w1 pc_p' :
    decodeInstrW w = Jnz r1 r2 →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ inl 0%Z }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ inl 0%Z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | | ]; try incrementPC_inv; simplify_map_eq; eauto.
   { congruence. }
   { iApply "Hφ". iFrame. rewrite insert_insert.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
  Qed.

End cap_lang_rules.
