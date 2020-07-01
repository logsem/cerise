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

  Inductive Mov_spec (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | IsPtr_spec_success w:
      word_of_argument regs src = Some w →
      incrementPC (<[ dst := w ]> regs) = Some regs' →
      Mov_spec regs dst src regs' NextIV
  | Mov_spec_failure w:
      word_of_argument regs src = Some w →
      incrementPC (<[ dst := w ]> regs) = None →
      Mov_spec regs dst src regs' FailedV.

  Lemma wp_Mov Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src regs :
    decodeInstrW w = Mov dst src ->
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of (Mov dst src) ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Mov_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ[pc_p'] w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; naive_solver. }
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    assert (exists w, word_of_argument regs src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri r0) as [? [? ?]]. set_solver+. eauto. }

    pose proof Hwsrc as Hwsrc'. eapply word_of_argument_Some_inv' in Hwsrc; eauto.

    assert ((c, σ2) = updatePC (update_reg (r, m) dst wsrc)) as HH.
    { destruct Hwsrc as [ [? [? ?] ] | [? (? & ? & Hr') ] ]; simplify_eq; eauto.
      by rewrite /= /RegLocate Hr' in Hstep. }
    rewrite /update_reg /= in HH.

    destruct (incrementPC (<[ dst := wsrc ]> regs)) as [regs'|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_move_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 z pc_p' :
    decodeInstrW w = Mov r1 (inl z) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl z }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv pc_p' :
    decodeInstrW w = Mov r1 (inr rv) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ wr1
        ∗ ▷ rv ↦ᵣ wrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ wrv
          ∗ rv ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 pc_p' :
    decodeInstrW w = Mov r1 (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_samePC E pc_p pc_g pc_b pc_e pc_a pc_a' w pc_p' :
    decodeInstrW w = Mov PC (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_toPC E pc_p pc_g pc_b pc_e pc_a w r1 p g b e a a' pc_p' :
    decodeInstrW w = Mov PC (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p,g),b,e,a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inr ((p,g),b,e,a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 pc_p' :
    decodeInstrW w = Mov r1 (inr PC) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PC ≠ r1 →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hpca' Hne ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End cap_lang_rules.
