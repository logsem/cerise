From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, @regG Σ CP}.
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

  Inductive Mov_spec (i : CoreN) (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | IsPtr_spec_success w:
      word_of_argument regs i src = Some w →
      incrementPC (<[ (i, dst) := w ]> regs) i = Some regs' →
      Mov_spec i regs dst src regs' (i, NextIV)
  | Mov_spec_failure w:
      word_of_argument regs i src = Some w →
      incrementPC (<[ (i, dst) := w ]> regs) i = None →
      Mov_spec i regs dst src regs' (i, FailedV).

  Lemma wp_Mov Ep i pc_p pc_b pc_e pc_a  w dst src regs :
    decodeInstrW w = Mov dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of_core (Mov dst src) i ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (i, Instr Executable) @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Mov_spec i regs dst src regs' retv ⌝ ∗
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
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of_core in Hri.
    destruct (Hri i dst) as [wdst [H'dst Hdst]]. by set_solver+.

    assert (exists w, word_of_argument regs i src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri i r0) as [? [? ?]]. set_solver+. eauto. }

    pose proof Hwsrc as Hwsrc'. eapply word_of_argument_Some_inv' in Hwsrc; eauto.

    assert (exec_opt (Mov dst src) i (r, m)
            = updatePC i (update_reg (r, m) i dst wsrc)) as HH.
    { destruct Hwsrc as [ [? [? ?] ] | [? (? & ? & Hr') ] ]; simplify_eq; eauto.
      cbn. by rewrite /= Hr'. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ (i, dst) := wsrc ]> regs) i) as [regs'|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m0:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply (@lookup_insert_is_Some'
                         (prod (@CoreN CP) RegName) _ _ _ _ _ _ _ _ _ finmap_reg)
      ; eauto.
      2: by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto ; apply finmap_reg).
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    eapply (incrementPC_success_updatePC _ i m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ (i, dst)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_move_success_z E i pc_p pc_b pc_e pc_a pc_a' w r1 wr1 z :
    decodeInstrW w = Mov r1 (inl z) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ wr1 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv ; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert insert_commute ; simplify_pair_eq.
      rewrite insert_insert ; simplify_pair_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

  Lemma wp_move_success_reg E i pc_p pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv :
    decodeInstrW w = Mov r1 (inr rv) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ wr1
        ∗ ▷ (i, rv) ↦ᵣ wrv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ wrv
          ∗ (i, rv) ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert insert_commute ; simplify_pair_eq.
      rewrite insert_insert ; simplify_pair_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

  Lemma wp_move_success_reg_same E i pc_p pc_b pc_e pc_a pc_a' w r1 wr1 :
    decodeInstrW w = Mov r1 (inr r1) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ wr1 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert insert_commute ; simplify_pair_eq.
      rewrite insert_insert ; simplify_pair_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

  Lemma wp_move_success_reg_samePC E i pc_p pc_b pc_e pc_a pc_a' w :
    decodeInstrW w = Mov PC (inr PC) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_toPC E i pc_p pc_b pc_e pc_a w r1 p b e a a':
    decodeInstrW w = Mov PC (inr r1) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (a + 1)%a = Some a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ WCap p b e a }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap p b e a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ WCap p b e a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite insert_insert insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

  Lemma wp_move_success_reg_fromPC E i pc_p pc_b pc_e pc_a pc_a' w r1 wr1 :
    decodeInstrW w = Mov r1 (inr PC) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r1) ↦ᵣ wr1 }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r1) ↦ᵣ WCap pc_p pc_b pc_e pc_a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by unfold regs_of_core; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, r1) (i, PC)) ; simplify_pair_eq.
      rewrite insert_insert insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

End cap_lang_rules.
