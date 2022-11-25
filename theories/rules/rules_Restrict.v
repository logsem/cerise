From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
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

  Inductive Restrict_failure (i : CoreN) (regs: Reg) (dst: RegName) (src: Z + RegName) :=
  | Restrict_fail_dst_noncap z:
      regs !! (i, dst) = Some (WInt z) →
      Restrict_failure i regs dst src
  | Restrict_fail_pE p b e a:
      regs !! (i, dst) = Some (WCap p b e a) →
      p = E →
      Restrict_failure i regs dst src
  | Restrict_fail_src_nonz:
      z_of_argument regs i src = None →
      Restrict_failure i regs dst src
  | Restrict_fail_invalid_perm p b e a n:
      regs !! (i, dst) = Some (WCap p b e a) →
      p ≠ E →
      z_of_argument regs i src = Some n →
      PermFlowsTo (decodePerm n) p = false →
      Restrict_failure i regs dst src
  | Restrict_fail_PC_overflow p b e a n:
      regs !! (i, dst) = Some (WCap p b e a) →
      p ≠ E →
      z_of_argument regs i src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementPC (<[ (i, dst) := WCap (decodePerm n) b e a ]> regs) i = None →
      Restrict_failure i regs dst src.

  Inductive Restrict_spec (i: CoreN) (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Restrict_spec_success p b e a n:
      regs !! (i, dst) = Some (WCap p b e a) →
      p ≠ E ->
      z_of_argument regs i src = Some n →
      PermFlowsTo (decodePerm n) p = true →
      incrementPC (<[ (i, dst) := WCap (decodePerm n) b e a ]> regs) i = Some regs' →
      Restrict_spec i regs dst src regs' (i, NextIV)
  | Restrict_spec_failure:
      Restrict_failure i regs dst src →
      Restrict_spec i regs dst src regs' (i, FailedV).

  Lemma wp_Restrict Ep i pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of_core (Restrict dst src) i ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (i, Instr Executable) @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Restrict_spec i regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.
    unfold exec in Hstep. cbn in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri i dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (z_of_argument regs i src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
    { destruct src as [| r0]; cbn in Hwsrc; [ congruence |].
      destruct (Hri i r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument, regs_of_core; set_solver+.
      rewrite Hr'0 in Hwsrc. destruct r0v; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { rewrite /= Hdst Hr0 in Hstep. cbn in Hstep. by simplify_pair_eq. }
      iFailWP "Hφ" Restrict_fail_src_nonz. }
    apply (z_of_arg_mono _ r) in Hwsrc; auto. rewrite Hwsrc in Hstep; simpl in Hstep.

    destruct wdst.
    { rewrite /= Hdst in Hstep.  inversion Hstep.
      all: iFailWP "Hφ" Restrict_fail_dst_noncap. }
     rewrite Hdst in Hstep.

    destruct (decide (p = E)).
    { subst p.  inv Hstep.
       iFailWP "Hφ" Restrict_fail_pE. }

    cbn in Hstep.
    destruct (PermFlowsTo (decodePerm wsrc) p) eqn:Hflows; cycle 1.
    { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Restrict_fail_invalid_perm. }

    rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ (i, dst) := WCap (decodePerm wsrc) b e a ]> regs) i) eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    {
      assert (incrementPC (<[ (i, dst) := WCap( decodePerm wsrc) b e a ]> r) i = None) as HH.
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
        by apply (@lookup_insert_is_Some'
                    (prod (@CoreN CP) RegName) _ _ _ _ _ _ _ _ _ finmap_reg)
        ; eauto.
        by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto
            ; apply finmap_reg).
      }
      apply (incrementPC_fail_updatePC _ i m) in HH. rewrite HH in Hstep.
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
                                             by (destruct p; inversion Hstep; auto).
      iFailWP "Hφ" Restrict_fail_PC_overflow. }

    eapply (incrementPC_success_updatePC _ i m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
     eassert ((c, σ2) = (NextI, _)) as HH.
     { destruct p; cbn in Hstep; eauto. congruence. }
     simplify_pair_eq.

     iFrame.
    iMod ((gen_heap_update_inSepM _ _ (i, dst)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_restrict_success_reg_PC Ep i pc_p pc_b pc_e pc_a pc_a' w rv z a' :
    decodeInstrW w = Restrict PC (inr rv) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ (i, rv) ↦ᵣ WInt z }}}
       (i, Instr Executable) @ Ep
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap (decodePerm z) pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ (i, rv) ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by unfold regs_of_core; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq by simplify_pair_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_reg Ep i pc_p pc_b pc_e pc_a pc_a' w r1 rv p b e a z :
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ (i, r1) ↦ᵣ WCap p b e a
         ∗ ▷ (i, rv) ↦ᵣ WInt z }}}
       (i, Instr Executable) @ Ep
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ (i, rv) ↦ᵣ WInt z
           ∗ (i, r1) ↦ᵣ WCap (decodePerm z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows Hnp ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by unfold regs_of_core; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r1)); simplify_pair_eq.
      rewrite insert_insert (insert_commute _ (i, PC) (i, r1)); simplify_pair_eq.
      rewrite insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq by simplify_pair_eq; eauto; try congruence.
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_PC Ep i pc_p pc_b pc_e pc_a pc_a' w z :
     decodeInstrW w = Restrict PC (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) pc_p = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w }}}
       (i, Instr Executable) @ Ep
     {{{ RET (i, NextIV);
         (i, PC) ↦ᵣ WCap (decodePerm z) pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite !insert_insert.
       iApply (regs_of_map_1 with "Hmap"). }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq by simplify_pair_eq; eauto. congruence.
       incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep i pc_p pc_b pc_e pc_a pc_a' w r1 p b e a z :
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     PermFlowsTo (decodePerm z) p = true →
     p ≠ E →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ (i, r1) ↦ᵣ WCap p b e a }}}
       (i, Instr Executable) @ Ep
     {{{ RET (i, NextIV);
         (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w
         ∗ (i, r1) ↦ᵣ WCap (decodePerm z) b e a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hflows HpE ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by unfold regs_of_core; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r1)); simplify_pair_eq.
      rewrite insert_insert (insert_commute _ (i, PC) (i, r1)); simplify_pair_eq.
      rewrite insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq by simplify_pair_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

End cap_lang_rules.
