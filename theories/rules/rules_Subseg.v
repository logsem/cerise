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
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word. 

  Inductive Subseg_failure  (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) : Reg → Prop :=
  | Subseg_fail_dst_noncap z :
      regs !! dst = Some (WInt z) →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_pE p b e a :
      regs !! dst = Some (WCap p b e a) →
      p = E →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src1_nonaddr :
      addr_of_argument regs src1 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src2_nonaddr :
      addr_of_argument regs src2 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_not_iswithin p b e a a1 a2 :
      regs !! dst = Some (WCap p b e a) →
      addr_of_argument regs src1 = Some a1 →
      addr_of_argument regs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC p b e a a1 a2 :
      regs !! dst = Some (WCap p b e a) →
      p <> E →
      addr_of_argument regs src1 = Some a1 →
      addr_of_argument regs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementPC (<[ dst := WCap p a1 a2 a ]> regs) = None →
      Subseg_failure regs dst src1 src2 regs.

  Inductive Subseg_spec (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Subseg_spec_success p b e a a1 a2:
      regs !! dst = Some (WCap p b e a) ->
      p <> E ->
      addr_of_argument regs src1 = Some a1 ->
      addr_of_argument regs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementPC (<[ dst := WCap p a1 a2 a ]> regs) = Some regs' ->
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_failure :
      Subseg_failure regs dst src1 src2 regs' →
      Subseg_spec regs dst src1 src2 regs' FailedV.

  
  Lemma wp_Subseg Ep pc_p pc_b pc_e pc_a w dst src1 src2 regs :
    decodeInstrW w = Subseg dst src1 src2 ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom _ regs →
    
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep; cbn in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1;
      pose proof Ha1 as H'a1; cycle 1.
    { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep.
      { rewrite /RegLocate Hdst Ha1 /= in Hstep.
        assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
      subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'1 in Ha1.
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct r1v ; simplify_pair_eq.
        all: unfold addr_of_argument, z_of_argument at 2 in Hstep.
        all: rewrite /= /RegLocate Hdst Hr1 ?Ha1 /= in Hstep.
        all: inv Hstep; auto.
      }
      repeat case_match; try congruence.
      all: iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
    apply (addr_of_arg_mono _ r) in Ha1; auto. rewrite Ha1 /= in Hstep.

    destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2;
      pose proof Ha2 as H'a2; cycle 1.
    { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep.
      { rewrite /RegLocate Hdst Ha2 /= in Hstep.
        assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iFailWP "Hφ" Subseg_fail_src2_nonaddr. }
      subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'2 in Ha2.
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct r2v ; simplify_pair_eq.
        all: unfold addr_of_argument, z_of_argument  in Hstep.
        all: rewrite /= /RegLocate Hdst Hr2 ?Ha2 /= in Hstep.
        all: inv Hstep; auto.
      }
      repeat case_match; try congruence.
      all: iFailWP "Hφ" Subseg_fail_src2_nonaddr. }
    apply (addr_of_arg_mono _ r) in Ha2; auto. rewrite Ha2 /= in Hstep.

    destruct wdst.
    { rewrite /= /RegLocate Hdst in Hstep. repeat case_match; inv Hstep; simplify_pair_eq.
      all: iFailWP "Hφ" Subseg_fail_dst_noncap. }
    apply regs_lookup_eq in Hdst. rewrite Hdst in Hstep.

    destruct (decide (p = E)).
    { subst p. inv Hstep.
      iFailWP "Hφ" Subseg_fail_pE. }

    rewrite /update_reg /= in Hstep.

    destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
    { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Subseg_fail_not_iswithin. }

    destruct (incrementPC (<[ dst := (WCap p a1 a2 a) ]> regs)) eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { assert (incrementPC (<[ dst := (WCap p a1 a2 a) ]> r) = None) as HH.
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       apply (incrementPC_fail_updatePC _ m) in HH. rewrite HH in Hstep.
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
           by (destruct p; inversion Hstep; auto).
       iFailWP "Hφ" Subseg_fail_incrPC. }

    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
     eassert ((c, σ2) = (NextI, _)) as HH.
     { destruct p; cbn in Hstep; eauto. congruence. }
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_subseg_success E pc_p pc_b pc_e pc_a w dst r1 r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap p b e a
        ∗ ▷ r1 ↦ᵣ WInt n1
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WCap p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_b pc_e pc_a w dst r1 p b e a n1 a1 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    p ≠ machine_base.E →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap p b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WCap p a1 a1 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_b pc_e pc_a w dst r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap p b e a
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WCap p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_b pc_e pc_a w dst r1 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap p b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WCap p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_b pc_e pc_a w dst p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WCap p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_b pc_e pc_a w r1 r2 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence. congruence. }
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_b pc_e pc_a w r1 n1 a1 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    pc_p ≠ machine_base.E →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p a1 a1 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence. congruence. }
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_b pc_e pc_a w r2 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r2) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence. congruence. }
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_b pc_e pc_a w r1 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence. congruence. }
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_b pc_e pc_a w n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; unfold addr_of_argument, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence. congruence. }
  Qed.

End cap_lang_rules.
