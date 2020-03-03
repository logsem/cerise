From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word. 

  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let g := fresh "g" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as ((((p & g) & b) & e) & a).

  Inductive Subseg_failure  (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) : Reg → Prop :=
  | Subseg_fail_dst_noncap z :
      regs !! dst = Some (inl z) →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_pE p g b e a :
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p = E →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src1_nonaddr :
      addr_of_argument regs src1 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src2_nonaddr :
      addr_of_argument regs src2 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_not_iswithin p g b e a a1 a2 :
      regs !! dst = Some (inr (p, g, b, e, a)) →
      addr_of_argument regs src1 = Some a1 →
      addr_of_argument regs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC p g b e a a1 a2 :
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p <> E →
      addr_of_argument regs src1 = Some a1 →
      addr_of_argument regs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementPC (<[ dst := inr (p, g, a1, a2, a) ]> regs) = None →
      Subseg_failure regs dst src1 src2 (<[ dst := inr (p, g, a1, a2, a) ]> regs).

  Inductive Subseg_spec (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Subseg_spec_success p g b e a a1 a2:
      regs !! dst = Some (inr (p, g, b, e, a)) ->
      p <> E ->
      addr_of_argument regs src1 = Some a1 ->
      addr_of_argument regs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementPC (<[ dst := inr (p, g, a1, a2, a) ]> regs) = Some regs' ->
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_failure :
      Subseg_failure regs dst src1 src2 regs' →
      Subseg_spec regs dst src1 src2 regs' FailedV.

  
  Lemma wp_Subseg Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src1 src2 regs :
    cap_lang.decode w = Subseg dst src1 src2 ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of (Subseg dst src1 src2) ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ[pc_p'] w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    assert (pc_p' ≠ O).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst; destruct H7 as [Hcontr | [Hcontr | Hcontr]]; inversion Hcontr. }
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
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct wdst as [| cdst]; [| destruct_cap cdst].
    { rewrite /= /RegLocate Hdst in Hstep. repeat case_match; inv Hstep; simplify_pair_eq.
      all: iFailWP "Hφ" Subseg_fail_dst_noncap. }

    destruct (decide (p = E)).
    { subst p. rewrite /= /RegLocate Hdst in Hstep.
      repeat case_match; inv Hstep; simplify_pair_eq.
      all: iFailWP "Hφ" Subseg_fail_pE. }

    destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1;
      pose proof Ha1 as H'a1; cycle 1.
    { destruct src1 as [| r1] eqn:?; cbn in Ha1.
      { rewrite /= /RegLocate Hdst Ha1 in Hstep.
        assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
      subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'1 in Ha1.
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { repeat case_match; simplify_pair_eq.
        all: rewrite /= /RegLocate Hdst Hr1 ?Ha1 in Hstep.
        all: repeat case_match; inv Hstep; auto. }
      repeat case_match; try congruence.
      all: iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
    eapply addr_of_argument_Some_inv' in Ha1 as [z1 [Hz1 Hz1']]; eauto.

    destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2;
      pose proof Ha2 as H'a2; cycle 1.
    { destruct src2 as [| r2] eqn:?; cbn in Ha2.
      { rewrite /= /RegLocate Hdst Ha2 in Hstep.
        assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iFailWP "Hφ" Subseg_fail_src2_nonaddr. }
      subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'2 in Ha2.
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { repeat case_match; simplify_pair_eq.
        all: rewrite /= /RegLocate Hdst Hr2 ?Ha2 in Hstep.
        all: repeat case_match; inv Hstep; auto. }
      repeat case_match; try congruence.
      all: iFailWP "Hφ" Subseg_fail_src2_nonaddr. }
    eapply addr_of_argument_Some_inv' in Ha2 as [z2 [Hz2 Hz2']]; eauto.

    assert ((c, σ2) = if isWithin a1 a2 b e then
                        updatePC (update_reg (r, m) dst (inr (p, g, a1, a2, a))) else
                        (Failed, (r, m)))
      as Hexec.
    { rewrite -Hstep; clear Hstep. 
      rewrite /= /RegLocate Hdst.
      destruct Hz1' as [ -> | [r1 (-> & Hr1 & Hr1') ] ];
        destruct Hz2' as [ -> | [r2 (-> & Hr2 & Hr2') ] ].
      all: rewrite ?Hz1 ?Hz2 ?Hr1' ?Hr2'.
      all: repeat case_match; auto; congruence. }

    clear Hstep.
    destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
    { inv Hexec. iFailWP "Hφ" Subseg_fail_not_iswithin. }

    destruct (incrementPC (<[ dst := (inr (p, g, a1, a2, a)) ]> regs)) eqn:HX;
      pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in HX.
      eapply updatePC_fail_incl with (m':=m) in HX.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFailWP "Hφ" Subseg_fail_incrPC. }

    eapply (incrementPC_success_updatePC _ m) in HX
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg dst (inr r1) (inr r2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
        ∗ ▷ r1 ↦ᵣ inl n1
        ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ r2 ↦ᵣ inl n2
          ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
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

  Lemma wp_subseg_success_same E pc_p pc_g pc_b pc_e pc_a w dst r1 p g b e a n1 a1 pc_p' pc_a' :
    cap_lang.decode w = Subseg dst (inr r1) (inr r1) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
        ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ dst ↦ᵣ inr (p, g, a1, a1, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hn1 Hpne Hdstne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
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

  Lemma wp_subseg_success_l E pc_p pc_g pc_b pc_e pc_a w dst r2 p g b e a n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg dst (inl n1) (inr r2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
        ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ inl n2
          ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
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

  Lemma wp_subseg_success_r E pc_p pc_g pc_b pc_e pc_a w dst r1 p g b e a n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg dst (inr r1) (inl n2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
        ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
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

  Lemma wp_subseg_success_lr E pc_p pc_g pc_b pc_e pc_a w dst p g b e a n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg dst (inl n1) (inl n2) →
    PermFlows pc_p pc_p' → 
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ cap_lang.E →
    dst ≠ PC →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inr (p, g, a1, a2, a)
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hdstne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
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

  Lemma wp_subseg_success_pc E pc_p pc_g pc_b pc_e pc_a w r1 r2 n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg PC (inr r1) (inr r2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ inl n1
        ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ r2 ↦ᵣ inl n2
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
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

  Lemma wp_subseg_success_pc_same E pc_p pc_g pc_b pc_e pc_a w r1 n1 a1 pc_p' pc_a' :
    cap_lang.decode w = Subseg PC (inr r1) (inr r1) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a1,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
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

  Lemma wp_subseg_success_pc_l E pc_p pc_g pc_b pc_e pc_a w r2 n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg PC (inl n1) (inr r2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r2 ↦ᵣ inl n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ inl n2
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
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

  Lemma wp_subseg_success_pc_r E pc_p pc_g pc_b pc_e pc_a w r1 n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg PC (inr r1) (inl n2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r1 ↦ᵣ inl n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
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

  Lemma wp_subseg_success_pc_lr E pc_p pc_g pc_b pc_e pc_a w n1 n2 a1 a2 pc_p' pc_a' :
    cap_lang.decode w = Subseg PC (inl n1) (inl n2) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    pc_p ≠ cap_lang.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    
    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),a1,a2,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
      }}}.
  Proof.
    iIntros (Hinstr Hfl Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
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
