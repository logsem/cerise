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

  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let g := fresh "g" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as ((((p & g) & b) & e) & a).

  Inductive Restrict_failure (regs: Reg) (dst: RegName) (src: Z + RegName) :=
  | Restrict_fail_dst_noncap z:
      regs !! dst = Some (inl z) →
      Restrict_failure regs dst src
  | Restrict_fail_pE p g b e a:
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p = E →
      Restrict_failure regs dst src
  | Restrict_fail_src_nonz:
      z_of_argument regs src = None →
      Restrict_failure regs dst src
  | Restrict_fail_invalid_perm p g b e a n:
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p ≠ E →
      z_of_argument regs src = Some n →
      PermPairFlowsTo (decodePermPair n) (p, g) = false →
      Restrict_failure regs dst src
  | Restrict_fail_PC_overflow p g b e a n:
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p ≠ E →
      z_of_argument regs src = Some n →
      PermPairFlowsTo (decodePermPair n) (p, g) = true →
      incrementPC (<[ dst := inr (decodePermPair n, b, e, a) ]> regs) = None →
      Restrict_failure regs dst src.

  Inductive Restrict_spec (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Restrict_spec_success p g b e a n:
      regs !! dst = Some (inr (p, g, b, e, a)) →
      p ≠ E ->
      z_of_argument regs src = Some n →
      PermPairFlowsTo (decodePermPair n) (p, g) = true →
      incrementPC (<[ dst := inr (decodePermPair n, b, e, a) ]> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_failure:
      Restrict_failure regs dst src →
      Restrict_spec regs dst src regs' FailedV.

  Lemma wp_Restrict Ep pc_p pc_g pc_b pc_e pc_a pc_p' w dst src regs :
    decodeInstrW w = Restrict dst src ->

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of (Restrict dst src) ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗
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
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct wdst as [| cdst]; [| destruct_cap cdst].
    { rewrite /= /RegLocate Hdst in Hstep. destruct src; inv Hstep; simplify_pair_eq.
      all: iFailWP "Hφ" Restrict_fail_dst_noncap. }

    destruct (z_of_argument regs src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
    { destruct src as [| r0]; cbn in Hwsrc; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hwsrc. destruct r0v as [| cc]; [ congruence | destruct_cap cc].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { rewrite /= /RegLocate Hdst Hr0 in Hstep. by simplify_pair_eq. }
      iFailWP "Hφ" Restrict_fail_src_nonz. }
    eapply z_of_argument_Some_inv' in Hwsrc; eauto.

    destruct (decide (p = E)).
    { subst p. cbn in Hstep. rewrite /RegLocate Hdst in Hstep.
      repeat case_match; inv Hstep; iFailWP "Hφ" Restrict_fail_pE. }

    destruct (PermPairFlowsTo (decodePermPair wsrc) (p, g)) eqn:Hflows; cycle 1.
    { rewrite /= /RegLocate Hdst in Hstep.
      destruct Hwsrc as [ -> | (r0 & -> & Hr0 & Hr0') ].
      all: rewrite ?Hr0' Hflows in Hstep.
      all: repeat case_match; inv Hstep; iFailWP "Hφ" Restrict_fail_invalid_perm. }

    assert ((c, σ2) = updatePC (update_reg (r, m) dst (inr (decodePermPair wsrc, b, e, a)))) as HH.
    { rewrite /= /RegLocate Hdst in Hstep.
      destruct Hwsrc as [ -> | (r0 & -> & Hr0 & Hr0') ].
      all: rewrite ?Hr0' Hflows in Hstep.
      all: repeat case_match; inv Hstep; eauto; congruence. }
    clear Hstep. rewrite /update_reg /= in HH.

    destruct (incrementPC (<[ dst := inr (decodePermPair wsrc, b, e, a) ]> regs)) eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFailWP "Hφ" Restrict_fail_PC_overflow. }

    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_restrict_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z a' pc_p' :
    decodeInstrW w = Restrict PC (inr rv) →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    PermPairFlowsTo (decodePermPair z) (pc_p,pc_g) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w
         ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr (decodePermPair z,pc_b,pc_e,pc_a')
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ rv ↦ᵣ inl z }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       destruct (decodePermPair n); simplify_eq. rewrite !insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z
         pc_p' :
     decodeInstrW w = Restrict r1 (inr rv) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (p,g) = true →
     r1 ≠ PC → p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w
         ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
         ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e, pc_a')
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ rv ↦ᵣ inl z
           ∗ r1 ↦ᵣ inr (decodePermPair z,b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows Hne1 Hnp ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z pc_p' :
     decodeInstrW w = Restrict PC (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (pc_p,pc_g) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr (decodePermPair z,pc_b,pc_e,pc_a')
         ∗ pc_a ↦ₐ[pc_p'] w }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert. destruct (decodePermPair n); simplify_eq.
       iApply (regs_of_map_1 with "Hmap"). }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto. congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z pc_p' :
     decodeInstrW w = Restrict r1 (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (p,g) = true →
     r1 ≠ PC → p ≠ E →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
         ∗ ▷ pc_a ↦ₐ[pc_p'] w
         ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
         ∗ pc_a ↦ₐ[pc_p'] w
         ∗ r1 ↦ᵣ inr (decodePermPair z,b,e,a) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hflows Hne1 HpE ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     by unfold regs_of; rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
     assert (pc_p ≠ E).
     { intros ->. inversion Hvpc; subst. naive_solver. }

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       destruct (decodePermPair n); simplify_eq.
       rewrite (insert_commute _ PC r1) // insert_insert
               (insert_commute _ PC r1) // insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

End cap_lang_rules.
