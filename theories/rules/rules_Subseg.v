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
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive Subseg_failure (lregs: LReg) (dst: RegName) (src1 src2: Z + RegName) : LReg → Prop :=
  | Subseg_fail_allowed lw :
      lregs !! dst = Some lw →
      is_mutable_rangeL lw = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src1_nonaddr p b e a v:
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src1 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src2_nonaddr p b e a v:
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src2 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src1_nonotype p b e a:
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_src2_nonotype p b e a:
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src2 = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_not_iswithin_cap p b e a v a1 a2 :
      lregs !! dst = Some (LCap p b e a v) →
      addr_of_argumentL lregs src1 = Some a1 →
      addr_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_incrPC_cap p b e a v a1 a2 :
      lregs !! dst = Some (LCap p b e a v) →
      p <> E →
      addr_of_argumentL lregs src1 = Some a1 →
      addr_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementLPC (<[ dst := LCap p a1 a2 a v ]> lregs) = None →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_not_iswithin_sr p b e a a1 a2 :
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = Some a1 →
      otype_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = false →
      Subseg_failure lregs dst src1 src2 lregs
  | Subseg_fail_incrPC_sr p b e a a1 a2 :
      lregs !! dst = Some (LSealRange p b e a) →
      otype_of_argumentL lregs src1 = Some a1 →
      otype_of_argumentL lregs src2 = Some a2 →
      isWithin a1 a2 b e = true →
      incrementLPC (<[ dst := LSealRange p a1 a2 a ]> lregs) = None →
      Subseg_failure lregs dst src1 src2 lregs.

  Inductive Subseg_spec (lregs: LReg) (dst: RegName) (src1 src2: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Subseg_spec_success_cap p b e a v a1 a2:
      lregs !! dst = Some (LCap p b e a v) ->
      p <> E ->
      addr_of_argumentL lregs src1 = Some a1 ->
      addr_of_argumentL lregs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementLPC (<[ dst := LCap p a1 a2 a v]> lregs) = Some lregs' ->
      Subseg_spec lregs dst src1 src2 lregs' NextIV
  | Subseg_spec_success_sr p b e a v a1 a2:
      lregs !! dst = Some (LSealRange p b e a) ->
      otype_of_argumentL lregs src1 = Some a1 ->
      otype_of_argumentL lregs src2 = Some a2 ->
      isWithin a1 a2 b e = true ->
      incrementLPC (<[ dst := LSealRange p a1 a2 a ]> lregs) = Some lregs' ->
      Subseg_spec lregs dst src1 src2 lregs' NextIV
  | Subseg_spec_failure :
      Subseg_failure lregs dst src1 src2 lregs' →
      Subseg_spec lregs dst src1 src2 lregs' FailedV.

  Lemma wp_Subseg Ep pc_p pc_b pc_e pc_a pc_v lw dst src1 src2 lregs :
    decodeInstrWL lw = Subseg dst src1 src2 ->
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Subseg dst src1 src2) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ Subseg_spec lregs dst src1 src2 lregs' retv ⌝ ∗
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
  (*   destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+. *)

  (*   rewrite /exec /= Hdst /= in Hstep. *)

  (*   destruct (is_mutable_range wdst) eqn:Hwdst. *)
  (*    2: { (* Failure: wdst is not of the right type *) *)
  (*      unfold is_mutable_range in Hwdst. *)
  (*      assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*      { destruct wdst as [ | [p b e a | ] | ]; try by inversion Hwdst. *)
  (*        all: try by simplify_pair_eq. *)
  (*        destruct p; try congruence. *)
  (*        repeat destruct (addr_of_argument reg _); cbn in Hstep; simplify_pair_eq; auto. } *)
  (*      iFailWP "Hφ" Subseg_fail_allowed. } *)

  (*   (* Now the proof splits depending on the type of value in wdst *) *)
  (*   destruct wdst as [ | [p b e a | p b e a] | ]. *)
  (*   1,4: inversion Hwdst. *)

  (*   (* First, the case where r1v is a capability *) *)
  (*   + destruct (perm_eq_dec p E); [ subst p |]. *)
  (*      { rewrite /is_mutable_range in Hwdst; congruence. } *)

  (*     destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1; *)
  (*       pose proof Ha1 as H'a1; cycle 1. *)
  (*     { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep. *)
  (*       { rewrite Ha1 /= in Hstep. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { repeat case_match; inv Hstep; auto. } *)
  (*         iFailWP "Hφ" Subseg_fail_src1_nonaddr. } *)
  (*       subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]]. *)
  (*         by unfold regs_of_argument; set_solver+. *)
  (*         rewrite /addr_of_argument /= Hr'1 in Ha1. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { destruct r1v ; simplify_pair_eq. *)
  (*           all: unfold addr_of_argument, z_of_argument at 2 in Hstep. *)
  (*           all: rewrite /= Hr1 ?Ha1 /= in Hstep. *)
  (*           all: inv Hstep; auto. *)
  (*         } *)
  (*         repeat case_match; try congruence. *)
  (*         all: iFailWP "Hφ" Subseg_fail_src1_nonaddr. } *)
  (*     apply (addr_of_arg_mono _ reg) in Ha1; auto. rewrite Ha1 /= in Hstep. *)

  (*     destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2; *)
  (*       pose proof Ha2 as H'a2; cycle 1. *)
  (*     { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep. *)
  (*       { rewrite Ha2 /= in Hstep. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { repeat case_match; inv Hstep; auto. } *)
  (*         iFailWP "Hφ" Subseg_fail_src2_nonaddr. } *)
  (*       subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]]. *)
  (*         by unfold regs_of_argument; set_solver+. *)
  (*         rewrite /addr_of_argument /= Hr'2 in Ha2. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { destruct r2v ; simplify_pair_eq. *)
  (*           all: unfold addr_of_argument, z_of_argument  in Hstep. *)
  (*           all: rewrite /= Hr2 ?Ha2 /= in Hstep. *)
  (*           all: inv Hstep; auto. *)
  (*         } *)
  (*         repeat case_match; try congruence. *)
  (*         all: iFailWP "Hφ" Subseg_fail_src2_nonaddr. } *)
  (*     apply (addr_of_arg_mono _ reg) in Ha2; auto. rewrite Ha2 /= in Hstep. *)
  (*     rewrite /update_reg /= in Hstep. *)

  (*     destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1. *)
  (*     { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Subseg_fail_not_iswithin_cap. } *)

  (*     destruct (incrementPC (<[ dst := (WCap p a1 a2 a) ]> regs)) eqn:Hregs'; *)
  (*       pose proof Hregs' as H'regs'; cycle 1. *)
  (*     { assert (incrementPC (<[ dst := (WCap p a1 a2 a) ]> reg) = None) as HH. *)
  (*       { eapply incrementPC_overflow_mono; first eapply Hregs'. *)
  (*           by rewrite lookup_insert_is_Some'; eauto. *)
  (*             by apply insert_mono; eauto. } *)
  (*       eapply (incrementPC_fail_updatePC _ mem) in HH. rewrite HH in Hstep. *)
  (*       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->) *)
  (*           by (destruct p; inversion Hstep; auto). *)
  (*       iFailWP "Hφ" Subseg_fail_incrPC_cap. } *)

  (*     eapply (incrementPC_success_updatePC _ mem) in Hregs' *)
  (*       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
  (*     eapply updatePC_success_incl with (m':=mem) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep. *)
  (*     eassert ((c, σ2) = (NextI, _)) as HH. *)
  (*     { destruct p; cbn in Hstep; eauto. congruence. } *)
  (*     simplify_pair_eq. iFrame. *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto. *)
  (*    (* Now, the case where wsrc is a capability *) *)
  (*   + destruct (otype_of_argument regs src1) as [a1|] eqn:Ha1; *)
  (*       pose proof Ha1 as H'a1; cycle 1. *)
  (*     { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep. *)
  (*       { rewrite Ha1 /= in Hstep. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { repeat case_match; inv Hstep; auto. } *)
  (*         iFailWP "Hφ" Subseg_fail_src1_nonotype. } *)
  (*       subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]]. *)
  (*         by unfold regs_of_argument; set_solver+. *)
  (*         rewrite /otype_of_argument /= Hr'1 in Ha1. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { destruct r1v ; simplify_pair_eq. *)
  (*           all: unfold otype_of_argument, z_of_argument at 2 in Hstep. *)
  (*           all: rewrite /= Hr1 ?Ha1 /= in Hstep. *)
  (*           all: inv Hstep; auto. *)
  (*         } *)
  (*         repeat case_match; try congruence. *)
  (*         all: iFailWP "Hφ" Subseg_fail_src1_nonotype. } *)
  (*     apply (otype_of_arg_mono _ reg) in Ha1; auto. rewrite Ha1 /= in Hstep. *)

  (*     destruct (otype_of_argument regs src2) as [a2|] eqn:Ha2; *)
  (*       pose proof Ha2 as H'a2; cycle 1. *)
  (*     { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep. *)
  (*       { rewrite Ha2 /= in Hstep. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { repeat case_match; inv Hstep; auto. } *)
  (*         iFailWP "Hφ" Subseg_fail_src2_nonotype. } *)
  (*       subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]]. *)
  (*         by unfold regs_of_argument; set_solver+. *)
  (*         rewrite /otype_of_argument /= Hr'2 in Ha2. *)
  (*         assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
  (*         { destruct r2v ; simplify_pair_eq. *)
  (*           all: unfold otype_of_argument, z_of_argument  in Hstep. *)
  (*           all: rewrite /= Hr2 ?Ha2 /= in Hstep. *)
  (*           all: inv Hstep; auto. *)
  (*         } *)
  (*         repeat case_match; try congruence. *)
  (*         all: iFailWP "Hφ" Subseg_fail_src2_nonotype. } *)
  (*     apply (otype_of_arg_mono _ reg) in Ha2; auto. rewrite Ha2 /= in Hstep. *)
  (*     rewrite /update_reg /= in Hstep. *)

  (*     destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1. *)
  (*     { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Subseg_fail_not_iswithin_sr. } *)

  (*     destruct (incrementPC (<[ dst := (WSealRange p a1 a2 a) ]> regs)) eqn:Hregs'; *)
  (*       pose proof Hregs' as H'regs'; cycle 1. *)
  (*     { assert (incrementPC (<[ dst := (WSealRange p a1 a2 a) ]> reg) = None) as HH. *)
  (*       { eapply incrementPC_overflow_mono; first eapply Hregs'. *)
  (*           by rewrite lookup_insert_is_Some'; eauto. *)
  (*             by apply insert_mono; eauto. } *)
  (*       eapply (incrementPC_fail_updatePC _ mem) in HH. rewrite HH in Hstep. *)
  (*       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->) *)
  (*           by (destruct p; inversion Hstep; auto). *)
  (*       iFailWP "Hφ" Subseg_fail_incrPC_sr. } *)

  (*     eapply (incrementPC_success_updatePC _ mem) in Hregs' *)
  (*       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->). *)
  (*     eapply updatePC_success_incl with (m':=mem) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep. *)
  (*     eassert ((c, σ2) = (NextI, _)) as HH. *)
  (*     { destruct p; cbn in Hstep; eauto. } *)
  (*     simplify_pair_eq. iFrame. *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto. *)
  (*     Unshelve. all: auto. *)
  (* Qed. *)
  Admitted.

  Lemma wp_subseg_success E pc_p pc_b pc_e pc_a pc_v lw dst r1 r2 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a v n1 a1 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 →
    p ≠ machine_base.E →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LCap p a1 a1 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_b pc_e pc_a pc_v lw dst r2 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a v n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LCap p a1 a2 a v
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct p; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_fail_lr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a v n1 n2 a1 a2 :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    ¬ (p ≠ machine_base.E ∧ isWithin a1 a2 b e = true) →
    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ dst ↦ᵣ LCap p b e a v }}}
      Instr Executable @ E
      {{{ RET FailedV;
          ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
            ∗ ▷ (pc_a, pc_v) ↦ₐ lw
            ∗ ▷ dst ↦ᵣ LCap p b e a v }}}.
  Proof.
    iIntros (? ? ? ? Hncond ?) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [| | * Hfail].
    { (* Success (contradiction) *)
      exfalso. apply Hncond. simplify_map_eq. split; first done.
      by cbn in * ; simplify_eq. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure *)
      destruct Hfail; cbn in *; simplify_map_eq.
      all: iApply "Hφ"; iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_b pc_e pc_a pc_v lw r1 r2 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_b pc_e pc_a pc_v lw r1 n1 a1 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 →
    pc_p ≠ machine_base.E →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a1 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_b pc_e pc_a pc_v lw r2 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r2) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_b pc_e pc_a pc_v lw r1 n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC r1) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_b pc_e pc_a pc_v lw n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg PC (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    pc_p ≠ machine_base.E →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p a1 a2 pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hpne Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold addr_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Success with WSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold addr_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; try congruence.
      destruct pc_p; congruence. congruence. }
    Unshelve. all: auto.
  Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

  Lemma wp_subseg_success_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with WCap (contradiction) *)
       simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a n1 a1 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inr r1) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LSealRange p a1 a1 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l_sr E pc_p pc_b pc_e pc_a pc_v lw dst r2 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r2 ↦ᵣ LInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r_sr E pc_p pc_b pc_e pc_a pc_v lw dst r1 p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inr r1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a
        ∗ ▷ r1 ↦ᵣ LInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr_sr E pc_p pc_b pc_e pc_a pc_v lw dst p b e a n1 n2 a1 a2 pc_a' :
    decodeInstrWL lw = Subseg dst (inl n1) (inl n2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LSealRange p b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LSealRange p a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | * Hfail].
    { (* Success with LSealRange (contradiction) *)
      simplify_map_eq. }
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      unfold otype_of_argumentL, z_of_argument in *. simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; unfold otype_of_argumentL, z_of_argument in *.
      all: simplify_map_eq; eauto; congruence. }
    Unshelve. all: auto.
  Qed.

End cap_lang_rules.
