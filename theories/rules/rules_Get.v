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
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition denote (i: instr) p b e a: Z :=
    match i with
    | GetP _ _ => encodePerm p
    | GetB _ _ => b
    | GetE _ _ => e
    | GetA _ _ => a
    | _ => 0%Z
    end.

  Global Arguments denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetA dst src.

  Lemma regs_of_is_Get i dst src :
    is_Get i dst src →
    regs_of i = {[ dst; src ]}.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  Lemma regs_of_core_is_Get it dst src i :
    is_Get it dst src →
    regs_of_core it i = {[ (i,dst); (i,src) ]}.
  Proof.
    intros HH.
    rewrite /regs_of_core.
    erewrite regs_of_is_Get ; eauto.
    set_solver.
  Qed.

  Inductive Get_failure (it: instr) (i : CoreN) (regs: Reg) (dst src: RegName) :=
    | Get_fail_src_noncap : forall n,
        regs !! (i, src) = Some (WInt n) →
        Get_failure it i regs dst src
    | Get_fail_overflow_PC : forall p b e a,
        regs !! (i, src) = Some (WCap p b e a) →
        incrementPC (<[ (i, dst) := WInt (denote it p b e a) ]> regs) i = None →
        Get_failure it i regs dst src.

  Inductive Get_spec (it: instr) (i : CoreN) (regs: Reg) (dst src: RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Get_spec_success p b e a:
      regs !! (i, src) = Some (WCap p b e a) →
      incrementPC (<[ (i, dst) := WInt (denote it p b e a) ]> regs) i = Some regs' →
      Get_spec it i regs dst src regs' (i, NextIV)
  | Get_spec_failure:
      Get_failure it i regs dst src →
      Get_spec it i regs dst src regs' (i, FailedV).



  Lemma wp_Get Ep i pc_p pc_b pc_e pc_a w get_i dst src (regs : Reg) :
    decodeInstrW w = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of_core get_i i ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (i, Instr Executable) @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Get_spec (decodeInstrW w) i regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hmap") as "#H".
    iDestruct "H" as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & ( c & -> & Hstep)).
    iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    specialize (Hri i).
    erewrite regs_of_core_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct wsrc as [| p b e a ] eqn:Hwsrc.
    { (* Failure: src is not a capability *)
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc in Hstep; inversion Hstep; auto. }
      iFailWP "Hφ" Get_fail_src_noncap. }

    assert (exec_opt get_i i (r, m) = updatePC i (update_reg (r, m) i dst (WInt (denote get_i p b e a)))) as HH.
    { destruct_or! Hinstr; rewrite Hinstr /= in Hstep |- *; auto; cbn in Hstep.
      all: destruct b, e, a; rewrite /update_reg Hsrc /= in Hstep |-*; auto. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ (i,dst) := WInt (denote get_i p b e a) ]> regs) i)
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inversion Hstep.
      iFailWP "Hφ" Get_fail_overflow_PC. }

    (* Success *)

    eapply (incrementPC_success_updatePC _ i m) in Hregs'
        as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ (i,dst)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ (i,PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.


  Lemma wp_Get_PC_success E i get_i dst pc_p pc_b pc_e pc_a w wdst pc_a' :
    decodeInstrW w = get_i →
    is_Get get_i dst PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    
    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, dst) ↦ᵣ wdst }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, dst) ↦ᵣ WInt (denote get_i pc_p pc_b pc_e pc_a) }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_core_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv ; simplify_map_eq by simplify_pair_eq.
      rewrite insert_commute.
      rewrite insert_insert insert_commute.
      rewrite insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame.
      all: simplify_pair_eq.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      all: try incrementPC_inv; (simplify_map_eq by simplify_pair_eq); eauto.
      congruence. }
  Qed.

  Lemma wp_Get_same_success E i get_i r pc_p pc_b pc_e pc_a w p' b' e' a' pc_a' :
    decodeInstrW w = get_i →
    is_Get get_i r r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, r) ↦ᵣ WCap p' b' e' a' }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, r) ↦ᵣ WInt (denote get_i p' b' e' a') }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_core_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; (simplify_map_eq by simplify_pair_eq).
      rewrite insert_commute ; simplify_pair_eq.
      rewrite insert_insert insert_commute ; simplify_pair_eq.
      rewrite insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; (simplify_map_eq by simplify_pair_eq); eauto.
      congruence. }
  Qed.

  Lemma wp_Get_success E i get_i dst src pc_p pc_b pc_e pc_a w wdst p' b' e' a' pc_a' :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, src) ↦ᵣ WCap p' b' e' a'
        ∗ ▷ (i, dst) ↦ᵣ wdst }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, src) ↦ᵣ WCap p' b' e' a'
          ∗ (i, dst) ↦ᵣ WInt (denote get_i p' b' e' a') }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hpca' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_core_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; (simplify_map_eq by simplify_pair_eq).
      rewrite insert_commute; simplify_pair_eq.
      rewrite insert_insert insert_commute; simplify_pair_eq.
      rewrite insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
      congruence. }
  Qed.

End cap_lang_rules.

(* Hints to automate proofs of is_Get *)

Lemma is_Get_GetP dst src : is_Get (GetP dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetB dst src : is_Get (GetB dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetE dst src : is_Get (GetE dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.

Global Hint Resolve is_Get_GetP : core.
Global Hint Resolve is_Get_GetB : core.
Global Hint Resolve is_Get_GetE : core.
Global Hint Resolve is_Get_GetA : core.
