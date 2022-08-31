From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Import machine_base.
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

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_AddSubLt (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Lt r arg1 arg2.

  Lemma regs_of_is_AddSubLt i r arg1 arg2 :
    is_AddSubLt i r arg1 arg2 →
    regs_of i = {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  Inductive AddSubLt_failure (i: instr) (regs: Reg) (dst: RegName) (rv1 rv2: Z + RegName) (regs': Reg) :=
  | AddSubLt_fail_nonconst1:
      z_of_argument regs rv1 = None ->
      AddSubLt_failure i regs dst rv1 rv2 regs'
  | AddSubLt_fail_nonconst2:
      z_of_argument regs rv2 = None ->
      AddSubLt_failure i regs dst rv1 rv2 regs'
  | AddSubLt_fail_incrPC n1 n2:
      z_of_argument regs rv1 = Some n1 ->
      z_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := WInt (denote i n1 n2) ]> regs) = None ->
      AddSubLt_failure i regs dst rv1 rv2 regs'.

  Inductive AddSubLt_spec (i: instr) (regs: Reg) (dst: RegName) (rv1 rv2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | AddSubLt_spec_success n1 n2:
      z_of_argument regs rv1 = Some n1 ->
      z_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := WInt (denote i n1 n2) ]> regs) = Some regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' NextIV
  | AddSubLt_spec_failure:
      AddSubLt_failure i regs dst rv1 rv2 regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' FailedV.

  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  Lemma wp_AddSubLt Ep i pc_p pc_b pc_e pc_a w dst arg1 arg2 regs :
    decodeInstrW w = i →
    is_AddSubLt i dst arg1 arg2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of i ⊆ dom regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ AddSubLt_spec (decodeInstrW w) regs dst arg1 arg2 regs' retv ⌝ ∗
          pc_a ↦ₐ w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
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
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_AddSubLt in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (z_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold z_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn1. destruct r0v as [| ? ? ? ? ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst1. }
    apply (z_of_arg_mono _ r) in Hn1; auto.

    destruct (z_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold z_of_argument in Hn2. destruct arg2 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn2. destruct r0v as [| ? ? ? ? ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= Hn1 in Hstep; cbn in Hstep.
        all: rewrite Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst2. }
    apply (z_of_arg_mono _ r) in Hn2; auto.

    assert (exec_opt i (r, m) = updatePC (update_reg (r, m) dst (WInt (denote i n1 n2)))) as HH.
    { all: destruct_or! Hinstr; rewrite Hinstr /= /update_reg /= in Hstep |- *; auto.
      all: by rewrite Hn1 Hn2; cbn. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := WInt (denote i n1 n2) ]> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    (* Failure: Cannot increment PC *)
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inversion Hstep.
      iFail "Hφ" AddSubLt_fail_incrPC. }


    (* Success *)

    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  (* Derived specifications *)

  Lemma wp_add_sub_lt_success_z_z E dst pc_p pc_b pc_e pc_a w wdst ins n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_z E dst pc_p pc_b pc_e pc_a w wdst ins r1 n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WInt n1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ dst PC) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_z_r E dst pc_p pc_b pc_e pc_a w wdst ins n1 r2 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ WInt n2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ dst PC) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_r E dst pc_p pc_b pc_e pc_a w wdst ins r1 n1 r2 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WInt n1
        ∗ r2 ↦ᵣ WInt n2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_r_same E dst pc_p pc_b pc_e pc_a w wdst ins r n pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r) (inr r) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r ↦ᵣ WInt n
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ WInt n
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_z E dst pc_p pc_b pc_e pc_a w ins n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr dst) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WInt n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_z_dst E dst pc_p pc_b pc_e pc_a w ins n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WInt n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_r E dst pc_p pc_b pc_e pc_a w ins n1 r2 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr dst) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ WInt n2
        ∗ dst ↦ᵣ WInt n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert. 
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_dst E dst pc_p pc_b pc_e pc_a w ins r1 n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WInt n1
        ∗ dst ↦ᵣ WInt n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_dst E dst pc_p pc_b pc_e pc_a w ins n pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr dst) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) ->

    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WInt n
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_fail_z_r E ins dst n1 r2 w wdst p b e a pc_p pc_b pc_e pc_a :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r2 ↦ᵣ WCap p b e a }}}
      Instr Executable
            @ E
    {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(HPC & Hpc_a & Hdst & Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

End cap_lang_rules.

(* Hints to automate proofs of is_AddSubLt *)
Lemma is_AddSubLt_Add dst arg1 arg2 :
  is_AddSubLt (Add dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_AddSubLt; eauto. Qed.
Lemma is_AddSubLt_Sub dst arg1 arg2 :
  is_AddSubLt (Sub dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_AddSubLt; eauto. Qed.
Lemma is_AddSubLt_Lt dst arg1 arg2 :
  is_AddSubLt (Lt dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_AddSubLt; eauto. Qed.

Global Hint Resolve is_AddSubLt_Add : core.
Global Hint Resolve is_AddSubLt_Sub : core.
Global Hint Resolve is_AddSubLt_Lt : core.
