From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (* TODO: move to stdpp *)
  Tactic Notation "destruct_or" ident(H) :=
  match type of H with
  | _ ∨ _ => destruct H as [H|H]
  | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
  end.
  Tactic Notation "destruct_or" "?" ident(H) := repeat (destruct_or H).
  Tactic Notation "destruct_or" "!" ident(H) := hnf in H; destruct_or H; destruct_or? H.

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | cap_lang.Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_AddSubLt (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = cap_lang.Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Lt r arg1 arg2.

  Lemma regs_of_is_AddSubLt i r arg1 arg2 :
    is_AddSubLt i r arg1 arg2 →
    regs_of i = {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  (* TODO: move to rules_base *)
  Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
    z_of_argument regs arg = Some z →
    (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z)).
  Proof.
    unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  Qed.

  (* TODO: move to rules_base. *)
  (* TODO: add in the second case of the conclusion the fact that [regs !! r = Some (inl z)]
     (there is an unecessary loss of generality at the moment) *)
  Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
    z_of_argument regs arg = Some z →
    regs ⊆ regs' →
    (arg = inl z ∨ ∃ r, arg = inr r ∧ regs' !! r = Some (inl z)).
  Proof.
    unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
    intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
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
      incrementPC (<[ dst := inl (denote i n1 n2) ]> regs) = None ->
      regs' = (<[ dst := inl (denote i n1 n2) ]> regs) ->
      AddSubLt_failure i regs dst rv1 rv2 regs'.

  Inductive AddSubLt_spec (i: instr) (regs: Reg) (dst: RegName) (rv1 rv2: Z + RegName) (regs': Reg): cap_lang.val -> Prop :=
  | AddSubLt_spec_success n1 n2:
      z_of_argument regs rv1 = Some n1 ->
      z_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := inl (denote i n1 n2) ]> regs) = Some regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' NextIV
  | AddSubLt_spec_failure:
      AddSubLt_failure i regs dst rv1 rv2 regs' ->
      AddSubLt_spec i regs dst rv1 rv2 regs' FailedV.

  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  (* TODO: move elsewhere *)
  Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
      x = (y, z) -> x = (u, t) ->
      y = u ∧ z = t.
  Proof. intros. subst x. inversion H2. auto. Qed.

  Tactic Notation "simplify_eq_pair" :=
    repeat
      lazymatch goal with
      | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
        assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
      | |- _ => progress simplify_eq
      end.

  Lemma wp_AddSubLt Ep i pc_p pc_g pc_b pc_e pc_a pc_p' w dst arg1 arg2 regs :
    cap_lang.decode w = i →
    is_AddSubLt i dst arg1 arg2 →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of i ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ AddSubLt_spec (cap_lang.decode w) regs dst arg1 arg2 regs' retv ⌝ ∗
          pc_a ↦ₐ[pc_p'] w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
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
    erewrite regs_of_is_AddSubLt in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (z_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold z_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn1. destruct r0v as [| (([[? ?] ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst1. }

    destruct (z_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold z_of_argument in Hn2. destruct arg2 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn2. destruct r0v as [| (([[? ?] ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" AddSubLt_fail_nonconst2. }

    eapply z_of_argument_Some_inv' in Hn1; eapply z_of_argument_Some_inv' in Hn2; eauto.

    destruct (incrementPC (<[ dst := inl (denote i n1 n2) ]> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    (* Failure: Cannot increment PC *)
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.

      assert (c = Failed ∧ σ2 = (<[ dst := inl (denote i n1 n2) ]> r, m)) as (-> & ->).
      { destruct Hn1 as [ -> | (r1 & -> & Hr1) ]; destruct Hn2 as [ -> | (r2 & -> & Hr2) ].
        all: destruct_or! Hinstr; rewrite !Hinstr /= /update_reg /RegLocate in Hstep Hregs' |- *.
        all: rewrite ?Hr1 ?Hr2 /= in Hstep.
        all: by simplify_eq_pair. }
      cbn; iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      rewrite Hdecode. iFail "Hφ" AddSubLt_fail_incrPC. }

    (* Success *)

    assert ((c, σ2) = updatePC (update_reg (r, m) dst (inl (denote i n1 n2)))) as HH.
    { destruct Hn1 as [ -> | (r1 & -> & Hr1) ]; destruct Hn2 as [ -> | (r2 & -> & Hr2) ].
      all: destruct_or! Hinstr; rewrite Hinstr /= /RegLocate /update_reg /= in Hstep |- *; auto.
      all: rewrite ?Hr1 ?Hr2 /= in Hstep; auto. }

    rewrite /update_reg /= in HH.
    eapply (incrementPC_success_updatePC _ m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in HH. simplify_eq.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  (* Derived specifications *)

  Lemma wp_add_sub_lt_success_z_z E dst pc_p pc_g pc_b pc_e pc_a w wdst ins n1 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_r_z E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r1 n1 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr r1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r1 ↦ᵣ inl n1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_z_r E dst pc_p pc_g pc_b pc_e pc_a w wdst ins n1 r2 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r2 ↦ᵣ inl n2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ inl n2
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_r_r E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r1 n1 r2 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r1 ↦ᵣ inl n1
        ∗ r2 ↦ᵣ inl n2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ r2 ↦ᵣ inl n2
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hr2 & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_r_r_same E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r n pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr r) (inr r) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r ↦ᵣ inl n
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r ↦ᵣ inl n
          ∗ dst ↦ᵣ inl (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_dst_z E dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr dst) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ dst ↦ᵣ inl n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_z_dst E dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inl n1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ dst ↦ᵣ inl n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_dst_r E dst pc_p pc_g pc_b pc_e pc_a w ins n1 r2 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr dst) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r2 ↦ᵣ inl n2
        ∗ dst ↦ᵣ inl n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r2 ↦ᵣ inl n2
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_r_dst E dst pc_p pc_g pc_b pc_e pc_a w ins r1 n1 n2 pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr r1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ r1 ↦ᵣ inl n1
        ∗ dst ↦ᵣ inl n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r1 ↦ᵣ inl n1
          ∗ dst ↦ᵣ inl (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
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

  Lemma wp_add_sub_lt_success_dst_dst E dst pc_p pc_g pc_b pc_e pc_a w ins n pc_p' pc_a' :
    cap_lang.decode w = ins →
    is_AddSubLt ins dst (inr dst) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    PermFlows pc_p pc_p' → isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ pc_a ↦ₐ[pc_p'] w
        ∗ dst ↦ᵣ inl n
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inl (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hfl Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
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

End cap_lang_rules.

(* Hints to automate proofs of is_AddSubLt *)
Lemma is_AddSubLt_Add dst arg1 arg2 :
  is_AddSubLt (cap_lang.Add dst arg1 arg2) dst arg1 arg2.
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
