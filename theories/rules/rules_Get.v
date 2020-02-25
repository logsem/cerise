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


  Definition denote (i: instr) (c: Cap): Z :=
    match c with
    | (p, g, b, e, a) =>
      match i with
      | GetP _ _ => encodePerm p
      | GetL _ _ => encodeLoc g
      | GetB _ _ => b
      | GetE _ _ => e
      | GetA _ _ => a
      | _ => 0%Z
      end
    end.

  Global Arguments denote : simpl never.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetL dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetA dst src.

  Lemma regs_of_is_Get i dst src :
    is_Get i dst src →
    regs_of i = {[ dst; src ]}.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  Inductive Get_failure (i: instr) (regs: Reg) (dst src: RegName) :=
    | Get_fail_src_noncap : forall n,
        regs !! src = Some (inl n) →
        Get_failure i regs dst src
    | Get_fail_overflow_PC : forall (c:Cap),
        regs !! src = Some (inr c) →
        incrementPC (<[ dst := inl (denote i c) ]> regs) = None →
        Get_failure i regs dst src.

  Inductive Get_spec (i: instr) (regs: Reg) (dst src: RegName) (regs': Reg): cap_lang.val -> Prop :=
  | Get_spec_success (c: Cap):
      regs !! src = Some (inr c) →
      incrementPC (<[ dst := inl (denote i c) ]> regs) = Some regs' →
      Get_spec i regs dst src regs' NextIV
  | Get_spec_failure:
      Get_failure i regs dst src →
      Get_spec i regs dst src regs' FailedV.

  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  Lemma wp_Get Ep pc_p pc_g pc_b pc_e pc_a pc_p' w get_i dst src regs :
    cap_lang.decode w = get_i →
    is_Get get_i dst src →

    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
    regs_of get_i ⊆ dom _ regs →
    {{{ ▷ pc_a ↦ₐ[pc_p'] w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Get_spec (cap_lang.decode w) regs dst src regs' retv ⌝ ∗
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
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hmap") as "#H".
    iDestruct "H" as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct wsrc as [| (([[p g] b] & e) & a) ] eqn:Hwsrc.
    { (* Failure: src is not a capability *)
      assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite /RegLocate Hsrc in Hstep; inversion Hstep; auto. }
      iFail "Hφ" Get_fail_src_noncap. }

    destruct (incrementPC (<[ dst := inl (denote get_i (p, g, b, e, a)) ]> regs))
      as [regs'|] eqn:Hregs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      assert (c = Failed ∧ σ2 = (<[ dst := inl (denote get_i (p,g,b,e,a)) ]> r, m)) as (-> & ->).
      { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
        eapply updatePC_fail_incl with (m':=m) in Hregs'.
        2: by apply lookup_insert_is_Some_weaken; eauto.
        2: by apply insert_mono; eauto.
        destruct_or! Hinstr; rewrite Hinstr in Hstep Hregs' |- *; cbn in Hstep.
        all: rewrite /RegLocate /update_reg /denote Hsrc /= in Hstep Hregs'.
        all: destruct b, e, a; rewrite Hstep in Hregs'; simplify_eq; eauto. }
      iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFail "Hφ" Get_fail_overflow_PC. by rewrite Hdecode. }

    (* Success *)

    assert ((c, σ2) = updatePC (update_reg (r, m) dst (inl (denote get_i (p,g,b,e,a))))) as HH.
    { destruct_or! Hinstr; rewrite Hinstr /= in Hstep |- *; auto; cbn in Hstep.
      all: destruct b, e, a; rewrite /RegLocate /update_reg Hsrc /= in Hstep |-*; auto. }
    clear Hstep. rewrite /update_reg in HH.

    pose proof Hregs' as Hregs'2.
    eapply (incrementPC_success_updatePC _ m) in Hregs'
        as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in HH. simplify_eq.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_Get_PC_success E get_i dst pc_p pc_g pc_b pc_e pc_a w wdst pc_a' pc_p' :
    cap_lang.decode w = get_i →
    is_Get get_i dst PC →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    dst <> PC ->

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ dst ↦ᵣ inl (denote get_i (pc_p, pc_g, pc_b, pc_e, pc_a)) }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc Hpca' HnePC φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_same_success E get_i r pc_p pc_g pc_b pc_e pc_a w (c:Cap) pc_a' pc_p' :
    cap_lang.decode w = get_i →
    is_Get get_i r r →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    r <> PC ->

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ r ↦ᵣ inr c }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ r ↦ᵣ inl (denote get_i c) }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc Hpca' HnePC φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a w wdst csrc pc_a' pc_p' :
    cap_lang.decode w = get_i →
    is_Get get_i dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' ->
    dst <> PC -> src <> PC ->

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
        ∗ ▷ pc_a ↦ₐ[pc_p'] w
        ∗ ▷ src ↦ᵣ inr csrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
          ∗ pc_a ↦ₐ[pc_p'] w
          ∗ src ↦ᵣ inr csrc
          ∗ dst ↦ᵣ inl (denote get_i csrc) }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc Hpca' Hdst Hsrc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End cap_lang_rules.

(* Hints to automate proofs of is_Get *)

Lemma is_Get_GetP dst src : is_Get (GetP dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetL dst src : is_Get (GetL dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetB dst src : is_Get (GetB dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetE dst src : is_Get (GetE dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.

Global Hint Resolve is_Get_GetP : core.
Global Hint Resolve is_Get_GetL : core.
Global Hint Resolve is_Get_GetB : core.
Global Hint Resolve is_Get_GetE : core.
Global Hint Resolve is_Get_GetA : core.
