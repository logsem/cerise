From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Import machine_base.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
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

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Mod _ _ _ => (n1 `mod` n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | HashConcat _ _ _ => (hash_concat n1 n2)
    | _ => 0%Z
    end.

  Definition is_AddSubLt (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Mod r arg1 arg2 ∨
    i = HashConcat r arg1 arg2 ∨
    i = Lt r arg1 arg2.

  Lemma exec_AddSubLt_eq {i r arg1 arg2 φ} :
    is_AddSubLt i r arg1 arg2 ->
    exec_opt i φ = z1 ← z_of_argument (reg φ) arg1 ;
                   z2 ← z_of_argument (reg φ) arg2 ;
                   updatePC (update_reg φ r (WInt (denote i z1 z2))).
  Proof.
    destruct 1 as [-> | [-> | [-> | [-> | ->] ] ]]; done.
  Qed.


  Lemma regs_of_is_AddSubLt i r arg1 arg2 :
    is_AddSubLt i r arg1 arg2 →
    regs_of i = {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  Inductive AddSubLt_failure (i: instr) (lregs: LReg) (dst: RegName) (rv1 rv2: Z + RegName) (lregs': LReg) :=
  | AddSubLt_fail_nonconst1:
      z_of_argumentL lregs rv1 = None ->
      AddSubLt_failure i lregs dst rv1 rv2 lregs'
  | AddSubLt_fail_nonconst2:
      z_of_argumentL lregs rv2 = None ->
      AddSubLt_failure i lregs dst rv1 rv2 lregs'
  | AddSubLt_fail_incrPC n1 n2:
      z_of_argumentL lregs rv1 = Some n1 ->
      z_of_argumentL lregs rv2 = Some n2 ->
      incrementLPC (<[ dst := LInt (denote i n1 n2) ]> lregs) = None ->
      AddSubLt_failure i lregs dst rv1 rv2 lregs'.

  Inductive AddSubLt_spec (i: instr) (lregs: LReg) (dst: RegName) (rv1 rv2: Z + RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | AddSubLt_spec_success n1 n2:
      z_of_argumentL lregs rv1 = Some n1 ->
      z_of_argumentL lregs rv2 = Some n2 ->
      incrementLPC (<[ dst := LInt (denote i n1 n2) ]> lregs) = Some lregs' ->
      AddSubLt_spec i lregs dst rv1 rv2 lregs' NextIV
  | AddSubLt_spec_failure:
      AddSubLt_failure i lregs dst rv1 rv2 lregs' ->
      AddSubLt_spec i lregs dst rv1 rv2 lregs' FailedV.

  (* Local Ltac iFail Hcont get_fail_case := *)
  (*   cbn; iFrame; iApply Hcont; iFrame; iPureIntro; *)
  (*   econstructor; eapply get_fail_case; eauto. *)

  Lemma wp_AddSubLt Ep i pc_p pc_b pc_e pc_a pc_v lw dst arg1 arg2 lregs :
    decodeInstrWL lw = i →
    is_AddSubLt i dst arg1 arg2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of i ⊆ dom lregs →
    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lregs' retv, RET retv;
        ⌜ AddSubLt_spec (decodeInstrWL lw) lregs dst arg1 arg2 lregs' retv ⌝ ∗
          (pc_a, pc_v) ↦ₐ lw ∗
          [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (HdecodeLW Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_exec_opt Hvpc HPC HdecodeLW Dregs).
    iFrame.
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrectpc & %HdecodeW) Hcred".

    (* case split on i *)
    rewrite (exec_AddSubLt_eq Hinstr).
    rewrite (regs_of_is_AddSubLt _ _ _ _ Hinstr) in Dregs.

    (* Starting the transaction *)
    iApply wp_wp2.
    (* Copying the initial state as the transient state *)
    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    (* both executions use a bind *)
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    (* We give Hσ to get a z1 *)
    iApply (wp2_z_of_argument with "[Hφ Hpc_a Hcred $Hσ]"). { set_solver. }
    (* wp2_z_of_argument introduces an existential (see shelved goals) *)
    (* and get back a new Hσ *)
    iSplit.
    { iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply AddSubLt_spec_failure.
      by constructor.
    }
    iIntros ( z1 ) "Hσ %Harg1L %Harg1".

    (* Same trick again *)
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_z_of_argument with "[Hφ Hpc_a Hcred $Hσ]"). { set_solver. }

    iSplit.
    { iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply AddSubLt_spec_failure.
      by constructor.
    }

    iIntros ( z2 ) "Hσ %Harg2L %Harg2".

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (k1 := fun x => Some x)).
    iApply wp_opt2_eqn_both.

    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LWInt (denote i z1 z2)) with "Hσ") as "Hσ".
    { set_solver. }
    { by cbn. }

    iApply (wp2_opt_incrementPC with "[$Hσ Hcred Hpc_a Hφ]").
    { now rewrite elem_of_dom (lookup_insert_dec HPC). }

    rewrite HdecodeLW; iSplit; cbn.
    - iIntros "Hσ %Heqn1 %Heqn2".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply AddSubLt_spec_failure.
      by constructor 3 with z1 z2.
    - iIntros (lrt' rs') "Hσ %Heqn1 %Heqn2".
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      by constructor 1 with z1 z2.
  Qed.

  (* Derived specifications *)

  Lemma wp_add_sub_lt_success_z_z E dst pc_p pc_b pc_e pc_a pc_v lw lwdst ins n1 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ dst ↦ᵣ lwdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite insert_commute // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_z E dst pc_p pc_b pc_e pc_a pc_v lw lwdst ins r1 n1 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r1 ↦ᵣ LInt n1
        ∗ dst ↦ᵣ lwdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ dst PC) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_z_r E dst pc_p pc_b pc_e pc_a pc_v lw wdst ins n1 r2 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r2 ↦ᵣ LInt n2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ dst PC) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_r E dst pc_p pc_b pc_e pc_a pc_v lw lwdst ins r1 n1 r2 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r1 ↦ᵣ LInt n1
        ∗ r2 ↦ᵣ LInt n2
        ∗ dst ↦ᵣ lwdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr1 & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_r_same E dst pc_p pc_b pc_e pc_a pc_v lw lwdst ins r n pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r) (inr r) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r ↦ᵣ LInt n
        ∗ dst ↦ᵣ lwdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r ↦ᵣ LInt n
          ∗ dst ↦ᵣ LInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_z E dst pc_p pc_b pc_e pc_a pc_v lw ins n1 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr dst) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ dst ↦ᵣ LInt n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_z_dst E dst pc_p pc_b pc_e pc_a pc_v lw ins n1 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inl n1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ dst ↦ᵣ LInt n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_r E dst pc_p pc_b pc_e pc_a pc_v lw ins n1 r2 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr dst) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r2 ↦ᵣ LInt n2
        ∗ dst ↦ᵣ LInt n1
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r2 ↦ᵣ LInt n2
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_r_dst E dst pc_p pc_b pc_e pc_a pc_v lw ins r1 n1 n2 pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ r1 ↦ᵣ LInt n1
        ∗ dst ↦ᵣ LInt n2
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ r1 ↦ᵣ LInt n1
          ∗ dst ↦ᵣ LInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_add_sub_lt_success_dst_dst E dst pc_p pc_b pc_e pc_a pc_v lw ins n pc_a' :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr dst) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->

    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ dst ↦ᵣ LInt n
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementLPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  (* Slightly generalized: fails in all cases where r2 does not contain an integer. *)
  Lemma wp_add_sub_lt_fail_z_r E ins dst n1 r2 lw lw2 lwdst pc_p pc_b pc_e pc_a pc_v :
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    is_zL lw2 = false →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗ (pc_a, pc_v) ↦ₐ lw ∗ dst ↦ᵣ lwdst ∗ r2 ↦ᵣ lw2 }}}
      Instr Executable
            @ E
    {{{ RET FailedV; (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hisnz φ) "(HPC & Hpc_a & Hdst & Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)  destruct lw2; simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_add_sub_lt_fail_r_r_1 E ins dst r1 r2 lw lwdst lw1 lw2 pc_p pc_b pc_e
    pc_a pc_v:
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    is_zL lw1 = false →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗ (pc_a, pc_v) ↦ₐ lw ∗ dst ↦ᵣ lwdst ∗ r1 ↦ᵣ lw1 ∗ r2 ↦ᵣ lw2 }}}
      Instr Executable
      @ E
    {{{ RET FailedV; (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hzf φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct lw1; by exfalso. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_add_sub_lt_fail_r_r_2 E ins dst r1 r2 lw lwdst lw2 lw3 pc_p pc_b pc_e
    pc_a pc_v:
    decodeInstrWL lw = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    is_zL lw3 = false →
    {{{ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗ (pc_a, pc_v) ↦ₐ lw ∗ dst ↦ᵣ lwdst ∗ r1 ↦ᵣ lw2 ∗ r2 ↦ᵣ lw3 }}}
      Instr Executable
      @ E
    {{{ RET FailedV; (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hzf φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct lw3; by exfalso. }
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
Lemma is_AddSubLt_Mod dst arg1 arg2 :
  is_AddSubLt (Mod dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_AddSubLt; eauto. Qed.
Lemma is_AddSubLt_HashConcat dst arg1 arg2 :
  is_AddSubLt (HashConcat dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_AddSubLt; eauto. Qed.

Global Hint Resolve is_AddSubLt_Add : core.
Global Hint Resolve is_AddSubLt_Sub : core.
Global Hint Resolve is_AddSubLt_Lt : core.
Global Hint Resolve is_AddSubLt_Mod : core.
Global Hint Resolve is_AddSubLt_HashConcat : core.
