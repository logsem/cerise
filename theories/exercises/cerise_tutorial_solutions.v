(** This file is a tutorial to learn how to use the Cerise program logic in Coq.
    We will specify a simple program and explain the tactic to use to prove the
    specification.
    We assume the user already knows how to use Iris, for instance with Heaplang.
 *)

From iris.proofmode Require Import tactics.
From cap_machine Require Import rules proofmode macros_helpers.
Open Scope Z_scope.

Section base_program.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Definition prog_instrs : list Word :=
    encodeInstrsW [
      Lea r_t1 1 ;
      Store r_t1 r_t2 ].

  (** **** Exercise 1 - More automation with iGo
      Prove the specification of the previous example using the automated
      tactic iGo. In order to leverage the strengh of the tactic, the memory
      resources should be ready before the execution of the tactic, in
      particular, the memory buffer should be splitted at the beginning of the
      proof: it will allows the tactic `iGo` to step through multiple
      instructions at once.

      Tips: take inspiration on the proof of the previous exercise, but I
            recommend to try to manipulate the SL resources and the adresses
            arithmetic by yourself.
            Indeed, adresses arithmetic is a very common side-condition,
            and the lemmas often requires you to manipulate the resources
            in order to make them fit with the hypethesis. *)

  Lemma prog_spec_igo
    p_pc b_pc e_pc a_prog (* pc *)
    b_mem (* mem *)
    φ :

    let e_mem := (b_mem ^+ 2)%a in
    let e_prog := (a_prog ^+ length prog_instrs)%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog e_prog ->
    ContiguousRegion b_mem 2 →

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ codefrag a_prog prog_instrs
        ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem b_mem
        ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 0] ]]
        ∗ r_t2 ↦ᵣ WInt 42
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
                ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem (b_mem ^+1)%a
                ∗ r_t2 ↦ᵣ WInt 42
                ∗ codefrag a_prog prog_instrs
                ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 42] ]]
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hmem_bounds.
    unfold ContiguousRegion in Hmem_bounds.
    iIntros "(HPC& Hprog& Hr1& Hmem& Hr2& Hcont)".
    subst e_mem e_prog; simpl.

    (* Derives the facts from the codefrag *)
    codefrag_facts "Hprog".
    simpl in *.

    (* Prepare the memory resource for the Store *)
    iDestruct (region_mapsto_cons with "Hmem") as "(Hmem0& Hmem1)".
    { transitivity (Some (b_mem ^+1)%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iDestruct (region_mapsto_single with "Hmem1") as "Hmem1".
    { transitivity (Some (b_mem ^+(1+1))%a) ; auto ; by solve_addr. }
    iDestruct "Hmem1" as (v) "(Hmem1& %Hr)".
    injection Hr ; intro Hr' ; subst ; clear Hr.

    (* 2 - step through multiple instructions *)
    iGo "Hprog".

    (* 3 - Continuation *)
    iApply "Hcont".
    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+1)%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+(1+1))%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iFrame.
    replace (b_mem ^+ (1 + 1))%a with (b_mem ^+ 2)%a by solve_addr.
    unfold region_mapsto.
    rewrite finz_seq_between_empty ; last solve_addr.
    done.
  Qed.

  (** **** Exercise 2 --- Manual detailled proofs
        For this exercise, we propose to re-do the proof of the previous
        specification, using the manual WP rules.
        We explain the different steps for the first instruction `Lea`.
        Complete the proof, for the instruction `Store` and the
        postcondition.
   *)

  Lemma prog_spec_detailed
    p_pc b_pc e_pc (* pc *)
    a_prog a
    b_mem (* mem *)
    φ :

    let e_mem := (b_mem ^+ 2)%a in
    let e_prog := (a_prog ^+ length prog_instrs)%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog e_prog ->
    contiguous_between a a_prog (e_prog) →
    ContiguousRegion b_mem 2 →

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ ([∗ list] a_i;w ∈ a;prog_instrs, a_i ↦ₐ w)%I
        ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem b_mem
        ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 0] ]]
        ∗ r_t2 ↦ᵣ WInt 42
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
                ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem (b_mem ^+1)%a
                ∗ r_t2 ↦ᵣ WInt 42
               ∗ ([∗ list] a_i;w ∈ a;prog_instrs, a_i ↦ₐ w)%I
                ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 42] ]]
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hprog_addr Hmem_bounds.
    iIntros "(HPC& Hprog& Hr1& Hmem& Hr2& Hcont)".
    subst e_mem e_prog; simpl in *.
    (* In order to use the tactic `iCorrectPC` that solve the side-condition
       about the PC, we need this assertion, equivalent to
       `Hpc_perm /\ Hpc_bounds` *)
    assert (Hpc_correct : isCorrectPC_range p_pc b_pc e_pc a_prog (a_prog ^+ 2)%a).
    { unfold isCorrectPC_range. intros.
      apply isCorrectPC_ExecPCPerm_InBounds ; auto ; solve_addr.
    }


    (* Lea *)
    (* Prepare the resources
       Destruct the list of addresses of the code fragment *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct_list a.
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hprog_addr) as ->.
    (* Focus to the atomic expression (regarding the operational semantic) *)
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    (* Apply the WP rule corresponding to the instruction
       and prove the preconditions of the rule *)
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]").
    { apply decode_encode_instrW_inv. }
    { iCorrectPC a_prog (a_prog ^+ 2)%a. }
    { iContiguous_next Hprog_addr 0. }
    { transitivity (Some (b_mem ^+ 1 )%a) ; auto ; solve_addr. }
    { auto. }
    (* Introduce the postconditions of the rule and re-focus the expression. *)
    iNext; iIntros "(HPC& Hdone& Hr1)"; iSimpl.
    iApply wp_pure_step_later;auto;iNext.

    (* Lea *)
    (* Destruct the list of addresses of the code fragment *)
    pose proof (contiguous_between_last _ _ _ a Hprog_addr eq_refl) as Hlast.

    (* Prepare the memory resource for the Store *)
    iDestruct (region_mapsto_cons with "Hmem") as "(Hmem0& Hmem1)".
    { transitivity (Some (b_mem ^+1)%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iDestruct (region_mapsto_single with "Hmem1") as "Hmem1".
    { transitivity (Some (b_mem ^+(1+1))%a) ; auto ; by solve_addr. }
    iDestruct "Hmem1" as (v) "(Hmem1& %Hr)".
    injection Hr ; intro Hr' ; subst ; clear Hr.

    (* Focus to the atomic expression (regarding the operational semantic) *)
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (wp_bind (fill [SeqCtx])).

    (* Apply the WP rule corresponding to the instruction
       and prove the preconditions of the rule *)
    iApply (wp_store_success_reg with "[$HPC $Hi $Hmem1 $Hr2 $Hr1]").
    { apply decode_encode_instrW_inv. }
    { iCorrectPC a_prog (a_prog ^+ 2)%a. }
    { eauto. }
    { eauto. }
    { apply le_addr_withinBounds; solve_addr. }

    (* Introduce the postconditions of the rule and re-focus the expression. *)
    iNext; iIntros "(HPC& Hi& Hr2& Hr1& Hmem1 )"; iSimpl.
    iCombine "Hdone Hi" as "Hdone". iApply wp_pure_step_later;auto;iNext.

    (* 3 - Continuation *)
    iApply "Hcont".
    iDestruct "Hdone" as "[? ?]".
    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+1)%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+(1+1))%a) ; auto ; by solve_addr.  }
    { by solve_addr. }
    iFrame.
    replace (b_mem ^+ (1 + 1))%a with (b_mem ^+ 2)%a by solve_addr.
    unfold region_mapsto.
    rewrite finz_seq_between_empty ; last solve_addr.
    done.
  Qed.

End base_program.
