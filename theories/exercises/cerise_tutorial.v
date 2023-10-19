(** This file is a tutorial to learn how to use the Cerise Program Logic within Coq.
    We will specify a simple program and explain how to use the tactics of the
    Cerise Proofmode to prove the specification.

    Prerequisites:
    We assume the user already knows how to use Iris and the Iris Proofmode,
    for instance with Heaplang. Learning material for Iris is available
    at this URL: https://iris-project.org/ *)

From iris.proofmode Require Import tactics.
From cap_machine Require Import rules macros_helpers proofmode.
From cap_machine Require Import contiguous.
Open Scope Z_scope.

(** The imports correspond to the following:
    - the Iris tactics and the Iris proofmode
    - the WP rules of the Cerise program logic
    - the automated tactics of the Cerise proofmode
    - some additional tactics for the Cerise proofmode

    We recommand to check the documentation of the proofmode of Cerise:
    https://github.com/logsem/cerise/blob/main/proofmode.md *)

Section base_program.
  (** Iris requires the ressources in the context. The resources of our machine
      are the registers and the memory. Moreover, we need the machine parameters
      in the context, which abstract the encoding and the decoding function
      (for instance, to encode the instructions). *)
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (** The program is a list of instructions. As the machine has a Von Neumann
      architecture, the instructions are encoded data. The function
      `encodeInstrsW` transforms a list of instructions into integers.
      The encoding does not matter, as we always manipulate the encoded
      instructions with the decoding function. *)

  (** The program we will study in this file moves a pointer in a buffer and
      stores a value at this new location. More precisely, we assumes that the
      register `r1` of the machine contains a capability pointing to a memory
      buffer of size >= 1. The program derives a capability to the next address,
      and stores the value of the register `r2` at this address. *)

  Definition prog_instrs : list Word :=
    encodeInstrsW [
      Lea r_t1 1;     (* load effective address 1 into `r1` *)
      Store r_t1 r_t2 (* store value from `r2` at address specified by `r1` *)
    ].

  (** We use the program logic to specify the program. In the program logic,
      there is 2 types of ressources:
      - the register /reg/ maps to the word /w/, reg ↦ᵣ w
      - the address /a/ maps to the word /w/, a ↦ₐ w.
      The notation [[a1, a2]] ↦ₐ [[lw]] maps the list of words /lw/ to the
      contiguous fragment of memory between the adresses /a1/ and /a2/.

      To write the specification, we need to have the separation logic
      assertion that describe all the resources required throughout the
      execution. In this case, we need the ownership of:
      - the fragment of the memory with the instructions of the program,
        stored between the adresses `a_prog` and `a_prog + len(prog)`
      - the memory buffer on which the program stores the new value,
        between the addresses `b_mem` and `b_mem + 2`
      - the PC contains a capability pointing to the first addresse of the
        program `a_prog`, with all the required permissions
        (i.e. validity range and executable)
      - the registers `r1` and `r2`, where `r1` contains the capability to the
        buffer and `r2` contains the new data (in our case, 42)

      The usual way to specify a program in Cerise in Coq is to use the
      weakest-precondition (WP) with a Continuation Passing Style, instead of
      the Hoare Triples.
      The CPS style is defined as follows:

      {P} e {Q} ≡ ∀ ϕ, (P ∗ ▷(Q -∗ WP e { ϕ })) -∗ WP e { ϕ }

      It is important to notice that, for a such low-level programming language,
      there is no notion of expression. The semantic only describes how the
      state of the machine changes at each execution step, as soon as the machine
      is in a Running state.
      However, the WP property requires an expression. In this way, an
      expression in the Cerise program logic encodes only the execution state of
      the machine (Running, Halted or Failed) (1).
      Thus, the WP rules only describes how the resources of the machine evolve
      at each execution step.


      (1) For technical purpose, an expression in actually either a (non-atomic)
          Sequence of instructions, or an (atomic) Instruction. *)

  (** The following lemma `prog_spec_instr` is a specification of the program
      previously defined.

      The SL assertion for the fragment of code is `codefrag a_prog prog_instr`.

      The PCC (PC Capability) has the permission `pc_p`, which has, at least,
      the execution permission: `ExecPCPerm p_pc`.
      The validity range of the PCC, between the addresses `pc_b` and `pc_e`,
      is larger than the actual range of the code fragment. Indeed, for
      modular purposes, the program we are specifying may be a part of a larger
      program. Thus, we need to ensure the fragment of the code is included in
      the PCC range, i.e. `SubBounds b_pc e_pc a_prog e_prog`.

      Because we work with addresses, which are actually finite integers,
      we need to assume the addresses are always valid when we do addresses
      arithmetic operations (for instance, there is no overflow of the memory).
      In particular, the memory buffer is a contiguous region of memory where
      all the addresses are in the bounds of the memory.

      For simplicity, we assume the buffer is filled with 0.

      When the whole program is a list of instructions, it is required to
      manually get some helping facts before reasoning on the instructions,
      using the tactic `codefrag_facts "Hprog"`. This tactic has to be used
      when the `codefrag` assertion is used. It allows to get some additionnal
      facts about the memory addresses containing the code. It is a boilerplate.

      To prove the specification, the idea is to manipulate the resources, such
      that we have all the required assertion that fit with the corresponding
      WP rule. Once all the resource are ready, the tactic `iInstr "Hprog"`
      steps through one instruction, automatically finds the appropriate rule,
      and tries to discharge as much goal as possible (e.g. side-condition
      about the PC). It only remains some side-condition to prove manually,
      such as address arithmetic.
      We can use the tactic `solve_addr` to solve automatically the address
      arithmetic goals. It sometimes requires to transform the goal or
      hypotheses a bit to work.

      We advice to read carefully the following specification and to try to
      understand each statement in the lemma.
      Then, we urge to execute the proof step by step, and to understand
      each time what happens to the proof state and why we are doing it. *)

  Lemma prog_spec_instr
    p_pc b_pc e_pc a_prog (* pc *)
    b_mem (* mem *)
    φ :

    let e_mem := (b_mem ^+ 2)%a in (* end of memory buffer at b_mem + 2 *)
    let e_prog := (a_prog ^+ length prog_instrs)%a in (* end of program at a_prog + length of instructions *)

    ExecPCPerm p_pc → (* p_pc has at least the executable permission*)
    SubBounds b_pc e_pc a_prog e_prog → (* [b_pc : e_pc) contains [a_prog : e_prog) *)
    ContiguousRegion b_mem 2 → (* addresses in [b_mem : b_mem + 2) are valid *)

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog (* PC points to the prog *)
        ∗ codefrag a_prog prog_instrs (* the prog instruction start at a_prog *)
        ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem b_mem (* r1 points to the allocated memory *)
        ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 0] ]] (* memory buffer, filled with 0 *)
        ∗ r_t2 ↦ᵣ WInt 42 (* new value 42 *)
         ∗ ▷ ( (* everything under the later `▷` and before the wand `-*` is our postcondition *)
                PC ↦ᵣ WCap p_pc b_pc e_pc e_prog (* PC has reached the end of the program *)
                ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem (b_mem ^+ 1)%a (* r1 points to b_mem + 1*)
                ∗ r_t2 ↦ᵣ WInt 42 (* unchanged *)
                ∗ codefrag a_prog prog_instrs (* unchanged *)
                ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 42] ]] (* our memory buffer now contains 42 *)
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hmem_bounds.
    unfold ContiguousRegion in Hmem_bounds.

    iIntros "(HPC & Hprog & Hr1 & Hmem & Hr2 & Hcont)".

    (* 1 - prepare the assertions for the proof *)
    subst e_mem e_prog. (* replace e_mem and e_prog with their known values *)
    codefrag_facts "Hprog". (* Derives the facts from the codefrag *)
    simpl in *.

    (* 2 - wp rules for each instructions *)
    (* Lea *)
    iInstr "Hprog".

    (* Store requires the resource (b_mem ^+ 1), we need to destruct the region_mapsto.
       This essentially the same as destructing a list into (first element)::(rest of list). *)
    iDestruct (region_mapsto_cons with "Hmem") as "(Hmem0 & Hmem1)".
    { (* We simplify the subgoal first *)
      transitivity (Some (b_mem ^+ 1)%a).
      2: reflexivity.

      (* This inequality holds if the address (b_mem + 1) is in memory *)
      (* The hypothesis `Hmem_bounds` ensures that (b_mem + 2) is in memory, so (b_mem + 1) too *)
      solve_addr +Hmem_bounds. (* `solve_addr` is invoked with the "required" environment + `Hmem_bounds` *)
    }
    { solve_addr +. (* `solve_addr` is invoked with only the "required" environment *) }

    (* We do it twice since we need the second element (b_mem ^+ 1). *)
    iDestruct (region_mapsto_cons with "Hmem1") as "(Hmem1 & _)".
    { transitivity (Some (b_mem ^+ (1 + 1))%a); [ solve_addr +Hmem_bounds | reflexivity ]. }
    { solve_addr +. }

    (* Store *)
    iInstr "Hprog".

    (* 3 - Continuation *)
    iApply "Hcont".

    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+ 1)%a); solve_addr +Hmem_bounds. }
    { solve_addr +. }

    iFrame.
    iApply region_mapsto_cons.
    { transitivity (Some (b_mem ^+ (1 + 1))%a); solve_addr +Hmem_bounds. }
    { solve_addr +. }

    iFrame.
    replace (b_mem ^+ (1 + 1))%a with (b_mem ^+ 2)%a by solve_addr +.

    unfold region_mapsto.
    rewrite finz_seq_between_empty.
    { simpl; iPureIntro. exact I. }
    { solve_addr +. }
  Qed.


  (** The tactic `iGo "Hprog"` steps through multiple instructions,
     until a side-condition needs to be prove manually. *)

  (** **** Exercise 1 --- More automation with iGo
      Prove the specification of the previous example using the automated
      tactic `iGo`. In order to leverage the strengh of the tactic, the memory
      resources should be ready before the execution of the tactic, in
      particular, the memory buffer should be split at the beginning of the
      proof: it will allows the tactic `iGo` to step through multiple
      instructions at once.

      Tips: take inspiration on the proof of the previous exercise, but we
            recommend to try to manipulate the SL resources and the address
            arithmetic by yourself.
            Indeed, address arithmetic is a very common side-condition,
            and the lemmas often require you to manipulate the PL resources
            in order to make them fit with the hypothesis. *)

  Lemma prog_spec_igo
    p_pc b_pc e_pc a_prog (* pc *)
    b_mem (* mem *)
    φ :

    let e_mem := (b_mem ^+ 2)%a in
    let e_prog := (a_prog ^+ length prog_instrs)%a in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_prog e_prog →
    ContiguousRegion b_mem 2 →

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ codefrag a_prog prog_instrs
        ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem b_mem
        ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 0] ]]
        ∗ r_t2 ↦ᵣ WInt 42
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
                ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem (b_mem ^+ 1)%a
                ∗ r_t2 ↦ᵣ WInt 42
                ∗ codefrag a_prog prog_instrs
                ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 42] ]]
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hmem_bounds.
    unfold ContiguousRegion in Hmem_bounds.

    iIntros "(HPC & Hprog & Hr1 & Hmem & Hr2 & Hcont)".
    subst e_mem e_prog.
    codefrag_facts "Hprog"; simpl in *.

    (* Prepare the memory resource for the Store *)
    iDestruct (region_mapsto_cons with "Hmem") as "(Hmem0 & Hmem1)".
    { transitivity (Some (b_mem ^+ 1)%a); solve_addr +Hmem_bounds. }
    { solve_addr +. }

    iDestruct (region_mapsto_single with "Hmem1") as "Hmem1".
    { transitivity (Some (b_mem ^+ (1 + 1))%a); solve_addr +Hmem_bounds. }

    iDestruct "Hmem1" as (v) "(Hmem1 & %Hr)".
    injection Hr as <-. (* `Hmem1` is now pointing to `WInt 0` *)

    (* 2 - step through multiple instructions *)
    (* FILL IN HERE *)

    (* 3 - Continuation *)
    (* FILL IN HERE *)
  Admitted.


  (** The tactics `iInstr` and `iGo` automatically lookup the PC, find the
      corresponding instruction in the `codefrag` instruction, find the
      right WP rule to apply accordingly with the instruction, instantiate
      the lemma and try to prove as much precondition as possible.

      However, in order to get a better understanding of the way to use the
      WP rules in Cerise, we propose to prove the previous lemma using the
      fully detailed tactics.
      It is also useful if the assertion that embeds the code is not the
      `codefrag` predicate, but for instance, the big conjonction separation
      `[∗ list]` --- even though it is usually possible to rewrite the one
      in term of the other. *)

  (** **** Exercise 2 --- Manual detailled proofs
        For this exercise, we propose to re-do the proof of the previous
        specification, using the manual WP rules.
        We explain the different steps for the first instruction `Lea`.
        Complete the proof.
   *)

  Lemma prog_spec_detailed
    p_pc b_pc e_pc (* pc *)
    a_prog a
    b_mem (* mem *)
    φ :

    let e_mem := (b_mem ^+ 2)%a in
    let e_prog := (a_prog ^+ length prog_instrs)%a in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_prog e_prog →
    contiguous_between a a_prog (e_prog) →
    ContiguousRegion b_mem 2 →

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ ([∗ list] a_i;w ∈ a;prog_instrs, a_i ↦ₐ w)%I
        ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem b_mem
        ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 0] ]]
        ∗ r_t2 ↦ᵣ WInt 42
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
                ∗ r_t1 ↦ᵣ WCap RW b_mem e_mem (b_mem ^+ 1)%a
                ∗ r_t2 ↦ᵣ WInt 42
               ∗ ([∗ list] a_i;w ∈ a;prog_instrs, a_i ↦ₐ w)%I
                ∗ [[b_mem, e_mem]] ↦ₐ [[ [WInt 0; WInt 42] ]]
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hprog_addr Hmem_bounds.
    iIntros "(HPC & Hprog & Hr1 & Hmem & Hr2 & Hcont)".
    subst e_mem e_prog; simpl in *.

    (* In order to use the tactic `iCorrectPC` that solves the side-condition
       about the PC, we need this assertion, equivalent to
       `Hpc_perm /\ Hpc_bounds` *)
    assert (Hpc_correct : isCorrectPC_range p_pc b_pc e_pc a_prog (a_prog ^+ 2)%a).
    { unfold isCorrectPC_range.
      intros.
      apply isCorrectPC_ExecPCPerm_InBounds.
      - assumption.
      - solve_addr +H Hpc_bounds.
    }

    (* 2 - step through instructions *)

    (* 2.1 - Lea *)
    (* Prepare the resources: Destruct the list of addresses of the code fragment *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct_list a.
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hprog_addr) as ->.

    (* Focus to the atomic expression (regarding the operational semantic) *)
    iDestruct "Hprog" as "[Hi Hprog]".

    (* Apply the WP rule corresponding to the instruction
       and prove the preconditions of the rule *)
    iApply (wp_bind (fill [SeqCtx])); iSimpl.
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]").
    { apply decode_encode_instrW_inv. }
    { iCorrectPC a_prog (a_prog ^+ 2)%a. }
    { iContiguous_next Hprog_addr 0%nat. }
    { unfold ContiguousRegion in Hmem_bounds.
      transitivity (Some (b_mem ^+ 1)%a); solve_addr +Hmem_bounds. }
    { auto. }

    (* Introduce the postconditions of the rule and re-focus the expression. *)
    iNext; iIntros "(HPC & Hdone & Hr1)"; iSimpl.
    iApply wp_pure_step_later; [ exact I |].
    iIntros "!> _".

    (* 2.2 - Store *)
    (* Destruct the list of addresses of the code fragment *)
    pose proof (contiguous_between_last _ _ _ a Hprog_addr eq_refl) as Hlast.

    (* Prepare the memory resource for the Store *)
    (* FILL IN HERE *)

    (* Focus to the atomic expression (regarding the operational semantic) *)
    (* FILL IN HERE *)

    (* Apply the WP rule corresponding to the instruction
       and prove the preconditions of the rule *)
    (* FILL IN HERE *)

    (* Introduce the postconditions of the rule and re-focus the expression. *)
    (* FILL IN HERE *)

    (* 3 - Continuation *)
    (* FILL IN HERE *)
  Admitted.


  (** The next step to learn how to use the Cerise Proofmode is to leverage
      the modularity of program logic to define macros and use their
      specification inside bigger programs.
      The next part of the tutorial "cerise_modularity.v" will learn you how
      to define, specify and use user-defined macros, and present you the main
      macros already defined in Cerise.
   *)

End base_program.
