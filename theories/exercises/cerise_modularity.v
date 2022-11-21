(** This file is a tutorial to learn how to use the Cerise Program Logic within Coq.
    We will use the modularity of the program logic to use the specification of
    a macro in a program, and show how the macro can be linked via a linking table.

    Prerequisites:
    We assume the user has already followed the first part of the tutorial
    "cerise_tutorial.v" and is able to prove the specification of a program
    with known code using the Cerise Proof Mode. *)

From iris.proofmode Require Import tactics.
From cap_machine Require Import rules proofmode macros_new macros_helpers.
Open Scope Z_scope.

Section increment_macro.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (** The increment macro is a macro that takes a register r (r ≠ r_env), which
      contains a capability C with a permission p ≤ RW, that points to
      an integer n. The macro increments the value of the integer.
      The macro uses the register r_env to perform the arithmetic, and clear
      the result of the register.
   *)
  Definition incr_instrs r r_env : list Word :=
    encodeInstrsW [
      Load r_env r ;
      Add r_env r_env 1;
      Store r r_env;
      Mov r_env 0 ].

  (** Specification of the macro. The proof is an optional exercise. *)
  Lemma incr_macro_spec
    p_pc b_pc e_pc a_prog (* pc *)
    r r_env (* registers of the macro *)
    p (e b a : Addr) n (* capability *)
    w_env
    φ :

    let e_prog := (a_prog ^+ length (incr_instrs r r_env))%a in
    r <> r_env ->

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog e_prog ->

    b <= a < e -> (* a is in the bounds of the capability *)
    writeAllowed p = true -> (* p can Read/Write *)

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog (* PC points to the prog*)
        ∗ codefrag a_prog (incr_instrs r r_env) (* the prog instruction start at a_prog *)
        ∗ r ↦ᵣ WCap p b e a (* r contains the capability *)
        ∗ r_env ↦ᵣ w_env (* ownership of r_env *)
        ∗ a ↦ₐ WInt n (* content of a, which is an integer *)
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r ↦ᵣ WCap p b e a
               ∗ r_env ↦ᵣ WInt 0 (* cleared register *)
               ∗ a ↦ₐ WInt (n+1) (* incremented value *)
                ∗ codefrag a_prog (incr_instrs r r_env)
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  (* FILL IN HERE *)
  Admitted.

  (** The increment macro is just a list of instructions. In particular,
      it can be used as a part of a bigger list of instructions.
      The specification assumes that the PCC points to the first address of the
      macro, and the list of instructions is _included_ into the bounds of the
      PCC: thus, the specification can be used in the proof of the specification
      of a bigger program.

      The macros are a way to define the program modularly.
      For such short macro, the modularity is a bit "too much", but dealing
      with larger and complex macros (e.g. involving a loop), this modularity
      is necessary. *)

  (** The following is a very simple example of program that uses the macro. The
        program assumes that R0 contains a writing capability pointing to the
        memory. It initializes the value of this memory address at 0, calls the
        increment macro to increment the value, and finally loads the
        incremented value in the register R1.

      The reader may notice 3 blocks of instructions, separated by the `++`
      operator. The proof will leverage this block separation using new
      `focus_block` tactics, detailled in `proofmode.md`, section `Focusing a
      sub-block`. They allow us to focus on a block, prove its specification
      locally, and then continue the proof of the global program.
      *)
  Definition prog_instrs: list Word :=
    encodeInstrsW [Store r_t0 0 ] ++
            incr_instrs r_t0 r_t1 ++
            encodeInstrsW [Load r_t1 r_t0 ].


  Lemma prog_spec
    p_pc b_pc e_pc a_prog (* pc *)
    p (e b a : Addr) w (* capability *)
    w_env
    φ :

    let e_prog := (a_prog ^+ length prog_instrs)%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog e_prog ->

    b <= a < e -> (* a is in the bounds of the capability *)
    writeAllowed p = true -> (* p can Read/Write *)

    ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog (* PC points to the prog *)
        ∗ codefrag a_prog prog_instrs (* the prog instruction start at a_prog *)
        ∗ r_t0 ↦ᵣ WCap p b e a (* r_t0 contains the capability *)
        ∗ r_t1 ↦ᵣ w_env (* ownership of r_t1 *)
        ∗ a ↦ₐ w (* content of a *)
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r_t0 ↦ᵣ WCap p b e a (* r_t0 contains the capability *)
               ∗ r_t1 ↦ᵣ WInt 1 (* ownership of r_t1 *)
               ∗ a ↦ₐ WInt 1 (* incremented value *)
               ∗ codefrag a_prog prog_instrs
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  intros * Hpc_perm Hpc_bounds Ha_bounds Hperm.
  iIntros "(HPC& Hprog& Hr& Hrenv& Ha& Hcont)".

  (* 1 - prepare the assertions for the proof *)
  subst e_prog; simpl.
  (* Derives the facts from the codefrag *)
  simpl in *.
  (* We use the new tactic to focus on the first block. *)
  (* Initialisation block *)
  focus_block_0 "Hprog" as "Hintro" "Hnext".
  iInstr "Hintro";[by rewrite withinBounds_true_iff|].
  unfocus_block "Hintro" "Hnext" as "Hprog".

  (* Increment macro *)
  focus_block 1%nat "Hprog" as a_incr Ha_incr "Hincr" "Hnext".
  (* We use the specification of the macro. *)
  iApply (incr_macro_spec with "[- $HPC $Hincr $Hr $Hrenv $Ha]");eauto.
  iNext; iIntros "(HPC &Hr &Hrenv &Ha &Hincr)".
  unfocus_block "Hincr" "Hnext" as "Hprog".

  focus_block 2%nat "Hprog" as a_end Ha_end "Hend" "Hnext".
  iGo "Hend".
  { split. apply writeA_implies_readA; done. by rewrite withinBounds_true_iff.  }
  unfocus_block "Hend" "Hnext" as "Hprog".

  (* 3 - continuation *)
  iApply "Hcont".
  simpl in *.
  replace (a_end ^+1)%a with (a_prog ^+ 6%nat)%a by solve_addr.
  iFrame.
  Qed.
End increment_macro.

Section rclear_macro.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (** In this section, we will use a pre-defined macro in Cerise, `rclear`.
      `rclear` is a macro that clears (puts 0) the list of registers given as
      argument. *)

  (** The following program assumes that the register r0 contains a capability
      that points to a buffer with at least 2 integers.
      It performs the addition of the 2 integers of the buffer and stores the
      result at the address of the second integer.
      Then, it clears all the used registers (to remove every trace of
      the computations) and halts the machine. *)
  Definition secret_add_instrs: list Word :=
    encodeInstrsW
            [Load r_t1 r_t0;
             Lea r_t0 1;
             Load r_t2 r_t0;
             Add r_t1 r_t1 r_t2;
             Store r_t0 r_t1
            ] ++
            rclear_instrs [r_t0;r_t1;r_t2] ++
            encodeInstrsW [Halt].

  (** **** Exercise 3 --- Secret addition
        Define the lemma `secret_add_spec` that specifies the program
        `secret_add_instrs` and prove it.

        Use the tactics to focus and unfocus the block.
        The specification of the `rclear` macro is `rclear_spec`,
        defined in the file `theories/examples/macros_new.v`.

        Hint (specification): TODO ???
        Hint (proof): The specification of `rclear` requires the use of
        the `big_sepM` resource. The `big_sepM` resource [...] use a map.
        We urge the reader to search lemmas about `big_sepM` and
        `gmap`.

        Hint (proof): useful lemmas
        - big_sepM_insert
        - big_sepM_insert_delete
        - delete_insert_ne
        - delete_empty
   *)

End rclear_macro.

Section linking_table.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* Demo with incr_macro for the setup *)

  (* Exercices using malloc and assert *)

End linking_table.


  (** Outline
    2 steps:
    1. use the macro in the middle of the code (as a real macro)
    2. capture the macro into a sentry-capability (as a function), and use a linking table

    1.1) Demo
    Define a program that use this specification that do the following:
    - takes a capability input
    - store 0 into it
    - use the increment macro

    1.2) Exercise
    Exercise with the rclear macro: specify and prove

    2.1) Demo
    Same program as 1.1, but the increment macro is reachable via
    the linking table (instead of inlined).
    It requires some boilerplate about the linking table and shows
    how to set it up.

    2.2) Exercise
    At last exercise, the reader should be able to use the Cerise macros,
    so why not a program that does the following:
    - dyn alloc a region of memory with malloc
    - stores 42 in the last adresse
    - assert it is 42

    Finally, list the macros available in Cerise *)


  (** Now that you are familiar with the Cerise Proofmode,
      we recommand to try defining a program by yourself, as
      well as its specification.
      We also recommand to continue the tutorial with
      TODO (next file) to learn how to define the specification,
      how to use the logical relation to reason with unknown code,
      and how to deal with local encapsulation, using the call macro.
   *)
