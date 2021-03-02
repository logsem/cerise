From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import list_new dynamic_sealing.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section interval.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* interval := λ_, let (seal,unseal) = makeseal () in
                     let makeint = λ n1 n2, seal (if n1 ≤ n2 then (n1,n2) else (n2,n1)) in
                     let imin = λ i, fst (unseal i) in
                     let imax = λ i, snd (unseal i) in
                     let isum = λ i, let x = unseal i in
                                     λ j, let y = unseal j in
                                          seal (fst x + fst y, snd x + snd y) in
                     (makeint, imin, imax, isum)
   *)

  Definition fst_instrs r :=
    encodeInstrsW [ GetB r_t1 r;
                  Lea r (inr r_t1);
                  Load r_t1 r ].

  Definition snd_instrs r :=
    encodeInstrsW [ GetB r_t1 r;
                  Add r_t1 (inr r_t1) (inl 1%Z);
                  Lea r (inr r_t1);
                  Load r_t1 r ].

  Definition interval_inv a1 a2 n1 n2 : iProp Σ :=
    ⌜(a1 + 1)%a = Some a2 ∧ (n1 ≤ n2)%Z⌝
    ∗ a1 ↦ₐ inl n1
    ∗ a2 ↦ₐ inl n2.

  (* r_t1 ↦ inl n1 ∗ r_t2 ↦ inl n2 -> otherwise the program fails *)
  (* r_env ↦ (RWX, b, b + 2, b)
     ∗ b ↦ seal activation E cap
     ∗ b + 1 ↦ unseal activation E cap *)
  Definition makeint f_m :=
    encodeInstrsW [ Load r_env r_env
                    ; Mov r_t6 r_t1
                    ; Mov r_t7 r_t2 (* move the n1 n2 parameters to make place for malloc *)
                  ] ++ malloc_instrs f_m 2%nat ++ (* allocate a region of size 2 for the interval pair *)
    encodeInstrsW [ Lt r_t2 r_t6 r_t7 (* check whether n1 < n2, this instruction fails if they are not ints *)
                    ; Mov r_t3 PC
                    ; Lea r_t3 6
                    ; Jnz r_t3 r_t2 (* if n2 ≤ n1, we must swap r6 and r7 *)
                    ; Mov r_t3 r_t6
                    ; Mov r_t6 r_t7
                    ; Mov r_t7 r_t3
                    ; Store r_t1 (inr r_t6) (* store min (n1 n2) into the lower bound, and max (n1 n2) into the upper bound *)
                    ; Lea r_t1 (1%Z)
                    ; Store r_t1 (inr r_t7)
                    ; Jmp r_env (* jmp to the seal function closure in r_env *)].
  (* the seal subroutine does the clearing, and will jump to r_t0 when done *)

  (* r_t1 must be a sealed interval *)
  Definition imin :=
    encodeInstrsW [ Lea r_env 1
                    ; Load r_env r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t2 r_t1]
                  ++ fst_instrs r_t2 ++
    encodeInstrsW [Jmp r_t0].

  Definition imax :=
    encodeInstrsW [ Lea r_env 1
                    ; Load r_env r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t2 r_t1]
                  ++ snd_instrs r_t2 ++
    encodeInstrsW [Jmp r_t0].

  Definition isum f_m :=
    encodeInstrsW [ Mov r_t6 r_env
                    ; Mov r_t7 r_t2
                    ; Lea r_t6 1
                    ; Load r_env r_t6
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t8 r_t1 (* r_t8 contains the first interval i *)
                    ; Mov r_t1 r_t7
                    ; Load r_env r_t6
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t0 r_t5
                    ; Mov r_t9 r_t1] (* r_t9 contains the second interval j *)
                  ++ fst_instrs r_t8 ++ encodeInstrsW [Mov r_t2 r_t1] ++ fst_instrs r_t9
                  ++ encodeInstrsW [Add r_t3 r_t1 r_t2]
                  ++ snd_instrs r_t8 ++ encodeInstrsW [Mov r_t2 r_t1] ++ fst_instrs r_t9 ++
    encodeInstrsW [ Add r_t2 r_t1 r_t2
                    ; Mov r_t1 r_t3
                    ; Mov r_env r_t6]
                  ++ makeint f_m.

End interval.
