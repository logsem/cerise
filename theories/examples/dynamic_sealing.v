From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone list malloc.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section sealing.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* Assume r_t1 contains a capability representing a sealed value.
     Get its b field, find the corresponding value in the linked list contained in r_env.
     Result is returned in r_t1; clear r_env for security and return. *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env *)
  Definition unseal_instrs :=
    encodeInstrsW [ GetB r_t1 r_t1 ]
                  ++ findb_instr ++
    encodeInstrsW [ Mov r_env (inl 0%Z)
                  ; Jmp r_t0
                  ].

  Definition unseal_instrs_length := Eval cbn in length (unseal_instrs).

  (* Assume r_t1 contains the word to seal.
     Append it to the linked list contained in r_env.
     Restrict the new capability to O permission.
     Subseg it, clear r_env and return *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env r_t2 *)
  Definition seal_instrs f_m :=
    appendb_instr f_m ++
    encodeInstrsW [ Restrict r_t1 (inl (encodePerm O))
                  ; GetB r_t2 r_t1
                  ; Subseg r_t1 r_t2 r_t2
                  ; Mov r_env (inl 0%Z)
                  ; Jmp r_t0
                  ].

  Definition seal_instrs_length := Eval cbn in length (seal_instrs 0%Z).

  (* Create two closures for sealing and unsealing assuming that their code is preceding this one *)
  (* This works by:
     1. Malloc an empty linked list, thus obtaining some capability c.
     2. Create a closure with access to c, and containing the code unseal_instr.
     3. Create a closure with access to c, and containing the code seal_instr.
     4. Return closure for unsealing in r_t1 and sealing in r_t2. *)
  (* Arguments: None
     Return point: rt_0
     Uses: r_t1 r_t2 r_t8 r_t9 r_t10 *)
  Definition make_seal_preamble f_m :=
    encodeInstrsW [ Mov r_t8 PC (* Copy PC into r_t8 *)
                  ; Lea r_t8 (- (Z.of_nat seal_instrs_length))%Z (* Capability pointing to code for seal_instrs *)
                  ]
    ++ malloc_instrs f_m 1 ++ (* Malloc an empty list *)
    encodeInstrsW [ Store r_t1 (inl 0%Z) (* Clear it *)
                  ; Mov r_t9 r_t1 (* Keep a copy of the capability to the list *)
                  ; Mov r_t2 r_t1 (* Prepare for creating closure, r_t2 must contain environment *)
                  ; Mov r_t1 r_t8 (* Prepare for creating closure, r_t1 must contain code *)
                  ]
    ++ crtcls_instrs f_m ++ (* Create the closure for seal, result in r_t1 *)
    encodeInstrsW [ Mov r_t10 r_t1 (* Closure for seal now in r_t10 *)
                  ; Lea r_t8 (- (Z.of_nat unseal_instrs_length))%Z (* Capability pointing to code for seal_instrs *)
                  ; Mov r_t1 r_t8 (* Prepare for creating closure for unseal, code *)
                  ; Mov r_t1 r_t9 (* Prepare for creating closure for unseal, environment *)
                  ]
    ++ crtcls_instrs f_m ++ (* Create the closure for unseal, result in r_t1 *)
    encodeInstrsW [ Mov r_t2 r_t10
                  ; Mov r_t8 (inl 0%Z) (* Clearing registers *)
                  ; Mov r_t9 (inl 0%Z)
                  ; Mov r_t10 (inl 0%Z)
                  ; Jmp r_t0 (* Return *)
                  ].

End sealing.
