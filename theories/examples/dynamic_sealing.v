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
     Uses: r_env r_t4 (r_t2 rt_3 are used by findb) *)
  Definition unseal_instrs :=
    encodeInstrsW [ GetB r_t1 r_t1
                  ; Mov r_t4 (inr r_t0) (* Save return point *)
                  ; Mov r_t0 (inr PC) (* Setup the return point for findb *)
                  ; Lea r_t0 (inl (length findb_instr + 1)%Z)
                  ; Load r_env r_env (* Need this to use findb_spec ?? *)
                  ] ++ findb_instr ++
    encodeInstrsW [ Mov r_env (inl 0%Z) (* Clearing *)
                  ; Mov r_t0 (inr r_t4) (* Restore return capability *)
                  ; Mov r_t4 (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition unseal_instrs_length := Eval cbn in length (unseal_instrs).
  Definition unseal ai :=
    ([∗ list] a_i;w_i ∈ ai;unseal_instrs, a_i ↦ₐ w_i)%I.

  (* Assume r_t1 contains the word to seal.
     Append it to the linked list contained in r_env.
     Restrict the new capability to O permission.
     Subseg it, clear r_env and return *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env r_t2 r_t7 (r_t3 r_t4 r_t5 r_t6 used by appendb) *)
  Definition seal_instrs f_m :=
    encodeInstrsW [ Mov r_t7 (inr r_t0) (* Save return point *)
                  ; Mov r_t0 (inr PC) (* Setup the return point for findb *)
                  ; Lea r_t0 (inl (Zlength (appendb_instr f_m)))
                  ] ++ appendb_instr f_m ++
    encodeInstrsW [ Restrict r_t1 (inl (encodePerm O))
                  ; GetB r_t2 r_t1
                  ; Subseg r_t1 r_t2 r_t2
                  ; Mov r_env (inl 0%Z) (* Clearing *)
                  ; Mov r_t0 (inr r_t7) (* Restore return capability *)
                  ; Mov r_t7 (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition seal_instrs_length := Eval cbn in length (seal_instrs 0%Z).
  Definition seal f_m ai :=
    ([∗ list] a_i;w_i ∈ ai;(seal_instrs f_m), a_i ↦ₐ w_i)%I.

  (* Create two closures for sealing and unsealing assuming that their code is preceding this one.
     Specifically, we assume the memory layout is [unseal_instrs][seal_instrs][make_seal_preamble] *)
  (* This works by:
     1. Malloc an empty linked list, thus obtaining some capability c.
     2. Create a closure with access to c, and containing the code unseal_instr.
     3. Create a closure with access to c, and containing the code seal_instr.
     4. Return closure for unsealing in r_t1 and sealing in r_t2. *)
  (* Arguments: None
     Return point: rt_0
     Uses: r_t1 r_t2 r_t8 r_t9 r_t10 *)
  Definition make_seal_preamble_instrs f_m :=
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
                  ; Lea r_t8 (inl (- (Z.of_nat unseal_instrs_length))%Z) (* Capability pointing to code for seal_instrs *)
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

  Definition make_seal_preamble f_m ai :=
    ([∗ list] a_i;w_i ∈ ai;(make_seal_preamble_instrs f_m), a_i ↦ₐ w_i)%I.

  Lemma unseal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        p b e a (* input cap *)
        unseal_addrs (* program addresses *)
        ll ll' (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        ι ι1 γ φ (* invariant/gname names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between unseal_addrs a_first a_last ->

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ ⊤ ∖ ↑ι1 →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
      ∗ r_t1 ↦ᵣ inr (p, b, e, a)
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      ∗ (∃ w, r_t4 ↦ᵣ w)
      (* invariant for d *)
      ∗ sealLL ι ll γ
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (unseal unseal_addrs)
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ inl 0%Z
          ∗ (∃ b' w pbvals, ⌜(b + 2)%a = Some b' ∧ (b,w) ∈ pbvals⌝ ∗ prefLL γ pbvals ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ inl 0%Z)
          ∗ r_t3 ↦ᵣ inl 0%Z
          ∗ r_t4 ↦ᵣ inl 0%Z
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
  Admitted.

  Lemma seal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w (* input z *)
        seal_addrs (* program addresses *)
        ll ll' pbvals (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 ι2 γ Ep φ (* invariant/gname names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between seal_addrs a_first a_last ->

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_env; r_t0; r_t1 ]} →

    (* environment table *)
    withinBounds (RW, b_r, e_r, a_r') = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι1 ⊆ Ep →
    up_close (B:=coPset) ι ⊆ Ep ∖ ↑ι1 →
    up_close (B:=coPset) ι2 ⊆ Ep ∖ ↑ι1 ∖ ↑ι →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
       ∗ r_t1 ↦ᵣ w
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (seal f_m seal_addrs)
       (* malloc *)
       ∗ na_inv logrel_nais ι2 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
       ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
       (* linked list invariants *)
       ∗ sealLL ι ll γ
       ∗ prefLL γ pbvals
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
          ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
          ∗ ([∗ map] r↦w ∈ <[r_t2:=inl 0%Z]> (<[r_t3:=inl 0%Z]> (<[r_t4:=inl 0%Z]>
                          (<[r_t5:=inl 0%Z]> (<[r_t6:=inl 0%Z]> (<[r_t7:=inl 0%Z]> rmap))))), r ↦ᵣ w)
          ∗ (∃ a pbvals', prefLL γ (pbvals ++ pbvals' ++ [(a,w)]) ∗ r_t1 ↦ᵣ inr (RWX,a,a,a))
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
  Admitted.

End sealing.
