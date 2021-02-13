From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone list_new malloc.
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
                  ; Lea r_t0 (inl (length findb_instr + 3)%Z)
                  ] ++ (encodeInstrW (Load r_env r_env) :: findb_instr) ++
    encodeInstrsW [ Mov r_env (inl 0%Z) (* Clearing *)
                  ; Mov r_t0 (inr r_t4) (* Restore return capability *)
                  ; Mov r_t4 (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition unseal_instrs_length := Eval cbn in length (unseal_instrs).

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
                  ; Lea r_t0 (inl (length (appendb_instr f_m) + 2)%Z)
                  ] ++ appendb_instr f_m ++
    encodeInstrsW [ Restrict r_t1 (inl (encodePerm O))
                  ; GetB r_t2 r_t1
                  ; Subseg r_t1 r_t2 r_t2
                  ; Mov r_env (inl 0%Z) (* Clearing *)
                  ; Mov r_t2 (inl 0%Z) (* Clearing *)
                  ; Mov r_t0 (inr r_t7) (* Restore return capability *)
                  ; Mov r_t7 (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition seal_instrs_length := Eval cbn in length (seal_instrs 0%Z).

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
                  ; Mov r_t2 r_t9 (* Prepare for creating closure for unseal, environment *)
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
        ll ll' (* linked list head and pointers *)
        a_first (* special adresses *)
        ι γ φ Ep (* invariant/gname names *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length unseal_instrs)%a →

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ Ep →

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
      ∗ na_own logrel_nais Ep
      (* trusted code *)
      ∗ codefrag a_first unseal_instrs
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ inl 0%Z
          ∗ (∃ b' w pbvals, ⌜(b + 2)%a = Some b' ∧ (b,w) ∈ pbvals⌝ ∗ prefLL γ pbvals ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ inl 0%Z)
          ∗ r_t3 ↦ᵣ inl 0%Z
          ∗ r_t4 ↦ᵣ inl 0%Z
          ∗ codefrag a_first unseal_instrs
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hd Hnclose) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & #Hseal_inv & Hown & Hprog & Hφfailed & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t4" as (w4) "Hr_t4".

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hprog" "Hcont".
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iApply findb_spec; iFrameCapSolve; eauto.
    iFrame "# ∗". iSplitL "Hr_t2"; eauto. iSplitL "Hr_t3"; eauto.
    iNext. iIntros "(HPC & Hr_t0 & Hr_t2 & HisList & Hr_t3 & Hprog & Hown)".
    iDestruct "HisList" as (b_a b' w pbvals) "(%HX & Hpref & Hr_t1 & Hr_env)".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    destruct HX as (HA & HB & HC). eapply z_to_addr_eq_inv in HA. subst b_a; auto.

    rewrite (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 18)%a ltac:(destruct Hvpc; congruence)).
    focus_block 2 "Hprog" as a_middle' Ha_middle' "Hprog" "Hcont".
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ"; iFrame "# ∗".
    iExists _,_,_. iFrame.
    iPureIntro. eauto.
  Qed.

  Lemma seal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w (* input z *)
        ll ll' pbvals (* linked list head and pointers *)
        a_first (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 γ Ep φ (* invariant/gname names *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (seal_instrs f_m))%a →

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_env; r_t0; r_t1 ]} →

    (* environment table *)
    withinBounds (RW, b_r, e_r, a_r') = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι ⊆ Ep →
    up_close (B:=coPset) ι1 ⊆ Ep ∖ ↑ι →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
       ∗ r_t1 ↦ᵣ w
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first (seal_instrs f_m)
       (* malloc *)
       ∗ na_inv logrel_nais ι1 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
       ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
       (* linked list invariants *)
       ∗ sealLL ι ll γ
       ∗ prefLL γ pbvals
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ inl 0%Z
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
          ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
          ∗ ([∗ map] r↦w ∈ <[r_t2:=inl 0%Z]> (<[r_t3:=inl 0%Z]> (<[r_t4:=inl 0%Z]>
                          (<[r_t5:=inl 0%Z]> (<[r_t6:=inl 0%Z]> (<[r_t7:=inl 0%Z]> rmap))))), r ↦ᵣ w)
          ∗ (∃ a pbvals', prefLL γ (pbvals ++ pbvals' ++ [(a,w)]) ∗ r_t1 ↦ᵣ inr (O,a,a,a))
          ∗ codefrag a_first (seal_instrs f_m)
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hhd Hdom Hbounds Hf_m Hnclose Hnclose') "(HPC & Hr_env & Hr_t1 & Hr_t0 & Hregs & Hown & Hprog & #Hmalloc & Hpc_b & Ha_r' & #Hseal_inv & #Hpref & Hφ)".

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hprog" "Hcont".
    assert (is_Some (rmap !! r_t7)) as [w7 Hw7];[rewrite elem_of_gmap_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[apply Hw7|].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs"; [apply lookup_delete|].
    rewrite insert_delete.

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iApply appendb_spec; try iFrame "∗ #"; auto. rewrite dom_insert_L Hdom. set_solver.
    iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hpc_b & Ha_r' & Hregs & HisList & Hprog & Hown)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    rewrite (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 53)%a ltac:(destruct Hvpc; congruence)).
    focus_block 2 "Hprog" as a_middle' Ha_middle' "Hprog" "Hcont".
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[simplify_map_eq; auto|].
    map_simpl "Hregs".
    iDestruct "HisList" as (a a' pbvals') "(%HA & #Hpref' & Hr_t1)".
    iGo "Hprog". rewrite decode_encode_perm_inv. reflexivity.
    iGo "Hprog". rewrite decode_encode_perm_inv. auto. solve_addr.
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ"; iFrame "∗ #".
    iSplitR "Hr_t1".
    - iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs"; [apply lookup_delete|].
      rewrite insert_delete -delete_insert_ne //.
      iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs"; [apply lookup_delete|].
      rewrite insert_delete. rewrite !(insert_commute _ r_t7) //.
    - iExists _, _. rewrite decode_encode_perm_inv. iFrame "∗ #".
  Qed.

End sealing.
