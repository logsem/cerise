From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import addr_reg_sample macros_new.
From cap_machine Require Import rules logrel.
From cap_machine Require Import monotone keylist.
From cap_machine.proofmode Require Import tactics_helpers solve_pure proofmode contiguous map_simpl.

Section sealing.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}
          {seals:sealStoreG Σ}
          {mono : sealLLG Σ}.

  (* Assume r_t1 contains a capability representing a sealed value.
     First we must check that its permission is RWX (or the environment could derive
     an O capability from the entrypoint to malloc), and that its range is 1
     (to make sure it has the authority of a seal)
     Get its b field, find the corresponding value in the linked list contained in r_env.
     Result is returned in r_t1; clear r_env for security and return. *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env r_t4 (r_t2 rt_3 are used by findb) *)
  Definition unseal_instrs :=
    encodeInstrsW [ Mov r_t3 r_t1 ] ++
    reqperm_instrs r_t3 (encodePerm RWX) ++
    reqsize_exact_instrs r_t3 1 ++
    encodeInstrsW [ GetB r_t1 r_t3
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
     Subseg the new capability to bottom range
     clear r_env and return *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env r_t2 r_t7 (r_t3 r_t4 r_t5 r_t6 used by appendb) *)
  Definition seal_instrs f_m :=
    encodeInstrsW [ Mov r_t7 (inr r_t0) (* Save return point *)
                  ; Mov r_t0 (inr PC) (* Setup the return point for findb *)
                  ; Lea r_t0 (inl (length (appendb_instr f_m) + 2)%Z)
                  ] ++ appendb_instr f_m ++
    encodeInstrsW [ GetB r_t2 r_t1
                  ; Add r_t3 r_t2 1
                  ; Subseg r_t1 r_t2 r_t3
                  ; Mov r_env (inl 0%Z) (* Clearing *)
                  ; Mov r_t2 (inl 0%Z) (* Clearing *)
                  ; Mov r_t3 (inl 0%Z) (* Clearing *)
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
    encodeInstrsW [ Mov r_t9 r_t1 (* Keep a copy of the capability to the list *)
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
    encodeInstrsW [ Mov r_t2 r_t10 (* Closure for seal now in r_t2 *)
                  ; Mov r_t8 (inl 0%Z) (* Clearing registers *)
                  ; Mov r_t9 (inl 0%Z)
                  ; Mov r_t10 (inl 0%Z)
                  ; Jmp r_t0 (* Return *)
                  ].

  Definition make_seal_preamble f_m ai :=
    ([∗ list] a_i;w_i ∈ ai;(make_seal_preamble_instrs f_m), a_i ↦ₐ w_i)%I.

  Lemma unseal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        wsealed (* p b e a *) (* input cap *)
        ll ll' (* linked list head and pointers *)
        a_first (* special adresses *)
        ι γ φ Ep (* invariant/gname names *)
        Φ {Hpers : ∀ w, Persistent (Φ w)} (* this predicate is chosen by the client at creation *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length unseal_instrs)%a →

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ Ep →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX ll ll' ll
      ∗ r_t1 ↦ᵣ (* WCap (p, b, e, a) *) wsealed
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      ∗ (∃ w, r_t4 ↦ᵣ w)
      (* invariant for d *)
      ∗ sealLL ι ll γ Φ
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais Ep
      (* trusted code *)
      ∗ codefrag a_first unseal_instrs
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ WInt 0%Z
          ∗ (∃ b b' a w pbvals, ⌜wsealed = WCap RWX b b' a ∧ (b + 1)%a = Some b' ∧ (b',w) ∈ pbvals⌝ ∗ prefLL γ pbvals ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ WInt 0%Z ∗ Φ w)
          ∗ r_t3 ↦ᵣ WInt 0%Z
          ∗ r_t4 ↦ᵣ WInt 0%Z
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

    focus_block_0 "Hprog" as "Hprog" "Hcont".
    iInstr "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as mid Hmid "Hprog" "Hcont".
    iApply reqperm_spec;iFrameAutoSolve.
    iNext. destruct (isPermWord wsealed RWX) eqn:Hperm;[|iFrame].
    destruct wsealed as [z|[p b e a|]|];try by inversion Hperm.
    apply bool_decide_eq_true_1 in Hperm as <-.
    iExists _,_,_. iSplit;eauto. iIntros "(HPC & Hprog & Hr_t3 & Hr_t1 & Hr_t2)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 2 "Hprog" as mid0 Hmid0 "Hprog" "Hcont".
    iApply reqsize_spec;iFrameAutoSolve.
    iNext. destruct (1 =? e - b)%Z eqn:Hsize;cycle 1.
    { iFrame. }
    iIntros "HH". iDestruct "HH" as (w1 w0) "(Hprog & HPC & Hr_t3 & Hr_t1 & Hr_t2)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    codefrag_facts "Hprog". simpl in H, H0.
    focus_block 3 "Hprog" as mid1 Hmid1 "Hprog" "Hcont".
    iGo "Hprog". simpl in *. instantiate (1 := (mid1 ^+ 18)%a). solve_addr.
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 4 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iApply findb_spec; iFrameAutoSolve; eauto.
    iFrame "# ∗".
    iNext. iIntros "(HPC & Hr_t0 & Hr_t2 & HisList & Hr_t3 & Hprog & Hown)".
    iDestruct "HisList" as (b_a b' b'' w pbvals) "(%HX & Hpref & Hr_t1 & Hr_env & #HΦ)".
    destruct HX as (HA & HA1 & HB & HC).
    unfocus_block "Hprog" "Hcont" as "Hprog".
    eapply finz_of_z_eq_inv in HA. subst b_a; auto.
    assert (e = b')%Z as <-.
    { solve_addr. }

    rewrite (updatePcPerm_cap_non_E pc_p pc_b pc_e (mid1 ^+ 18)%a ltac:(destruct Hvpc; congruence)).
    focus_block 5 "Hprog" as a_middle' Ha_middle' "Hprog" "Hcont".
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ"; iFrame "# ∗".
    iExists _,_,_. iPureIntro; eauto.
  Qed.

  Lemma seal_spec Φ (* client chosen seal predicate *)
        pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w (* input z *)
        ll ll' pbvals (* linked list head and pointers *)
        a_first (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 γ Ep φ (* invariant/gname names *)
        {Hpers : ∀ w, Persistent (Φ w)} (* the client chosen predicate is persistent *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (seal_instrs f_m))%a →

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    dom rmap = all_registers_s ∖ {[ PC; r_env; r_t0; r_t1 ]} →

    (* environment table *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι ⊆ Ep →
    up_close (B:=coPset) ι1 ⊆ Ep ∖ ↑ι →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_env ↦ᵣ WCap RWX ll ll' ll
       ∗ r_t1 ↦ᵣ w
       ∗ Φ w
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first (seal_instrs f_m)
       (* malloc *)
       ∗ na_inv logrel_nais ι1 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
       ∗ a_r' ↦ₐ WCap E b_m e_m b_m
       (* linked list invariants *)
       ∗ sealLL ι ll γ Φ
       ∗ prefLL γ pbvals
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ WInt 0%Z
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
          ∗ a_r' ↦ₐ WCap E b_m e_m b_m
          ∗ ([∗ map] r↦w ∈ <[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]>
                          (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]> rmap))))), r ↦ᵣ w)
          ∗ (∃ a a' pbvals', ⌜(a + 1)%a = Some a'⌝ ∗ prefLL γ (pbvals ++ pbvals' ++ [(a',w)]) ∗ r_t1 ↦ᵣ WCap RWX a a' a' ∗ a ↦ₐ WInt 0)
          ∗ codefrag a_first (seal_instrs f_m)
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hhd Hdom Hbounds Hf_m Hnclose Hnclose') "(HPC & Hr_env & Hr_t1 & HΦw & Hr_t0 & Hregs & Hown & Hprog & #Hmalloc & Hpc_b & Ha_r' & #Hseal_inv & #Hpref & Hφ)".

    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hprog" "Hcont".
    assert (is_Some (rmap !! r_t7)) as [w7 Hw7];[rewrite -elem_of_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[apply Hw7|].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs"; [apply lookup_delete|].
    rewrite insert_delete_insert.

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iApply appendb_spec; try iFrame "∗ #"; auto. rewrite dom_insert_L Hdom. set_solver.
    iFrame. iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hpc_b & Ha_r' & Hregs & HisList & Hprog & Hown)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    rewrite (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 58)%a ltac:(destruct Hvpc; congruence)).
    focus_block 2 "Hprog" as a_middle' Ha_middle' "Hprog" "Hcont".
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[simplify_map_eq; auto|].
    map_simpl "Hregs".
    iDestruct "HisList" as (a a' a'' pbvals') "(%HA & #Hpref' & Hr_t1 & Ha)".
    destruct HA as (HA & HB).
    iGo "Hprog". instantiate (1:=a'). solve_addr. solve_addr.
    iGo "Hprog".

    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ"; iFrame "∗ #".
    iSplit; eauto.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs"; [apply lookup_delete|].
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs"; [simplify_map_eq;auto|].
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs"; [simplify_map_eq;auto|].
    map_simpl "Hregs".
    repeat rewrite -(insert_commute _ _ r_t7)//.
  Qed.

  Lemma sealLL_alloc ι ll Ep Φ {Hpers : ∀ w, Persistent (Φ w)} :
    ll ↦ₐ WInt 0%Z -∗
    |={Ep}=> ∃ γ, sealLL ι ll γ Φ.
  Proof.
    iIntros "Hll".
    iMod (own_alloc (● principal prefR [])) as (γ) "Hown".
    { eapply auth_auth_valid. repeat red. apply I. }
    iMod (na_inv_alloc logrel_nais _ ι (∃ hd : Word, ll ↦ₐ hd ∗ (∃ awvals : list (Addr * Word), isList hd awvals ∗ Exact γ awvals ∗ [∗ list] aw ∈ awvals, Φ aw.2)) with "[Hll Hown]")%I as "Hinv".
    { iNext. iExists (WInt 0%Z). iFrame.
      iSplit;done. }
    iExists γ. auto.
  Qed.

  Lemma make_seal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        a_first (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 Ep φ (* invariant/gname names *)
        Φ {Hpers: ∀ w, Persistent (Φ w)} (* The spec for make seal works for any seal predicate Φ
             that the client must choose upon creation *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ (length (unseal_instrs) + length (seal_instrs f_m) + length (make_seal_preamble_instrs f_m)))%a →

    dom rmap = all_registers_s ∖ {[ PC; r_t0]} →

    (* environment table *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι1 ⊆ Ep →

    PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ (length (unseal_instrs) + length (seal_instrs f_m)))%a
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first (unseal_instrs ++ seal_instrs f_m ++ make_seal_preamble_instrs f_m)
       (* malloc *)
       ∗ na_inv logrel_nais ι1 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
       ∗ a_r' ↦ₐ WCap E b_m e_m b_m
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
          ∗ a_r' ↦ₐ WCap E b_m e_m b_m
          ∗ (∃ b1 e1 b2 e2 ll ll', let wvar := WCap RWX ll ll' ll in
                                   let wcode1 := WCap pc_p pc_b pc_e a_first in
                                   let wcode2 := WCap pc_p pc_b pc_e (a_first ^+ length (unseal_instrs))%a in
                                   r_t1 ↦ᵣ WCap E b1 e1 b1 ∗ r_t2 ↦ᵣ WCap E b2 e2 b2
                                   ∗ ⌜(b1 + 8)%a = Some e1⌝ ∗ ⌜(b2 + 8)%a = Some e2⌝
                                   ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
                                   ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
                                   (* linked list invariants *)
                                   ∗ ⌜(ll + 1)%a = Some ll'⌝
                                   ∗ ∃ γ, sealLL ι ll γ Φ)
          ∗ ([∗ map] r↦w ∈ (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]> (<[r_t8:=WInt 0%Z]> (<[r_t9:=WInt 0%Z]> (<[r_t10:=WInt 0%Z]> (delete r_t1 (delete r_t2 rmap)))))))))), r ↦ᵣ w)
          ∗ codefrag a_first (unseal_instrs ++ seal_instrs f_m ++ make_seal_preamble_instrs f_m)
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hdom Hbounds Hf_m Hnclose') "(HPC & Hr_t0 & Hregs & Hown & Hprog & #Hmalloc & Hpc_b & Ha_r' & Hφ)".

    focus_block 2 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    assert (is_Some (rmap !! r_t8)) as [w8 Hw8];[rewrite -elem_of_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[apply Hw8|].
    iGo "Hprog".
    { rewrite /seal_instrs_length. instantiate (1 := (a_first ^+ length (unseal_instrs))%a).
      solve_addr. }
    unfocus_block "Hprog" "Hcont" as "Hprog".

    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs"; [apply lookup_delete|].
    rewrite insert_delete_insert.

    rewrite /make_seal_preamble_instrs.
    focus_block 3 "Hprog" as a_middle1 Ha_middle1 "Hprog" "Hcont".
    iApply malloc_spec_alt; iFrameAutoSolve. 4: iFrame "# ∗".
    set_solver. auto. lia.
    iSplitL "". iNext. auto.
    iSplitL "". iNext. iRight. auto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hll & Hr_t0 & Hown & Hregs)".
    iDestruct "Hll" as (ll ll') "(%Heqb & Hr_t1 & Hll)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 4 "Hprog" as a_middle2 Ha_middle2 "Hprog" "Hcont".
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[simplify_map_eq; auto|].
    assert (is_Some (rmap !! r_t9)) as [w9 Hw9];[rewrite -elem_of_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]";[simplify_map_eq; auto|].
    map_simpl "Hregs".
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs"; [apply lookup_delete|].
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs"; [simplify_map_eq; auto|].
    (* TODO debug why map_simpl "Hregs" loops here ?? *)
    rewrite insert_delete_insert. rewrite (delete_commute _ _ r_t8)//.
    rewrite -(delete_insert_ne _ r_t8); auto. rewrite insert_delete_insert.

    focus_block 5 "Hprog" as a_middle3 Ha_middle3 "Hprog" "Hcont".
    iApply crtcls_spec_alt; iFrameAutoSolve. 3: iFrame "# ∗".
    set_solver+ Hdom. auto.
    iSplitL ""; eauto. iSplitL ""; eauto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hseal)".
    iDestruct "Hseal" as (b1 e1) "(Hb1eq & Hr_t1 & Hseal & Hr_t0 & Hr_t2 & Hown & Hregs)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 6 "Hprog" as a_middle4 Ha_middle4 "Hprog" "Hcont".
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]";[simplify_map_eq; auto|].
    assert (is_Some (rmap !! r_t10)) as [w10 Hw10];[rewrite -elem_of_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]";[simplify_map_eq; auto|].
    map_simpl "Hregs".
    iGo "Hprog". instantiate (1 := a_first). rewrite /unseal_instrs_length. solve_addr.
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 7 "Hprog" as a_middle5 Ha_middle5 "Hprog" "Hcont".
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs"; [simplify_map_eq; auto|].
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs"; [simplify_map_eq; auto|].
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs"; [simplify_map_eq; auto|].
    map_simpl "Hregs".
    iApply crtcls_spec; iFrameAutoSolve. 3: iFrame "# ∗".
    set_solver+ Hdom. auto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hunseal)".
    iDestruct "Hunseal" as (b2 e2) "(Hb2eq & Hr_t1 & Hunseal & Hr_t0 & Hr_t2 & Hown & Hregs)".
    map_simpl "Hregs".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 8 "Hprog" as a_middle6 Ha_middle6 "Hprog" "Hcont".
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t9 with "Hregs") as "[Hr_t9 Hregs]";[simplify_map_eq; auto|].
    iDestruct (big_sepM_delete _ _ r_t10 with "Hregs") as "[Hr_t10 Hregs]";[simplify_map_eq; auto|].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    iMod (sealLL_alloc with "[Hll]") as (γ) "Hsealinv".
    { rewrite /region_pointsto. rewrite finz_seq_between_singleton; auto.
      rewrite /region_addrs_zeroes. rewrite (proj2 (proj1 (finz_incr_iff_dist ll ll' 1) ltac:(auto))).
      simpl replicate. iDestruct "Hll" as "(Hll & _)". iFrame. }
    iDestruct (big_sepM_insert _ _ r_t9 with "[$Hregs $Hr_t9]") as "Hregs"; [simplify_map_eq; auto|].
    iDestruct (big_sepM_insert _ _ r_t8 with "[$Hregs $Hr_t8]") as "Hregs"; [simplify_map_eq; auto|].
    iDestruct (big_sepM_insert _ _ r_t10 with "[$Hregs $Hr_t10]") as "Hregs"; [simplify_map_eq; auto|].
    map_simpl "Hregs".
    iApply "Hφ"; iFrame "∗ #".
    iSplitR "Hregs".
    { iFrame "%". }
    { rewrite delete_commute //.
      rewrite !(insert_commute _ r_t3) // !(insert_commute _ r_t4) // !(insert_commute _ r_t5) // !(insert_commute _ r_t6) // !(insert_commute _ r_t7) // !(insert_commute _ r_t8) // !(insert_commute _ r_t9) // !(insert_commute _ r_t10) //. }
  Qed.

End sealing.
