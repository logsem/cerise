From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

(* NOTE
   Careful !! The exact implementation here is slightly different from the one
   in `trusted_compute.s`,
   as the main program here has a SEPARATE data section
   containing the linking table capability and placeholder for identity !
 *)

Section trusted_compute_example.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg : sealStoreG Σ} `{MP: MachineParameters}.

  (* Data part, following the directly the main code *)
  Definition trusted_compute_data (linking_table_cap : LWord) : list LWord :=
    [
      linking_table_cap ;
      (LWInt 0%Z) (* placeholder for storing identity of the enclave *)
    ].

  Definition trusted_compute_main_data_length : Z :=
    Eval cbv in (length (trusted_compute_data (LWInt 0%Z))).

  (* Before main_code_init, we expect a capability pointing to the data  *)
  Definition trusted_compute_main_code_init0 (init callback end_main : Z) : list LWord :=
    (* (RW, b_data, e_data, b_data) *)
    (* init: *)
    encodeInstrsLW [
        Mov r_t0 PC;      (* rt0 := (RWX, bpc, epc, bpc+1) *)
        Mov r_t1 r_t0;    (* rt1 := (RWX, bpc, epc, bpc+1) *)

        (* Create adversary capability *)
        GetA r_t2 r_t1;                     (* rt2 := bpc+1 *)
        Add r_t2 r_t2 (end_main - init)%Z;  (* rt2 := end_main *)
        GetE r_t3 r_t1;                     (* rt3 := epc *)
        Subseg r_t1 r_t2 r_t3;              (* rt1 := (RWX, end_main, epc, bpc+1) *)
        Lea r_t1 (end_main-init)%Z;         (* rt1 := (RWX, end_main, epc, end_main) *)

        (* Create callback sentry *)
        Lea r_t0 (callback - init)%Z;       (* rt0 := (RWX, bpc, epc, callback) *)
        Restrict r_t0 (encodePerm E);       (* rt0 := (E, bpc, epc, callback) *)

        (* Jump to adversary *)
        Mov r_t2 0;
        Mov r_t3 0;
        Mov r_t4 0;
        Jmp r_t1
      ].

  Definition trusted_compute_main_code_callback0
    (init callback fails : Z)
    (hash_enclave : Z)
    (assert_lt_offset : Z)
    : list LWord :=
      (* callback: *)
      encodeInstrsLW [
        (* until the end, r3 contains the capability that bails out if something is wrong *)
        Mov r_t3 PC ;                 (* r_t3 :=  (RX, bpc, epc, callback) *)
        Mov r_t4 r_t3 ;               (* r_t4 :=  (RX, bpc, epc, callback) *)
        Lea r_t3 (fails-callback)%Z;  (* r_t3 :=  (RX, bpc, epc, fails) *)

        (* get a writable capability for storing identity *)
        Lea r_t4 (init-callback-1)%Z; (* r_t4 :=  (RX, bpc, epc, bpc) *)
        Load r_t4 r_t4;               (* r_t4 := (RW, b_data, e_data, b_data) *)
        Lea r_t4 1;                   (* r_t4 := (RW, b_data, e_data, b_data+1) *)

        (* sanity check: w_res is a sealed capability *)
        GetOType r_t2 r_t0;
        Sub r_t2 r_t2 (-1)%Z;
        Jnz r_t3 r_t2;

        (* check otype(w_res) against identity of the enclave *)
        GetOType r_t2 r_t0;
        EStoreId r_t2 r_t2 r_t4;
        Sub r_t2 r_t2 1;
        Jnz r_t3 r_t2;
        Load r_t4 r_t4;
        Sub r_t4 r_t4 hash_enclave;
        Jnz r_t3 r_t4;

        (* get returned value and assert it to be 42 *)
        UnSeal r_t0 r_t0 r_t1;
        GetA r_t4 r_t0;
        Mov r_t5 42%Z
      ]
      ++ assert_instrs assert_lt_offset
      ++ encodeInstrsLW [Halt]
      ++ (* fails: *) encodeInstrsLW [Fail].


  Definition trusted_compute_enclave_code (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::
    encodeInstrsLW [
      (* get signing sealing key *)
      Mov r_t1 PC;
      Lea r_t1 (-1)%Z;
      Load r_t1 r_t1;
      Load r_t1 r_t1;
      GetA r_t1 r_t2;
      Add r_t3 r_t1 1;
      Subseg r_t1 r_t2 r_t3;

      (* store the result (42) in a O-permission capability and sign it *)
      Mov r_t2 PC;
      GetA r_t3 r_t2;
      Sub r_t3 42 r_t3;
      Lea r_t2 r_t3;
      Restrict r_t2 (encodePerm O);
      Seal r_t2 r_t2 r_t1;

      (* share the signed value and the unsealing key to the adversary *)
      Restrict r_t1 (encodeSealPerms (false, true)); (* restrict r1 U *)
      Jmp r_t0
    ].

  Definition trusted_compute_main_callback : Z :=
    Eval cbv in (length (trusted_compute_main_code_init0 0%Z 0%Z 0%Z)).

  Definition trusted_compute_main_data_len : Z :=
   Eval cbv in (length (trusted_compute_data (LInt 0%Z))).

  Definition trusted_compute_main_end :=
    Eval cbv in
      trusted_compute_main_callback +
        (length (trusted_compute_main_code_callback0 0%Z 0%Z 0%Z 0%Z 0%Z)) +
        trusted_compute_main_data_len.

  Definition trusted_compute_main_fails :=
    Eval cbv in trusted_compute_main_end - 1.

  Axiom hash_trusted_compute_enclave : Z.

  Definition trusted_compute_main_code (assert_lt_offset : Z) : list LWord :=
    let init := 1%Z in
    let callback := trusted_compute_main_callback  in
    let end_main := trusted_compute_main_end in
    let fails := trusted_compute_main_fails in
    (trusted_compute_main_code_init0 init callback end_main) ++
    (trusted_compute_main_code_callback0 init callback fails hash_trusted_compute_enclave assert_lt_offset).


  Context {nainv: logrel_na_invs Σ} .
  (* Define all the invariants *)
  Definition trusted_computeN : namespace := nroot .@ "trusted_compute".
  (* Linking table invariant *)
  Definition link_tableN := (trusted_computeN.@"link_table").
  Definition link_table_inv
    table_addr v_table_addr
    b_link e_link a_link v_link
    assert_entry b_assert e_assert v_assert :=
    na_inv logrel_nais link_tableN
      ((table_addr, v_table_addr) ↦ₐ LCap RO b_link e_link a_link v_link
       ∗ (assert_entry, v_link) ↦ₐ LCap E b_assert e_assert b_assert v_assert)%I.

  (* Assert invariant *)
  Definition assertN := (trusted_computeN.@"assert").
  Definition assert_inv b_a a_flag e_a v_assert :=
    na_inv logrel_nais assertN (assert_inv b_a a_flag e_a v_assert).

  Definition flag_assertN := (trusted_computeN.@"flag_assert").
  Definition flag_inv a_flag v_flag :=
    inv flag_assertN ((a_flag,v_flag) ↦ₐ LInt 0%Z) .

  Lemma trusted_compute_main_code_spec
    (b_code_main b_data_main end_adv: Addr)
    (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (* assert *)
    (w0 w1 w2 w3 w4 : LWord)
    φ :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let a_code_main := (b_code_main ^+ 1)%a in
    let e_data_main := (b_data_main ^+ trusted_compute_main_data_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    let len_main_code := length trusted_compute_main in
    let main_code_end := (a_code_main ^+ len_main_code)%a in
    let main_end := (main_code_end ^+ trusted_compute_main_data_len)%a in
    let link_addr := b_data_main in


    (a_link + assert_lt_offset)%a = Some assert_entry →
    (* TODO assume that, between 'main_end' and 'end_adv',
       there is only integers (for simplicity) *)
    main_end < end_adv ->

    (* TODO not needed for this part of the spec, but will be required for the full proof *)
    (link_table_inv link_addr v_link
      b_link e_link a_link v_link assert_entry
      b_assert e_assert v_assert
    ∗ assert_inv b_assert a_flag e_assert v_assert
    ∗ flag_inv a_flag v_assert)

    ⊢ ((
          codefrag a_code_main pc_v trusted_compute_main
          ∗ (b_code_main, pc_v) ↦ₐ (LCap RW b_data_main e_data_main b_data_main pc_v)
          ∗ [[b_data_main, e_data_main]] ↦ₐ{pc_v} [[ trusted_compute_data link_cap  ]]

          ∗ PC ↦ᵣ LCap RWX b_code_main end_adv a_code_main pc_v
          ∗ r_t0 ↦ᵣ w0
          ∗ r_t1 ↦ᵣ w1
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          ∗ r_t4 ↦ᵣ w4
          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag a_code_main pc_v trusted_compute_main
                ∗ (b_code_main, pc_v) ↦ₐ (LCap RW b_data_main e_data_main b_data_main pc_v)
                ∗ [[b_data_main, e_data_main]] ↦ₐ{pc_v} [[ trusted_compute_data link_cap  ]]

                ∗ PC ↦ᵣ (LCap RWX main_end end_adv main_end pc_v)
                ∗ r_t0 ↦ᵣ (LCap E b_code_main end_adv main_end pc_v)
                ∗ r_t1 ↦ᵣ (LCap RWX main_end end_adv main_end pc_v)
                ∗ r_t2 ↦ᵣ LInt 0
                ∗ r_t3 ↦ᵣ LInt 0
                ∗ r_t4 ↦ᵣ LInt 0
                  -∗ WP Seq (Instr Executable) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros * Hlink Hassert_entry Hend_adv.
    iIntros "(#Hlink & #Hassert & #Hflag)".
    iIntros "(Hcode & Hdata_cap & Hdata & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hφ)".
    codefrag_facts "Hcode".
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    transitivity (Some (a_code_main ^+ (trusted_compute_main_end + (-1))))%a; [|done].
    admit.
    admit.
    iInstr "Hcode"; first admit.
    transitivity (Some (a_code_main ^+ (trusted_compute_main_end + (-1))))%a; [|done].
    admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    rewrite decode_encode_perm_inv; by cbn.
    rewrite decode_encode_perm_inv.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.
    iInstr "Hcode"; first admit.

    iApply (wp_wand with "[-]").
    iApply "Hφ".
    iFrame.
    admit.
    iIntros (v); auto.
  Admitted.


End trusted_compute_example.
