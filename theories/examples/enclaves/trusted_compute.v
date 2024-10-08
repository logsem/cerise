From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

Section trusted_compute_example.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg : sealStoreG Σ} `{MP: MachineParameters}.

  (* Data part, following the directly the main code *)
  Definition trusted_compute_data (linking_table_cap : LWord) : list LWord :=
    [
      linking_table_cap ;
      (LWInt 0%Z) (* placeholder for storing identity of the enclave *)
    ].

  (* Expect:
     - PC := (RWX, main, main_end, main)
     - R0 := (RWX, adv, adv_end, adv) *)
  Definition trusted_compute_main_code_init0 (main callback data : Z) : list LWord :=
    (* main: *)
    encodeInstrsLW [
        Mov r_t1 PC;      (* rt1 := (RWX, main, main_end, main) *)
        Mov r_t2 r_t1;    (* rt2 := (RWX, main, main_end, main) *)

        (* Create callback sentry *)
        Lea r_t1 (callback - main)%Z;       (* rt1 := (RWX, main, main_end, callback) *)
        Restrict r_t1 (encodePerm E);       (* rt1 := (E, main, main_end, callback) *)

        (* Store writable capability into data*)
        Lea r_t2 (data - main)%Z;           (* rt2 := (RWX, main, main_end, data) *)
        Mov r_t3 r_t2;                      (* rt3 := (RWX, main, main_end, data) *)
        Lea r_t3 1%Z;                       (* rt3 := (RWX, main, main_end, data + 1) *)
        Store r_t3 r_t2;                    (* mem[data + 1] := (RWX, main, main_end, data) *)

        (* Jump to adversary *)
        Mov r_t2 0;
        Mov r_t3 0;
        Jmp r_t0
      ].

  (* Expect PC := (RWX, main, main_end, callback) *)
  Definition trusted_compute_main_code_callback0
    (callback fails data : Z)
    (hash_enclave : Z)
    (assert_lt_offset : Z)
    : list LWord :=
      (* callback: *)
      encodeInstrsLW [
        (* until the end, r3 contains the capability that bails out if something is wrong *)
        Mov r_t3 PC ;                 (* r_t3 :=  (RX, main, main_end, callback) *)
        Mov r_t4 r_t3 ;               (* r_t4 :=  (RX, main, main_end, callback) *)
        Lea r_t3 (fails-callback)%Z;  (* r_t3 :=  (RX, main, main_end, fails) *)

        (* get a writable capability for storing identity *)
        Lea r_t4 (data + 1 - callback)%Z; (* r_t4 := (RX, main, main_end, data + 1) *)
        Load r_t4 r_t4;                   (* r_t4 := (RWX, main, main_end, data) *)
        Load r_t5 r_t4 ;                  (* r_t5 := (RO, b_lt, e_lt, b_lt) *)
        Lea r_t4 1;                       (* r_t4 := (RWX, main, main_end, data + 1) *)

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
        Mov r_t1 r_t5;
        GetA r_t4 r_t0;
        Mov r_t5 42%Z
      ]
      ++ assert_reg_instrs assert_lt_offset r_t1
      ++ encodeInstrsLW [Halt]
      ++ (* fails: *) encodeInstrsLW [Fail].

  Definition trusted_compute_main_init_len : Z :=
    Eval cbv in (length (trusted_compute_main_code_init0 0%Z 0%Z 0%Z)).

  Definition trusted_compute_main_callback_len : Z :=
    Eval cbv in (length (trusted_compute_main_code_callback0 0%Z 0%Z 0%Z 0%Z 0%Z)).

  Definition trusted_compute_main_data_len : Z :=
    Eval cbv in (length (trusted_compute_data (LInt 0%Z))).

  Definition trusted_compute_enclave_code (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::
    encodeInstrsLW [
      (* get signing sealing key *)
      Mov r_t1 PC;
      Lea r_t1 (-1)%Z;
      Load r_t1 r_t1;
      Load r_t1 r_t1;
      GetA r_t2 r_t1;
      Add r_t3 r_t2 1;
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

  Axiom hash_trusted_compute_enclave : Z.

  Definition trusted_compute_main_code (assert_lt_offset : Z) : list LWord :=
    let init     := 0%Z in
    let callback := trusted_compute_main_init_len in
    let data     := trusted_compute_main_init_len + trusted_compute_main_callback_len in
    let fails    := (data - 1)%Z in
    (trusted_compute_main_code_init0 init callback data) ++
    (trusted_compute_main_code_callback0 callback fails data hash_trusted_compute_enclave assert_lt_offset).

  Definition trusted_compute_main_code_len : Z :=
    Eval cbv in trusted_compute_main_init_len + trusted_compute_main_callback_len.

  Definition trusted_compute_main_len :=
    Eval cbv in trusted_compute_main_code_len + trusted_compute_main_data_len.


  (** Specification init code *)
  Lemma trusted_compute_main_init_spec
    (b_main adv adv_end: Addr)
    (pc_v adv_v : Version)
    (assert_lt_offset : Z)
    (w0 w1 w2 w3 w4 : LWord)
    φ :

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    ContiguousRegion b_main trusted_compute_main_len ->
    ⊢ ((
          codefrag b_main pc_v trusted_compute_main
          ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LWInt 0%Z)

          ∗ PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
          ∗ r_t0 ↦ᵣ LCap RWX adv adv_end adv adv_v
          ∗ r_t1 ↦ᵣ w1
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag b_main pc_v trusted_compute_main
                ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LCap RWX b_main e_main a_data pc_v)
                ∗ PC ↦ᵣ (LCap RWX adv adv_end adv adv_v)
                ∗ r_t0 ↦ᵣ (LCap RWX adv adv_end adv adv_v)
                ∗ r_t1 ↦ᵣ (LCap E b_main e_main a_callback pc_v)
                ∗ r_t2 ↦ᵣ LInt 0
                ∗ r_t3 ↦ᵣ LInt 0
                  -∗ WP Seq (Instr Executable) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.

    (* We define a local version of solve_addr, which subst and unfold every computed addresses  *)
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /trusted_compute_main_len in H
                end)
      ; rewrite !/trusted_compute_main_code_len /trusted_compute_main_len
          /trusted_compute_main_init_len /trusted_compute_main_callback_len
      ; solve_addr.

    intros * Hregion.
    iIntros "(Hcode & Hdata & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hφ)".
    codefrag_facts "Hcode".
    iGo "Hcode".
    rewrite decode_encode_perm_inv; by cbn.
    rewrite decode_encode_perm_inv.
    iGo "Hcode".
    (* FIXME: not sure why I need to rewrite this *)
    replace (a_data ^+ 1)%a with (b_main ^+ 44)%a by solve_addr'.
    iGo "Hcode".
    iApply (wp_wand with "[-]"); last (iIntros (v) "H"; by iLeft).
    iApply "Hφ".
    iFrame.
  Qed.

  (** Specification callback code *)
  (** ------ TODO ------ *)

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


  Lemma trusted_compute_callback_code_spec
    (b_main adv adv_end: Addr)
    (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (* assert *)
    (w0 w1 w2 w3 : LWord)
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

End trusted_compute_example.
