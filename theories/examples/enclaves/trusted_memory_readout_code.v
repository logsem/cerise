From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

Class ClientSensor := {
    client_begin_addr : Addr;
    sensor_begin_addr : Addr;
    sensor_mmio_addr  : Addr;
  }.

Section trusted_memory_readout_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    `{reservedaddresses : ReservedAddresses}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  (* ------------------------ *)
  (* --- SENSOR *ENCLAVE* --- *)
  (* ------------------------ *)

  (* CODE LAYOUT:

      begin
       │
       ▽──────────┬──────┬──────┬──────┐
       │ cap data │ init │ read │ fail │
       └──────────┴──────┴──────┴──────┘

     DATA LAYOUT:

      data                          data+2
       │                             │
       ▽───────────┬─────────────────▽
       │ seal pair │ cap sensor_mmio │
       └───────────┴─────────────────┘
  *)

  (* Expect:
     - PC   = (RX, sensor, sensor_end, sensor_init)
     - r_t0 = return pointer
     - r_t1 = mmio addr capability
     Returns:
     - public signing key:      r_t1 = (U, σ__a+1, σ__a+2, σ__a+1)
     - read_sensor entry point: r_t2 = (E, sensor, sensor_end, sensor_read)
   *)
  Definition sensor_instrs_init (begin init read fail : Z) : list instr :=
    let RW := encodePerm RW in
    let E := encodePerm E in
    let U := encodeSealPerms (false, true) in
    let WCapType := encodeWordType (WCap O 0 0 0)%a in
    [ Mov r_t2 PC;             (* r_t2 = (RX, sensor, sensor_end, sensor_init) *)

      (* Check that we get an unsealed mmio capability from the adversary. *)
      Lea r_t2 (fail - init);  (* r_t2 = (RX, sensor, sensor_end, sensor_fail) *)
      GetWType r_t3 r_t1;
      Sub r_t3 r_t3 WCapType;
      Jnz r_t2 r_t3;           (* Jump to fail if not WCap *)

      (* Check that we get RW permissions. *)
      GetP r_t3 r_t1;
      Sub r_t3 r_t3 RW;
      Jnz r_t2 r_t3;           (* Jump to fail if not RW perms. *)

      (* Check that we have exclusive access to the mmio capability. *)
      IsUnique r_t3 r_t1;      (* r_t3 = 1: unique  0: not unique *)
      Sub r_t3 1 r_t3;         (* r_t3 = 0: unique  1: not unique *)
      Jnz r_t2 r_t3;           (* Jump to fail if not unique *)

      (* "Initialize" the sensor. *)
      Store r_t1 42;

      (* Get the data capability *)
      Lea r_t2 (begin - fail); (* r_t2 = (RX, sensor, sensor_end, sensor) *)
      Load r_t3 r_t2;          (* r_t3 = (RW, data, data_end, addr) *)
      GetB r_t4 r_t3;          (* r_t4 = data *)
      GetA r_t5 r_t3;          (* r_t5 = addr *)
      Sub r_t4 r_t4 r_t5;      (* r_t4 = data - addr *)
      Lea r_t3 r_t4;           (* r_t3 = (RW, data, data_end, data) *)

      (* Store mmio capability in private data. *)
      Lea r_t3 1;              (* r_t3 = (RW, data, data_end, data+1) *)
      Store r_t3 r_t1;

      (* Get the seal/unseal master capability and switch to signing.  *)
      Lea r_t3 (-1)%Z;         (* r_t3 = (RW, data, data_end, data) *)
      Load r_t1 r_t3;          (* r_t1 = (SU, σ__a, σ__a+2, σ__a) *)
      Lea r_t1 1%Z;            (* r_t1 = (SU, σ__a, σ__a+2, σ__a+1) *)

      (* Construct read_sensor entry point. *)
      Lea r_t2 (read - begin); (* r_t2 = (RX, sensor, sensor_end, sensor_read) *)
      Restrict r_t2 E;         (* r_t2 = (E, sensor, sensor_end, sensor_read) *)

      (* Sign the entry point capability. *)
      Seal r_t2 r_t1 r_t2 ;    (* r_t2 = Sealed σ__a+1 (E, sensor, sensor_end, sensor_read) *)

      (* Create signing public key *)
      GetA r_t3 r_t1;          (* r_t3 = σ__a+1 *)
      GetE r_t4 r_t1;          (* r_t4 = σ__a+2 *)
      Subseg r_t1 r_t3 r_t4;   (* r_t1 = (SU, σ__a+1, σ__a+2, σ__a+1) *)
      Restrict r_t1 U;         (* r_t1 = (U, σ__a+1, σ__a+2, σ__a+1) *)

      (* Jump back to adversary. *)
      Jmp r_t0
    ].

  Definition sensor_precode_init (begin init read fail : Z): list Word :=
    encodeInstrsW (sensor_instrs_init begin init read fail).

  Definition sensor_prelcode_init (begin init read fail : Z): list LWord :=
    encodeInstrsLW (sensor_instrs_init begin init read fail).

  (* Expect:
     - PC := (RX, sensor, sensor_end, sensor_read)
     - r_t0 return pointer
     Returns:
     - r_t0 return pointer
     - r_t1 sensor addr (mmio_a)
     - r_t2 return value (= 42)
     Clobbers: r_t3
   *)
  Definition sensor_instrs_read (begin read : Z) : list instr :=
    let ROperm := encodePerm RO in
    [ Mov r_t1 PC;                    (* r_t1 = (RX, sensor, sensor_end, sensor_read) *)
      Lea r_t1 (begin - read);        (* r_t1 = (RX, sensor, sensor_end, sensor) *)
      Load r_t1 r_t1;                 (* r_t1 = (RW, data_b, data_e, ?a) *)
      GetB r_t2 r_t1;                 (* r_t2 = data_b *)
      GetA r_t3 r_t1;                 (* r_t3 = ?a *)
      Sub r_t2 r_t2 r_t3;             (* r_t2 = data_b - ?a *)
      Lea r_t1 r_t2;                  (* r_t1 = (RW, data_b, data_e, data_b) *)

      (* Load mmio cap and sensor value *)
      (* cf https://github.com/proteus-core/cheritree/blob/e969919a30191a4e0ceec7282bb9ce982db0de73/morello/project/enclaveMorello/src/EL1Code/enclavecode/sensor_enclave.S#L106 *)
      Lea r_t1 1;                     (* r_t1 = (RW, data_b, data_e, data_b+1) *)
      Load r_t1 r_t1;                 (* r_t1 = (RW, mmio_b, mmio_e, mmio_a) *)
      Load r_t2 r_t1;                 (* r_t2 = sensor value (42) *)
      GetA r_t1 r_t1;                 (* r_t1 = mmio_a *)

      (* Return to caller *)
      Jmp r_t0
    ].

  Definition sensor_precode_read (init read : Z): list Word :=
    encodeInstrsW (sensor_instrs_read init read).
  Definition sensor_prelcode_read (init read : Z): list LWord :=
    encodeInstrsLW (sensor_instrs_read init read).

  Definition sensor_init_off : Z := 1.
  Definition sensor_init_len : nat :=
    Eval cbv in length (sensor_instrs_init 0 0 0 0).
  Definition sensor_read_off : Z :=
    Eval cbv in sensor_init_off + length (sensor_instrs_init 0 0 0 0).
  Definition sensor_read_len : nat :=
    Eval cbv in length (sensor_instrs_read 0 0).
  Definition sensor_fail_off : Z :=
    Eval cbv in sensor_read_off + sensor_read_len.

  Definition sensor_code_init : list Word :=
    sensor_precode_init 0 sensor_init_off sensor_read_off sensor_fail_off.
  Definition sensor_lcode_init : list LWord :=
    sensor_prelcode_init 0 sensor_init_off sensor_read_off sensor_fail_off.

  Definition sensor_code_read : list Word :=
    sensor_precode_read 0 sensor_read_off.
  Definition sensor_lcode_read : list LWord :=
    sensor_prelcode_read 0 sensor_read_off.

  Definition sensor_code : list Word :=
       sensor_code_init
    ++ sensor_code_read
    ++ encodeInstrsW [Fail].

  Definition sensor_lcode : list LWord :=
       sensor_lcode_init
    ++ sensor_lcode_read
    ++ encodeInstrsLW [Fail].
  Definition sensor_code_len : nat :=
    Eval cbv in length sensor_lcode.

  Definition hash_sensor : Z :=
    hash_concat (hash sensor_begin_addr) (hash sensor_code).

  (* Sealed predicate for sensor enclave *)

  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).

  (* The contract that the read sensor entry point should satisfy.  *)
  Definition sensor_enclave_read_sensor_contract
    (code_b code_e code_a : Addr) (code_v : Version) (ret : LWord) (φ : val → iPropI Σ) : iProp Σ :=
    □ (   na_own logrel_nais ⊤
        ∗ PC ↦ᵣ LCap E code_b code_e code_a code_v
        ∗ r_t0 ↦ᵣ ret
        ∗ (∃ w1, r_t1 ↦ᵣ w1)
        ∗ (∃ w2, r_t2 ↦ᵣ w2)
        ∗ (∃ w3, r_t3 ↦ᵣ w3)
        ∗ ▷ (  na_own logrel_nais ⊤
               ∗ PC ↦ᵣ updatePcPermL ret
               ∗ (∃ b e v, r_t0 ↦ᵣ LCap O b e f42 v
               ∗ (∃ w1, r_t1 ↦ᵣ w1)
               ∗ (∃ w2, r_t2 ↦ᵣ w2)
               ∗ (∃ w3, r_t3 ↦ᵣ w3)
                 -∗ WP Seq (Instr Executable) {{ φ }}))
          -∗ WP Seq (Instr Executable) {{ φ }}).

  (* The sensor enclave only signs the sentry to the read_sensor entry point. *)
  Definition sealed_sensor (w : LWord) : iProp Σ :=
    (∃ b e a v, ⌜ w = LCap E b e a v ⌝ ∧ ∀ ret φ, sensor_enclave_read_sensor_contract b e a v ret φ).

  Definition sealed_sensor_ne : (leibnizO LWord) -n> (iPropO Σ) :=
    λne (w : leibnizO LWord), sealed_sensor w%I.

  #[export] Instance sealed_sensor_persistent (w : LWord) : Persistent (sealed_sensor w).
  Proof. apply _. Qed.

  Definition seal_pred_sensor (τ : OType) := seal_pred τ sealed_sensor.
  Definition valid_sealed_sensor_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_sensor.
  Lemma sealed_sensor_interp (lw : LWord) : sealed_sensor lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "(%b & %e & %a & %v & -> & Hsealed)".
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs) "!> !> ([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    admit.
  Admitted.

  (* Trusted Compute Custom Predicates *)
  Definition sensor_enclave_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      sensor_code
      sensor_begin_addr
      (λ w, False%I)
      sealed_sensor.

  (* ------------------------ *)
  (* --- CLIENT *ENCLAVE* --- *)
  (* ------------------------ *)

  (* CODE LAYOUT:
                                       client_callback
     client      client_init   client_use │ client_fail client_end
       │            │             │       │    │           │
       ▽────────────▽─────────────▽───────▽────▽───────────▽
       │  cap data  │    init     │ use_sensor │ fail      │
       └────────────┴─────────────┴────────────┴───────────┘

     DATA LAYOUT:

      data        data+1                       data+4
       │           │                            │
       ▽───────────▽─────────┬─────────┬────────▽
       │ seal pair │ enc key │  nonce  │ result │
       └───────────┴─────────┴─────────┴────────┘
                   <      argument buffer       >
   *)

  (* Expect:
     - PC := (RX, client, client_end, client_init)
     - r_t0 return pointer
     - r_t1 read_sensor entry point (E, sensor, sensor_end, sensor_read)
     - r_t2 sensor public signing key     (U, σ__s, σ__s+1, σ__s)
     - r_t3 sensor public encryption key  (S, σ__s+1, σ__s+2, σ__s+1)
     Returns:
     - r_t1 client_use_sensor entry point (E, client, client_end, client_use_sensor)
     - r_t2 client public signing key:    (U, σ__c, σ__c+1, σ__c)
     - r_t3 client public encryption key: (S, σ__c+1, σ__c+2, σ__c+1)
   *)
  Definition client_enclave_code_init_instrs
    (client_init client_use client_fail : Z)
    (hash_sensor : Z)
    : list instr :=
    let Eperm := encodePerm E in
    let Sperm := encodeSealPerms (true, false) in
    let Uperm := encodeSealPerms (false, true) in
    [

        (* Get and keep a pointer to a fail instruction. *)
        Mov r_t4 PC;
        Lea r_t4 (client_fail - client_init);

        (* Attest the sensor enclave's signing key. *)
        GetA r_t5 r_t2;             (* r_t5 := ?σ__s *)
        EStoreId r_t5 r_t5;         (* r_t5 := ?hash_sensor *)
        (* Ensure the identity *)
        Sub r_t5 r_t5 hash_sensor;
        Jnz r_t4 r_t5;

        (* Attest the sensor enclave's encryption key. *)
        GetA r_t5 r_t3;             (* r_t5 := ?σ__s+1 *)
        EStoreId r_t5 r_t5;         (* r_t5 := ?hash_sensor *)
        (* Ensure the identity *)
        Sub r_t5 r_t5 hash_sensor;
        Jnz r_t4 r_t5;

        (* Load the data capability. *)
        Lea r_t4 ((client_init - 1) - client_fail);
        Load r_t5 r_t4;             (* r_t4 = cap_data *)

        (* The data capability comes from the adv which controls the cursor.
           Move it to the beginning. *)
        GetB r_t6 r_t5;             (* r_t6 = base (b') of cap_data *)
        GetA r_t7 r_t5;             (* r_t7 = addr (a') of cap_data *)
        Sub r_t6 r_t6 r_t7;         (* r_t6 = base - addr *)
        Lea r_t5 r_t6;              (* r_t5 = cap_data with address pointing to the beginning *)

        Mov r_t6 r_t5;
        (* Store the sensor enclave's entry point.  *)
        Lea r_t6 1;
        Store r_t6 r_t1;
        (* Store the sensor enclave's public signing key *)
        Lea r_t6 1;
        Store r_t6 r_t2;
        (* Store the sensor enclave's public encryption key *)
        Lea r_t6 1;
        Store r_t6 r_t3;
        Mov r_t6 0;

        (* Get the use_sensor entry point. *)
        Mov r_t1 r_t4;
        Lea r_t1 (client_use - (client_init - 1));
        Restrict r_t1 Eperm;    (* r_t1 = (E, client, client_end, client_use) *)

        (* Get the seal/unseal capability.  *)
        Load r_t2 r_t5;         (* r_t2 = seal / unseal capability (SU, σ__c, σ__c+2, σ__c) *)
        Mov r_t3 r_t2;          (* r_t3 = seal / unseal capability (SU, σ__c, σ__c+2, σ__c) *)

        (* Get public signing key, which is (U, σ__c, σ__c+1, σ__c) *)
        GetB r_t4 r_t2;         (* r_t4 = σ__c *)
        Add r_t5 r_t4 1;        (* r_t5 = σ__c+1 *)
        Subseg r_t2 r_t4 r_t5;  (* r_t2 = (SU, σ__c, σ__c+1, σ__c) *)
        Restrict r_t2 Uperm;    (* r_t2 = (U, σ__c, σ__c+1, σ__c) *)

        (* Get public encryption key, which is (S, σ__c+1, σ__c+2, σ__c+1) *)
        Lea r_t3 1%Z;          (* r_t3 = (SU, σ__c+1, σ__c+2, σ__c+1) *)
        GetE r_t4 r_t3;        (* r_t4 = σ__c+2 *)
        Subseg r_t3 r_t5 r_t4; (* r_t3 = (SU, σ__c+1, σ__c+2, σ__c+1) *)
        Restrict r_t3 Sperm;   (* r_t3 = (S, σ__c+1, σ__c+2, σ__c+1) *)

        Jmp r_t0
      ].

  Definition client_enclave_code_init_code
    (client_init client_use client_fail : Z)
    (hash_sensor : Z)
    : list Word :=
    encodeInstrsW (client_enclave_code_init_instrs client_init client_use client_fail hash_sensor).

  Definition client_enclave_code_init_lcode
    (client_init client_use client_fail : Z)
    (hash_sensor : Z)
    : list LWord :=
    encodeInstrsLW (client_enclave_code_init_instrs client_init client_use client_fail hash_sensor).

  (* Expect:
     - PC := (RX, client, client_end, client_use_sensor)
     - r_t1 pointer to buffer (arg). encrypted with the client enclave's encryption key.
     Returns:
   *)

  Definition client_enclave_code_use_sensor
    (client_use client_fail : Z) : list LWord :=

    encodeInstrsLW [
        Jmp r_t0
    ].

  Definition ts_enclaves_map : custom_enclaves_map (Σ := Σ) :=
    {[ hash_sensor := sensor_enclave_pred ]}.

  Lemma wf_ts_enclaves_map :
    custom_enclaves_map_wf ts_enclaves_map.
  Proof.
    rewrite /custom_enclaves_map_wf /ts_enclaves_map.
    split.
    + by rewrite map_Forall_singleton /hash_sensor /=.
    + rewrite map_Forall_singleton.
      apply Forall_forall. cbn.
      intros w Hw.
      repeat (rewrite elem_of_cons in Hw ; destruct Hw as [-> | Hw]; first done).
      by rewrite elem_of_nil in Hw.
  Qed.

  #[export] Instance contract_tsenclaves_map : CustomEnclavesMap :=
    MkCustomEnclavesMap ts_enclaves_map wf_ts_enclaves_map.

End trusted_memory_readout_example.
