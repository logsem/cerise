From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

Section trusted_memory_readout_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    `{reservedaddresses : ReservedAddresses}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* ------------------------ *)
  (* --- SENSOR *ENCLAVE* --- *)
  (* ------------------------ *)

  (* CODE LAYOUT:

     sensor       sensor_init  sensor_read  sensor_end
       │           │            │            │
       ▽───────────▽────────────▽────────────▽
       │ cap data  │    init    │    read    │
       └───────────┴────────────┴────────────┘

     DATA LAYOUT:

      data        data+1             data+2
       │           │                  │
       ▽───────────▽──────────────────▽
       │ seal pair │ enc cap arg_read │
       └───────────┴──────────────────┘
                   <    return buf    >
  *)

  (* Expect:
     - PC := (RX, sensor, sensor_end, sensor_init)
     - r_t0 return pointer
     Returns:
     - read_sensor entry point: r_t1 = (E, sensor, sensor_end, sensor_read)
     - public signing key:      r_t2 = (U, σ__a, σ__a+1, σ__a)
     - public encryption key:   r_t3 = (S, σ__a+1, σ__a+2, σ__a+1)
   *)
  Definition sensor_enclave_code_init (sensor_init sensor_read : Z): list LWord :=
    let Eperm := encodePerm E in
    let Sperm := encodeSealPerms (true, false) in
    let Uperm := encodeSealPerms (false, true) in
    encodeInstrsLW [
        Mov r_t1 PC;            (* r_t1 = (RX, sensor, sensor_end, sensor_init) *)
                                (*        (sensor_init is sensor+1)  *)
        Mov r_t2 r_t1;          (* r_t1 = (RX, sensor, sensor_end, sensor_init) *)

        (* Get the read_sensor entry point. *)
        Lea r_t1 (sensor_read - sensor_init); (* r_t1 = (RX, sensor, sensor_end, sensor_read) *)
        Restrict r_t1 Eperm;    (* r_t1 = (E, sensor, sensor_end, sensor_read) *)

        (* Get the seal/unseal capability.  *)
        Lea r_t2 (-1)%Z;        (* r_t2 = (RX, sensor, sensor_end, sensor) *)
        Load r_t2 r_t2;         (* r_t2 = cap_data *)
        GetB r_t3 r_t2;         (* r_t3 = base (b') of cap_data *)
        GetA r_t4 r_t2;         (* r_t4 = addr (a') of cap_data *)
        Sub r_t3 r_t3 r_t4;     (* r_t3 = base - addr *)
        Lea r_t2 r_t3;          (* r_t2 = cap_data with address pointing to the beginning *)
        Load r_t2 r_t2;         (* r_t2 = seal / unseal capability (SU, σ__a, σ__a+2, σ__a) *)
        Mov r_t3 r_t2;          (* r_t3 = seal / unseal capability (SU, σ__a, σ__a+2, σ__a) *)

        (* Get signing public key, which is (U, σ__a, σ__a+1, σ__a) *)
        GetB r_t4 r_t2;         (* r_t4 = σ__a *)
        Add r_t5 r_t4 1;        (* r_t5 = σ__a+1 *)
        Subseg r_t2 r_t4 r_t5;  (* r_t2 = (SU, σ__a, σ__a+1, σ__a) *)
        Restrict r_t2 Uperm;    (* r_t2 = (U, σ__a, σ__a+1, σ__a) *)

        (* Get encryption public key, which is (S, σ__a+1, σ__a+2, σ__a+1) *)
        Lea r_t3 1%Z;          (* r_t3 = (SU, σ__a+1, σ__a+2, σ__a+1) *)
        GetE r_t4 r_t3;        (* r_t4 = σ__a+2 *)
        Subseg r_t3 r_t5 r_t4; (* r_t3 = (SU, σ__a+1, σ__a+2, σ__a+1) *)
        Restrict r_t3 Sperm;   (* r_t3 = (S, σ__a+1, σ__a+2, σ__a+1) *)
        Jmp r_t0
      ].

  (* Expect:
     - PC := (RX, sensor, sensor_end, sensor_read)
     - r_t0 return pointer
     - r_t1 pointer to buffer (arg_read). encrypted with the sensor enclave's encryption key.
            contains 1. client encryption public key
                     2. nonce value
                     3. space for return value
     Returns:
     - r_t1 signed read only pointer to return buffer of the sensor enclave (RO,data+1 data+2, data+1)
   *)
  Definition sensor_enclave_code_read (sensor sensor_read : Z) : list LWord :=
    let ROperm := encodePerm RO in
    encodeInstrsLW [
        Mov r_t2 PC;                     (* r_t2 = (RX, sensor, sensor_end, sensor_read) *)
        Lea r_t2 (sensor - sensor_read); (* r_t2 = (RX, sensor, sensor_end, sensor) *)
        Load r_t2 r_t2;                  (* r_t2 = cap_data (RW, data, data+2, _) *)
        GetB r_t3 r_t2;                  (* r_t3 = base of cap_data *)
        GetA r_t4 r_t2;                  (* r_t4 = addr of cap_data *)
        Sub r_t3 r_t3 r_t4;              (* r_t3 = base - addr *)
        Lea r_t2 r_t3;                   (* r_t2 = cap_data with address pointing to the beginning *)
                                         (*        (RW, data, data+2, data) *)

        Load r_t3 r_t2;                  (* r_t3 = signing keys (SU, σ__s, σ__s+2, σ__s) *)
        Mov r_t4 r_t3;
        Lea r_t4 1;                      (* r_t4 = encryption keys (SU, σ__s, σ__s+2, σ__s+1) *)

        UnSeal r_t1 r_t4 r_t1;           (* r_t1 = decrypted pointer to buffer (arg_read) *)
        Mov r_t4 r_t1;
        Lea r_t4 2;                      (* r_t4 = pointer to store the result *)

        (* "READ SENSOR" *)
        (* cf https://github.com/proteus-core/cheritree/blob/e969919a30191a4e0ceec7282bb9ce982db0de73/morello/project/enclaveMorello/src/EL1Code/enclavecode/sensor_enclave.S#L106 *)
        Mov r_t5 123;                    (* r_t5 = sensor value *)
        Store r_t4 r_t5;                 (*        Store sensor value through r_t3 *)

        (* Encrypt and sign simultaneously using a memory indirection. *)
        Load r_t4 r_t1;                  (* r_t4 = caller's public encryption key *)
        Seal r_t1 r_t4 r_t1;             (* r_t1 = encrypted pointer to buffer (arg_read) using the caller's encryption key. *)

        Lea r_t2 1;                      (* r_t2 = pointer to return buffer within the sensor's enclaves data section *)
        Store r_t2 r_t1;                 (*        Store encryped pointer for signing *)

        (* Restrict the pointer into the data section to only cover the return buffer. *)
        GetA r_t4 r_t2;                  (* r_t4 = beginning of return buffer *)
        Add r_t5 r_t4 1;                 (* r_t5 = end of return buffer *)
        Subseg r_t2 r_t4 r_t5;           (* r_t2 = restricted pointer to the return buffer *)
        Restrict r_t2 ROperm;            (* r_t2 = read only pointer to the return buffer *)
        Seal r_t1 r_t3 r_t2;             (* r_t1 = read only pointer to the return buffer signed by sensor enclave *)
        Mov r_t2 0;
        Jmp r_t0
      ].

  Definition sensor_init_off : Z := 1.
  Definition sensor_read_off : Z :=
    sensor_init_off + length (sensor_enclave_code_init 0 0).

  Definition sensor_code : list LWord :=
       sensor_enclave_code_init sensor_init_off sensor_read_off
    ++ sensor_enclave_code_read 0 sensor_read_off.

  Definition hash_sensor (ts_addr : Addr) : Z :=
    hash_concat (hash ts_addr) (hash (lword_get_word <$> sensor_code)).

  (* Sealed predicate for sensor enclave *)
  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Definition sealed_sensor : LWord → iProp Σ :=
    λ w, (∃ (b e : Addr) v, ⌜ w = LCap O b e f42 v ⌝)%I.
  Definition sealed_sensor_ne : (leibnizO LWord) -n> (iPropO Σ) :=
    λne (w : leibnizO LWord), sealed_sensor w%I.

  Instance sealed_sensor_persistent (w : LWord) : Persistent (sealed_sensor w).
  Proof. apply _. Qed.

  Definition seal_pred_sensor (τ : OType) := seal_pred τ sealed_sensor.
  Definition valid_sealed_sensor_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_sensor.
  Lemma sealed_sensor_interp (lw : LWord) : sealed_sensor lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.

  (* Trusted Compute Custom Predicates *)
  Definition sensor_enclave_pred ts_addr : CustomEnclave :=
    @MkCustomEnclave Σ
      sensor_code
      ts_addr
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
  Definition client_enclave_code_init
    (client_init client_use client_fail : Z)
    (hash_sensor : Z)
    : list LWord :=
    let Eperm := encodePerm E in
    let Sperm := encodeSealPerms (true, false) in
    let Uperm := encodeSealPerms (false, true) in
    encodeInstrsLW [

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

  Definition ts_enclaves_map ts_addr : custom_enclaves_map :=
    {[hash_sensor ts_addr := sensor_enclave_pred ts_addr]}.

  Lemma wf_ts_enclaves_map (ts_addr : Addr) :
    custom_enclaves_map_wf (ts_enclaves_map ts_addr).
  Proof.
    rewrite /custom_enclaves_map_wf /ts_enclaves_map.
    by rewrite map_Forall_singleton /hash_sensor /=.
  Qed.

End trusted_memory_readout_example.
