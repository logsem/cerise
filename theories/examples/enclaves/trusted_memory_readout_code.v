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

Section SensorEnclaveData.

  Definition one_shotR : cmra := authR (optionUR unitO).
  Class one_shotG Σ := { #[local] one_shot_inG :: inG Σ one_shotR }.

  Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
  #[export] Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
  Proof. solve_inG. Qed.

  Context {Σ:gFunctors} {oneshotg : one_shotG Σ}.

  Definition pending_auth (γ : gname) : iProp Σ :=
    own γ (● None).
  Definition shot_auth (γ : gname) : iProp Σ :=
    own γ (● Some ()).
  Definition shot_token (γ : gname) : iProp Σ :=
    own γ (◯ Some ()).

  Lemma pending_alloc :
    ⊢ |==> ∃ γ, pending_auth γ.
  Proof. iApply own_alloc. by apply auth_auth_valid. Qed.


  Lemma shoot (γ : gname) :
    pending_auth γ ==∗ shot_auth γ ∗ shot_token γ.
  Proof.
    iIntros "H". rewrite -own_op.
    iApply (own_update with "H").
    by apply auth_update_alloc, alloc_option_local_update.
  Qed.

End SensorEnclaveData.

Section trusted_memory_readout_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {oneshotg : one_shotG Σ}
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
     - public signing key:      r_t1 = (U, σ__s+1, σ__s+2, σ__s+1)
     - read_sensor entry point: r_t2 = Sealed σ__s+1 (E, sensor, sensor_end, sensor_read)
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
      Load r_t1 r_t3;          (* r_t1 = (SU, σ__s, σ__s+2, σ__s) *)
      Lea r_t1 1%Z;            (* r_t1 = (SU, σ__s, σ__s+2, σ__s+1) *)

      (* Construct read_sensor entry point. *)
      Lea r_t2 (read - begin); (* r_t2 = (RX, sensor, sensor_end, sensor_read) *)
      Restrict r_t2 E;         (* r_t2 = (E, sensor, sensor_end, sensor_read) *)

      (* Sign the entry point capability. *)
      Seal r_t2 r_t1 r_t2 ;    (* r_t2 = Sealed σ__s+1 (E, sensor, sensor_end, sensor_read) *)

      (* Create signing public key *)
      GetA r_t3 r_t1;          (* r_t3 = σ__s+1 *)
      GetE r_t4 r_t1;          (* r_t4 = σ__s+2 *)
      Subseg r_t1 r_t3 r_t4;   (* r_t1 = (SU, σ__s+1, σ__s+2, σ__s+1) *)
      Restrict r_t1 U;         (* r_t1 = (U, σ__s+1, σ__s+2, σ__s+1) *)

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
     Clobbers: r_t3 *)
  Definition sensor_instrs_read (begin read : Z) : list instr :=
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
      GetA r_t1 r_t1;                 (* r_t3 = mmio_a *)

      (* Return to caller *)
      Jmp r_t0
    ].

  Definition sensor_precode_read (init read : Z): list Word :=
    encodeInstrsW (sensor_instrs_read init read).
  Definition sensor_prelcode_read (init read : Z): list LWord :=
    encodeInstrsLW (sensor_instrs_read init read).

  Definition sensor_init_off : Z := 0.
  Definition sensor_init_len : nat :=
    Eval cbv in length (sensor_instrs_init 0 0 0 0).
  Definition sensor_read_off : Z :=
    Eval cbv in length (sensor_instrs_init 0 0 0 0).
  Definition sensor_read_len : nat :=
    Eval cbv in length (sensor_instrs_read 0 0).
  Definition sensor_fail_off : Z :=
    Eval cbv in sensor_read_off + sensor_read_len.

  Definition sensor_code_init : list Word :=
    sensor_precode_init (-1)%Z sensor_init_off sensor_read_off sensor_fail_off.
  Definition sensor_lcode_init : list LWord :=
    sensor_prelcode_init (-1)%Z sensor_init_off sensor_read_off sensor_fail_off.

  Definition sensor_code_read : list Word :=
    sensor_precode_read (-1)%Z sensor_read_off.
  Definition sensor_lcode_read : list LWord :=
    sensor_prelcode_read (-1)%Z sensor_read_off.

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

  Definition sensor_one_shot_inv (γ : gname) data_b data_e data_v : iProp Σ :=
    (pending_auth γ ∗ (∃ enclave_data, [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]) ∨
     shot_token γ ∗
       (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∧
        ∃ mmio_b mmio_e mmio_a mmio_v,
           ((data_b ^+ 1)%a, data_v) ↦ₐ LCap RW mmio_b mmio_e mmio_a mmio_v
         ∗ ⌜ withinBounds mmio_b mmio_e mmio_a = true ⌝
         ∗ (mmio_a, mmio_v) ↦ₐ LInt 42)).

  Definition sensor_na_inv pc_v data_b data_e data_a data_v ot γ : iProp Σ :=
    let pc_b := sensor_begin_addr in
    let cf_b := (pc_b ^+ 1)%a in
    (codefrag cf_b pc_v sensor_lcode
     ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
     ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
     ∗ (sensor_one_shot_inv γ data_b data_e data_v)).

  (* The sensor enclave only signs the sentry to the read_sensor entry point. *)
  Definition sealed_sensor (w : LWord) : iProp Σ :=
    let pc_b := sensor_begin_addr in
    let pc_e := (pc_b ^+ (sensor_code_len + 1))%a in
    let cf_b := (pc_b ^+ 1)%a in
    (∃ pc_v data_b data_e data_a data_v ot γ,
          ⌜ w = LCap E pc_b pc_e (cf_b ^+ sensor_read_off)%a pc_v ⌝
        ∗ shot_token γ
        ∗ na_inv logrel_nais (system_invN.@hash_sensor)
            (sensor_na_inv pc_v data_b data_e data_a data_v ot γ)).

  Definition sealed_sensor_ne : (leibnizO LWord) -n> (iPropO Σ) :=
    λne (w : leibnizO LWord), sealed_sensor w%I.

  #[export] Instance sealed_sensor_persistent (w : LWord) : Persistent (sealed_sensor w).
  Proof. apply _. Qed.

  Definition seal_pred_sensor (τ : OType) := seal_pred τ sealed_sensor.
  Definition valid_sealed_sensor_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_sensor.

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
     - r_t1 sensor public signing key (U, σ__s+1, σ__s+2, σ__s+1)
     - r_t2 sensor read entry point (Sealed σ__s+1 (E, sensor, sensor_end, sensor_read))
     Returns:
     - r_t0 return pointer
     - r_t1 client_use_sensor entry point Sealed σ__c+1 (E, client, client_end, client_use_sensor)
     - r_t2 client public signing key:    (U, σ__c+1, σ__c+2, σ__c+1)
   *)
  Definition client_instrs_init (begin init use fail : Z) : list instr :=
    let E := encodePerm E in
    let U := encodeSealPerms (false, true) in
    [ Mov r_t3 PC;             (* r_t3 = (RX, client, client_end, client_init) *)

      (* Get and keep a pointer to a fail instruction. *)
      Lea r_t3 (fail - init);  (* r_t3 = (RX, client, client_end, client_fail) *)

      (* Unseal the read entry point capabilitiy. *)
      UnSeal r_t2 r_t1 r_t2;   (* r_t2 = ?(E, sensor, sensor_end, sensor_read) *)

      (* Attest the sensor enclave's read entry point. *)
      GetA r_t4 r_t1;          (* r_t4 = ?σ__s *)
      EStoreId r_t1 r_t4;      (* r_t1 = ?hash_sensor *)
      Sub r_t1 r_t1 hash_sensor;
      Jnz r_t3 r_t1;

      (* Get the data capability *)
      Lea r_t3 (begin - fail); (* r_t3 = (RX, client, client_end, client) *)
      Load r_t1 r_t3;          (* r_t1 = (RW, data, data_end, addr) *)
      GetB r_t4 r_t1;          (* r_t4 = data *)
      GetA r_t5 r_t1;          (* r_t5 = addr *)
      Sub r_t4 r_t4 r_t5;      (* r_t4 = data - addr *)
      Lea r_t1 r_t4;           (* r_t1 = (RW, data, data_end, data) *)

      (* Store read sensor capability in private data. *)
      Lea r_t1 1;              (* r_t1 = (RW, data, data_end, data+1) *)
      Store r_t1 r_t2;

      (* Get the seal/unseal master capability and switch to signing.  *)
      Lea r_t1 (-1)%Z;         (* r_t1 = (RW, data, data_end, data) *)
      Load r_t2 r_t1;          (* r_t2 = (SU, σ__c, σ__c+2, σ__c) *)
      Lea r_t2 1%Z;            (* r_t2 = (SU, σ__c, σ__c+2, σ__c+1) *)

      (* Construct read_sensor entry point. *)
      Lea r_t3 (use - begin);  (* r_t3 = (RX, client, client_end, client_use) *)
      Restrict r_t3 E;         (* r_t3 = (E, client, client_end, client_use) *)

      (* Sign the entry point capability. *)
      Seal r_t1 r_t2 r_t3;     (* r_t1 = Sealed σ__c+1 (E, client, client_end, client_use) *)

      (* Create signing public key *)
      GetA r_t3 r_t1;          (* r_t3 = σ__c+1 *)
      GetE r_t4 r_t1;          (* r_t4 = σ__c+2 *)
      Subseg r_t2 r_t3 r_t4;   (* r_t2 = (SU, σ__c+1, σ__c+2, σ__c+1) *)
      Restrict r_t2 U;         (* r_t2 = (U, σ__c+1, σ__c+2, σ__c+1) *)

      Jmp r_t0
    ].

  Definition client_precode_init (begin init use fail : Z): list Word :=
    encodeInstrsW (client_instrs_init begin init use fail).

  Definition client_prelcode_init (begin init use fail : Z): list LWord :=
    encodeInstrsLW (client_instrs_init begin init use fail).

  (* Expect:
     - PC := (RX, client, client_end, client_use)
     - r_t0 return pointer
     Returns:
     - r_t0 return pointer
     - r_t1 sensor addr (mmio_a)
     - r_t2 return value (= 84)
     Clobbers: r_t3, r_t4 *)
  Definition client_instrs_use (begin use : Z) : list instr :=
    [ Mov r_t1 PC;                    (* r_t1 = (RX, client, client_end, client_use) *)

      Lea r_t1 (begin - use);         (* r_t1 = (RX, client, client_end, client) *)
      Load r_t1 r_t1;                 (* r_t1 = (RW, data_b, data_e, ?a) *)
      GetB r_t2 r_t1;                 (* r_t2 = data_b *)
      GetA r_t3 r_t1;                 (* r_t3 = ?a *)
      Sub r_t2 r_t2 r_t3;             (* r_t2 = data_b - ?a *)
      Lea r_t1 r_t2;                  (* r_t1 = (RW, data_b, data_e, data_b) *)

      (* Load sensor enclave read entry point *)
      Lea r_t1 1;                     (* r_t1 = (RW, data_b, data_e, data_b+1) *)
      Load r_t1 r_t1;                 (* r_t1 = (E, sensor, sensor_end, sensor_read) *)

      (* Save return pointer to a register unclobbered by sensor read *)
      Mov r_t4 r_t0;                  (* r_t4 = return pointer *)

      (* Setup callback and jump to read sensor entry point. *)
      Mov r_t0 PC;
      Lea r_t0 3;                     (* r_t0 = use callback *)
      Jmp r_t1;

      (* Use Callback
           Expect:
           - r_t1 sensor addr (mmio_a)
           - r_t2 sensor read return value (= 42) *)

      (* Perform computation on the sensor value *)
      Add r_t2 r_t2 r_t2;             (* r_t2 = 84 *)

      (* Return to caller *)
      Jmp r_t0
    ].

  Definition client_precode_use (init use : Z): list Word :=
    encodeInstrsW (client_instrs_use init use).
  Definition client_prelcode_use (init use : Z): list LWord :=
    encodeInstrsLW (client_instrs_use init use).

  Definition client_init_off : Z := 0.
  Definition client_init_len : nat :=
    Eval cbv in length (client_instrs_init 0 0 0 0).
  Definition client_use_off : Z :=
    Eval cbv in length (client_instrs_init 0 0 0 0).
  Definition client_use_len : nat :=
    Eval cbv in length (client_instrs_use 0 0).
  Definition client_fail_off : Z :=
    Eval cbv in client_use_off + client_use_len.

  Definition client_code_init : list Word :=
    client_precode_init (-1)%Z client_init_off client_use_off client_fail_off.
  Definition client_lcode_init : list LWord :=
    client_prelcode_init (-1)%Z client_init_off client_use_off client_fail_off.

  Definition client_code_use : list Word :=
    client_precode_use (-1)%Z client_use_off.
  Definition client_lcode_use : list LWord :=
    client_prelcode_use (-1)%Z client_use_off.

  Definition client_code : list Word :=
       client_code_init
    ++ client_code_use
    ++ encodeInstrsW [Fail].

  Definition client_lcode : list LWord :=
       client_lcode_init
    ++ client_lcode_use
    ++ encodeInstrsLW [Fail].
  Definition client_code_len : nat :=
    Eval cbv in length client_lcode.

  Definition hash_client : Z :=
    hash_concat (hash client_begin_addr) (hash client_code).

  (* Sealed predicate for client enclave *)

  Program Definition f84 : Addr := (finz.FinZ 84 eq_refl eq_refl).

  Definition client_one_shot_inv (γ : gname) data_b data_e data_v : iProp Σ :=
    (pending_auth γ ∗ (∃ enclave_data, [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]) ∨
     shot_token γ ∗
       (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∧
        ∃ mmio_b mmio_e mmio_a mmio_v,
           ((data_b ^+ 1)%a, data_v) ↦ₐ LCap RW mmio_b mmio_e mmio_a mmio_v
         ∗ ⌜ withinBounds mmio_b mmio_e mmio_a = true ⌝
         ∗ (mmio_a, mmio_v) ↦ₐ LInt 42)).

  Definition client_na_inv pc_v data_b data_e data_a data_v ot γ : iProp Σ :=
    let pc_b := client_begin_addr in
    let cf_b := (pc_b ^+ 1)%a in
    (codefrag cf_b pc_v client_lcode
     ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
     ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
     ∗ (client_one_shot_inv γ data_b data_e data_v)).

  (* The client enclave only signs the sentry to the use entry point. *)
  Definition sealed_client (w : LWord) : iProp Σ :=
    let pc_b := client_begin_addr in
    let pc_e := (pc_b ^+ (client_code_len + 1))%a in
    let cf_b := (pc_b ^+ 1)%a in
    (∃ pc_v data_b data_e data_a data_v ot γ,
          ⌜ w = LCap E pc_b pc_e (cf_b ^+ client_use_off)%a pc_v ⌝
        ∗ shot_token γ
        ∗ na_inv logrel_nais (system_invN.@hash_client)
            (client_na_inv pc_v data_b data_e data_a data_v ot γ)).

  Definition sealed_client_ne : (leibnizO LWord) -n> (iPropO Σ) :=
    λne (w : leibnizO LWord), sealed_client w%I.

  #[export] Instance sealed_client_persistent (w : LWord) : Persistent (sealed_client w).
  Proof. repeat (apply bi.exist_persistent; intros). apply _. Qed.

  Definition seal_pred_client (τ : OType) := seal_pred τ sealed_client.
  Definition valid_sealed_client_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_client.

  (* Trusted Compute Custom Predicates *)
  Definition client_enclave_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      client_code
      client_begin_addr
      (λ w, False%I)
      sealed_client.

  (* ------------------------ *)
  (* ---   ENCLAVES MAP   --- *)
  (* ------------------------ *)

  Definition ts_enclaves_map : custom_enclaves_map (Σ := Σ) :=
    {[ hash_sensor := sensor_enclave_pred;
       hash_client := client_enclave_pred
    ]}.

  Lemma wf_ts_enclaves_map :
    custom_enclaves_map_wf ts_enclaves_map.
  Proof.
    rewrite /custom_enclaves_map_wf /ts_enclaves_map.
    split.
    - apply (map_Forall_insert_2 (λ (I : Z) (ce : CustomEnclave), _)).
      + by rewrite /hash_sensor /=.
      + by rewrite map_Forall_singleton /hash_client /=.
    - apply (map_Forall_insert_2 (λ (I : Z) (ce : CustomEnclave), _)).
      + cbn.
        rewrite /encodeInstrW.
        apply Forall_forall.
        intros w Hw.
        repeat (rewrite elem_of_cons in Hw ; destruct Hw as [-> | Hw]; first done).
        by rewrite elem_of_nil in Hw.
      + rewrite map_Forall_singleton; cbn.
        rewrite /encodeInstrW.
        apply Forall_forall.
        intros w Hw.
        repeat (rewrite elem_of_cons in Hw ; destruct Hw as [-> | Hw]; first done).
        by rewrite elem_of_nil in Hw.
  Qed.

  #[export] Instance contract_tsenclaves_map : CustomEnclavesMap :=
    MkCustomEnclavesMap ts_enclaves_map wf_ts_enclaves_map.

End trusted_memory_readout_example.
