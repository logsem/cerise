From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

(* TODO @June is there a way to define a typeclass or something
   for helping with reasoning and modularity ? *)
Section sealed_42.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Definition sealed_42 : LWord → iProp Σ :=
    λ w, (∃ b e v, ⌜w = LCap O b e f42 v⌝)%I.
  Definition sealed_42_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_42 w%I.

  Instance sealed_42_persistent w : Persistent (sealed_42 w).
  Proof. apply _. Qed.

  Definition seal_pred_42 τ := seal_pred τ sealed_42.
  Definition valid_sealed_cap w τ := valid_sealed w τ sealed_42.
  Lemma sealed_42_interp lw : sealed_42 lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed". iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.
End sealed_42.


Section trusted_memory_readout_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* ------------------------ *)
  (* --- SENSOR *ENCLAVE* --- *)
  (* ------------------------ *)

  (* Expect:
     - PC := (RX, sensor, sensor_end, init)
     - r_t0 return pointer
     Returns:
     - read_sensor entry point: r_t1 = (E, sensor, sensor_end, read)
     - public signing key:      r_t2 = (U, σ__a, σ__a+1, σ__a)
     - public encryption key:   r_t3 = (S, σ__a+1, σ__a+2, σ__a+1)
   *)
  Definition sensor_enclave_code_init (init read : Z): list LWord :=
    let Eperm := encodePerm E in
    let Sperm := encodeSealPerms (true, false) in
    let Uperm := encodeSealPerms (false, true) in
    encodeInstrsLW [
        Mov r_t1 PC;            (* r_t1 = (RX, sensor, sensor_end, init) *)
                                (* (init is sensor+1)  *)
        Mov r_t2 r_t1;          (* r_t1 = (RX, sensor, sensor_end, init) *)

        (* Get the read_sensor entry point. *)
        Lea r_t1 (read - init); (* r_t1 = (RX, sensor, sensor_end, read) *)
        Restrict r_t1 Eperm;    (* r_t1 = (E, sensor, sensor_end, read) *)

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

  Definition sensor_enclave_code_read (sensor read mmio : Z) : list LWord :=
    (* Expect:
     - PC := (RX, sensor, sensor_end, read)
     - r_t0 return pointer
     - r_t1 encrypted pointer to buffer
     *)
    encodeInstrsLW [
        Mov r_t2 PC;              (* r_t2 = (RX, sensor, sensor_end, read) *)
        Lea r_t2 (sensor - read); (* r_t2 = (RX, sensor, sensor_end, sensor) *)
        Load r_t2 r_t2;           (* r_t2 = cap_data *)
        GetB r_t3 r_t2;           (* r_t3 = base (b') of cap_data *)
        GetA r_t4 r_t2;           (* r_t4 = addr (a') of cap_data *)
        Sub r_t3 r_t3 r_t4;       (* r_t3 = base - addr *)
        Lea r_t2 r_t3;            (* r_t2 = cap_data with address pointing to the beginning *)
        Load r_t3 r_t2;           (* r_t3 = seal / unseal capability (SU, σ__a, σ__a+2, σ__a) *)
        Lea r_t3 1;               (* r_t3 = private encryption key (SU, σ__a, σ__a+2, σ__a+1) *)
        (* TODO(STEVE): Can I assume that the pointer points to the beginning of the buffer, i.e. the callers encryption key? *)
        UnSeal r_t1 r_t3 r_t1;    (* r_t1 = decrypted pointer to buffer *)

        Lea r_t2 (mmio - sensor); (* r_t2 = cap_data with address pointing to the mmio address *)
        Load r_t2 r_t2;           (* r_t2 = sensor reading *)

        (* WIP  *)

        Jmp r_t0
      ].

End trusted_memory_readout_example.
