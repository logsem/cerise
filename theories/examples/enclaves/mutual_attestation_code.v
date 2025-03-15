From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel proofmode.

(* -------------------------------------- *)
(* --------------- AXIOMS --------------- *)
(* -------------------------------------- *)

Axiom hash_concat_app : forall `{MachineParameters} {A : Type} (la la' : list A),
  hash (la++la') = hash_concat (hash la) (hash la').
Axiom hash_concat_assoc : forall `{MachineParameters}, Assoc eq hash_concat.
Instance hash_concat_Assoc `{MachineParameters} : Assoc eq hash_concat := hash_concat_assoc.

Class MutualAttestation := {
    ma_addr_A : Addr;
    ma_addr_B : Addr
  }.

Section mutual_attest_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.

  (* --------------------------------------- *)
  (* ------- MUTUAL ATTEST ENCLAVE A ------- *)
  (* --------------------------------------- *)

  Definition mutual_attest_enclave_A_mod_encoding_42 : list LWord :=
    encodeInstrsLW [

        (* r1 := (RW, data_b, data_e, data_b) *)
        (* prepare {42} *)
        GetB r_t2 r_t1;         (* r2 := data_b *)
        Add r_t3 r_t2 1;        (* r3 := data_b + 1 *)
        Mod r_t4 r_t2 2;        (* r4 := data_b % 2 *)

        (* if x%2 = 0 then data_b=[42] else  data_b+1=[42] *)
        Mov r_t5 PC;
        Lea r_t5 6;
        Jnz r_t5 r_t4;

        (* case x%2 == 0 *)
        Subseg r_t1 r_t2 r_t3;  (* r1 := (RW, data_b, data_b+1, data_b) *)
        Lea r_t5 2;
        Jmp r_t5;

        (* case x%2 == 1 *)
        Add r_t4 r_t3 1;        (* r4 := data_b + 2 *)
        Subseg r_t1 r_t3 r_t4;  (* r1 := (RW, data_b+1, data_b+2, data_b) *)

        (* continue here *)
        Sub r_t3 42 r_t2;       (* r3 := 42 - data_b *)
        Lea r_t1 r_t3;          (* r1 :=  (RW, data_b, data_b+1, 42) if data_b%2 = 0 *)
                                (* r1 :=  (RW, data_b+1 , data_b+2, 42) if data_b%2 = 1 *)
        Restrict r_t1 (encodePerm O)
      ].

  Definition mutual_attest_enclave_A_mod_encoding_1 : list LWord :=
    encodeInstrsLW [

        (* r1 := (RW, data_b, data_e, data_b) *)
        (* prepare {42} *)
        GetB r_t2 r_t1;         (* r2 := data_b *)
        Add r_t3 r_t2 1;        (* r3 := data_b + 1 *)
        Mod r_t4 r_t2 2;        (* r4 := data_b % 2 *)

        (* if x%2 = 0 then data_b+1=[1] else data_b=[1] *)
        Mov r_t5 PC;
        Lea r_t5 7;
        Jnz r_t5 r_t4;

        (* case x%2 == 0 *)
        Add r_t4 r_t3 1;        (* r4 := data_b + 2 *)
        Subseg r_t1 r_t3 r_t4;  (* r1 := (RW, data_b+1, data_b+2, data_b) *)
        Lea r_t5 1;
        Jmp r_t5;

        (* case x%2 == 1 *)
        Subseg r_t1 r_t2 r_t3;  (* r1 := (RW, data_b, data_b+1, data_b) *)

        (* continue here *)
        Sub r_t3 1 r_t2;        (* r3 := 1 - data_b *)
        Lea r_t1 r_t3;          (* r1 := (RW, data_b, data_b+1, 1) if data_b%2 = 1 *)
                                (* r1 := (RW, data_b+1 , data_b+2, 1) if data_b%2 = 0 *)
        Restrict r_t1 (encodePerm O)
      ].

  (* Expects:
     - r_t0 contains return pointer to adv
   *)
  Definition mutual_attest_enclave_A_code_pre : list LWord :=
    let size_idT : Z := 2 in
    let offset_idA : Z := 0 in
    let offset_idB : Z := 1 in
    encodeInstrsLW [

      (* SEND {(O,a,a+1,42)}_signed_A ; with a%2=0 *)

      (* fetch data_cap *)
      Mov r_t5 PC;          (* r5 := (RX, pc_b, pc_e, pc_a) *)
      GetA r_t1 r_t5;       (* r1 := pc_a *)
      GetB r_t2 r_t5;       (* r2 := pc_b *)
      Sub r_t1 r_t2 r_t1;   (* r1 := pc_b - pc_a *)
      Lea r_t5 r_t1;        (* r5 := (RX, pc_b, pc_e, pc_b) *)
      Load r_t1 r_t5;       (* r1 := (RW, data_b, data_e, data_a) *)

      (* fetch sign_key *)
      GetA r_t2 r_t1;       (* r2 := data_a *)
      GetB r_t3 r_t1;       (* r3 := data_b *)
      Sub r_t2 r_t3 r_t2;   (* r2 := data_b - data_a *)
      Lea r_t1 r_t2;        (* r1 := (RW, data_b, data_e, data_b) *)
      Load r_t6 r_t1       (* r6 := [SU, σ, σ+2, σ] *)
      ]
      ++ mutual_attest_enclave_A_mod_encoding_42
      ++ encodeInstrsLW [
        (* r1 :=  (RW, data_b, data_b+1, 42) *)
        (* r6 := [SU, σ, σ+2, σ] *)

        (* sign {42} *)
        Lea r_t6 1;            (* r6 := (SU, σ+1, σ+2, σ+1) *)
        Seal r_t1 r_t6 r_t1;

        GetA r_t3 r_t6;        (* r3 := σ+1 *)
        Add r_t4 r_t3 1;       (* r4 := σ+2 *)
        Subseg r_t6 r_t3 r_t4; (* r6 := (SU, σ+1, σ+2, σ+1) *)
        Restrict r_t6 (encodeSealPerms (false,true));

        (* create return pointer *)
        Mov r_t3 PC;
        Lea r_t3 8;
        Restrict r_t3 (encodePerm E);

        (* clear regs and jmp to adv *)
        Mov r_t2 r_t6;
        Mov r_t4 0;
        Mov r_t5 0;
        Mov r_t6 0;
        Jmp r_t0]
      ++ encodeInstrsLW [
        (* return from adversary *)
        (* Expect:
           r0 := ret_word
           r1 := {(RO, b, e, 43}_signed_B, with (b%2 = 0)
           r2 := pub_signed_B
         *)

        (* CHECK ATTESTS B *)
        (* get idT(B) in r_t3 *)

        Mov r_t4 PC;                (* r4 := (RX, pc_b, pc_e, pc_a) *)
        GetA r_t5 r_t4;             (* r5 := pc_a *)
        GetE r_t6 r_t4;             (* r6 := pc_e *)
        Sub r_t5 r_t6 r_t5;         (* r5 := pc_e - pc_a *)
        Lea r_t4 r_t5;              (* r4 := (RX, pc_b, pc_e, pc_e) *)
        Lea r_t4 (-size_idT)%Z;     (* r4 := (RX, pc_b, pc_e, a_idT) *)

        Mov r_t3 r_t4;              (* r3 := (RX, pc_b, pc_e, a_idT) *)
        Lea r_t3 offset_idB;        (* r3 := (RX, pc_b, pc_e, a_idT(B)) *)
        Load r_t3 r_t3;             (* r3 := idT(B) *)

        (* get hash(idT) in r_t4 *)
        GetA r_t5 r_t4;             (* r5 := a_idT *)
        Subseg r_t4 r_t5 r_t6;      (* r4 := (RX, a_idT pc_e, a_idT) *)
        Hash r_t4 r_t4;             (* r4 := #[a_idT;pc_E] *)

        (* get hash_concat(idT(B),idT) in r_t3 *)
        HashConcat r_t3 r_t3 r_t4;  (* r3 := idT(B) || #[a_idT;pc_E] *)

        (* compare identity(r_t1) == r_t3 *)
        GetOType r_t4 r_t1;         (* r4 := ?signed_B *)
        Add r_t4 r_t4 1;            (* r5 := if is_sealed(r_t1) = false then 0 else not0 *)

        (* if  is_sealed(r_t1) then continue else fail *)
        Mov r_t5 PC;
        Lea r_t5 4;
        Jnz r_t5 r_t4;
        Fail;

        GetOType r_t5 r_t1;         (* r5 := ?signed_B *)
        EStoreId r_t4 r_t5;         (* r4 := I_signed_B *)
        Sub r_t3 r_t3 r_t4;         (* r3 := (idT(B) || #[a_idT;pc_E]) - ?signed_B *)

        (* if ?signed_B != (idT(B) || #[a_idT;pc_E])
         then Fail
         else continue *)
        Mov r_t5 PC;
        Lea r_t5 5;
        Jnz r_t5 r_t3;
        Lea r_t5 1;
        Jmp r_t5;
        Fail;

        UnSeal r_t1 r_t2 r_t1;      (* r1 := unsealed( {(RO,a, _, 43)}_signed_B ) *)
        (* if (unsealed( {43}_signed_A ) != 43)
         then Fail
         else continue
         *)

        GetB r_t2 r_t1;             (* r2 := a *)
        Mod r_t2 r_t2 2;            (* r2 := a%2 *)
        (* if a%2 != 0 then Fail else continue *)
        Mov r_t5 PC;
        Lea r_t5 5;
        Jnz r_t5 r_t2;
        Lea r_t5 1;
        Jmp r_t5;
        Fail;

        GetA r_t1 r_t1; (* r1 := ?43 *)
        (* if ?43 != 43 then Fail else continue *)
        Sub r_t1 r_t1 43;
        Lea r_t5 6;
        Jnz r_t5 r_t2;
        Lea r_t5 1;
        Jmp r_t5;
        Fail;

        (* Confirmation attestation *)
        (* fetch data_cap *)
        GetA r_t1 r_t5;
        GetB r_t2 r_t5;
        Sub r_t1 r_t2 r_t1;
        Lea r_t5 r_t1;
        Load r_t1 r_t5;       (* r1 := (RW, data_b, data_e, data_a) *)

        (* fetch sign_key *)
        GetA r_t2 r_t1;
        GetB r_t3 r_t1;      (* r3 := data_b *)
        Sub r_t2 r_t3 r_t2;
        Lea r_t1 r_t2;       (* r1 := (RW, data_b, data_e, data_b) *)
        Load r_t6 r_t1      (* r6 := [SU, σ, σ+2, σ] *)
      ]
      ++ mutual_attest_enclave_A_mod_encoding_1
      ++ encodeInstrsLW [
        (* continue here  *)
        (* r1 := (RW, data_b, data_b+1, 1) *)
        (* r6 := [SU, σ, σ+2, σ] *)

        (* sign x and sign x+1 *)
        Lea r_t6 1;            (* r6 := (SU, σ+1, σ+2, σ+1) *)
        Seal r_t1 r_t6 r_t1;

        GetA r_t3 r_t6;        (* r3 := σ+1 *)
        Add r_t4 r_t3 1;       (* r4 := σ+2 *)
        Subseg r_t6 r_t3 r_t4; (* r6 := (SU, σ+1, σ+2, σ+1) *)
        Restrict r_t6 (encodeSealPerms (false,true));

        (* clear regs and jmp to adv *)
        Mov r_t3 r_t6;
        Mov r_t4 0;
        Mov r_t5 0;
        Mov r_t6 0;
        Jmp r_t0
    ].

  (* --------------------------------------- *)
  (* ------- MUTUAL ATTEST ENCLAVE B ------- *)
  (* --------------------------------------- *)


  Definition mutual_attest_enclave_B_mod_encoding : list LWord :=
    encodeInstrsLW [
        (* if x%2 = 0 then mb=[42;1] else  mb=[1;42] *)
        Mod r_t3 r_t2 2;
        Mov r_t5 PC;
        Lea r_t5 9;
        Jnz r_t5 r_t3;

        (* case x%2 == 0 *)
        Sub r_t3 43 r_t2;
        Lea r_t1 r_t3; (*  r1 :=  (RW, data_b, data_b+1, 42) *)
        Sub r_t3 1 r_t2;
        Lea r_t4 r_t3; (*  r4 :=  (RW, data_b+1, data_b+2, 1) *)
        Lea r_t5 4;
        Jmp r_t5;

        (* case x%2 == 1 *)
        Sub r_t3 1 r_t2;
        Lea r_t1 r_t3; (*  r1 :=  (RW, data_b, data_b+1, 1) *)
        Sub r_t3 43 r_t2;
        Lea r_t4 r_t3 (*  r4 :=  (RW, data_b+1, data_b+2, 42) *)
      ].

  (* Expects:
     - r_t0 contains return pointer to caller
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  Definition mutual_attest_enclave_B_code_pre : list LWord :=
    let size_idT : Z := 2 in
    let offset_idA : Z := 0 in
    let offset_idB : Z := 1 in
    encodeInstrsLW [
      (* CODE INITIALISATION ENCLAVE B *)

      (* receives:
         r_t1 := {42}_signed_A;
         r_t2 := pub_sign_key_A;
      *)

      (* CHECK ATTESTS A *)
      (* get idT(A) in r_t3 *)

      Mov r_t4 PC;                (* r4 := (RX, pc_b, pc_e, pc_a) *)
      GetA r_t5 r_t4;             (* r5 := pc_a *)
      GetE r_t6 r_t4;             (* r6 := pc_e *)
      Sub r_t5 r_t6 r_t5;         (* r5 := pc_e - pc_a *)
      Lea r_t4 r_t5;              (* r4 := (RX, pc_b, pc_e, pc_e) *)
      Lea r_t4 (-size_idT)%Z;     (* r4 := (RX, pc_b, pc_e, a_idT) *)

      Mov r_t3 r_t4;              (* r3 := (RX, pc_b, pc_e, a_idT) *)
      Lea r_t3 offset_idA;        (* r3 := (RX, pc_b, pc_e, a_idT(A)) *)
      Load r_t3 r_t3;             (* r3 := idT(A) *)

      (* get hash(idT) in r_t4 *)
      GetA r_t5 r_t4;             (* r5 := a_idT *)
      Subseg r_t4 r_t5 r_t6;      (* r4 := (RX, a_idT pc_e, a_idT) *)
      Hash r_t4 r_t4;             (* r4 := #[a_idT;pc_E] *)

      (* get hash_concat(idT(A),idT) in r_t3 *)
      HashConcat r_t3 r_t3 r_t4;  (* r3 := idT(A) || #[a_idT;pc_E] *)

      (* compare identity(r_t1) == r_t3 *)
      GetOType r_t4 r_t1;         (* r4 := ?signed_A *)
      Add r_t4 r_t4 1;            (* r5 := if is_sealed(r_t1) = false then 0 else not0 *)

      (* if  is_sealed(r_t1) then continue else fail *)
      Mov r_t5 PC;
      Lea r_t5 4;
      Jnz r_t5 r_t4;
      Fail;

      GetOType r_t5 r_t1;         (* r5 := ?signed_A *)
      EStoreId r_t4 r_t5;         (* r4 := I_signed_A *)
      Sub r_t3 r_t3 r_t4;         (* r3 := (idT(A) || #[a_idT;pc_E]) - ?signed_A*)

      (* if ?signed_A != (idT(A) || #[a_idT;pc_E])
         then Fail
         else continue *)
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t3;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      UnSeal r_t1 r_t2 r_t1;      (* r1 := unsealed( {(RO,a, _, 42)}_signed_A ) *)
      (* if (unsealed( {42}_signed_A ) != 42)
         then Fail
         else continue
       *)

      GetB r_t2 r_t1;             (* r2 := a *)
      Mod r_t2 r_t2 2;            (* r2 := a%2 *)
      (* if a%2 != 0 then Fail else continue *)
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      GetA r_t1 r_t1; (* r1 := ?42 *)
      (* if ?42 != 42 then Fail else continue *)
      Sub r_t1 r_t1 42;
      Lea r_t5 6;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      (* fetch data_cap *)
      GetA r_t1 r_t5;
      GetB r_t2 r_t5;
      Sub r_t1 r_t2 r_t1;
      Lea r_t5 r_t1;
      Load r_t1 r_t5;       (* r1 := (RW, data_b, data_e, data_a) *)

      (* fetch sign_key *)
      GetA r_t2 r_t1;
      GetB r_t3 r_t1;      (* r3 := data_b *)
      Sub r_t2 r_t3 r_t2;
      Lea r_t1 r_t2;       (* r1 := (RW, data_b, data_e, data_b) *)
      Load r_t6 r_t1;      (* r6 := [SU, σ, σ+2, σ] *)


      Mov r_t4 r_t1;      (* r4 := (RW, data_b, data_e, data_b) *)
      GetB r_t2 r_t1;     (* r2 := data_b *)
      Add r_t3 r_t2 1;    (* r3 := data_b + 1 *)
      Subseg r_t1 r_t2 r_t3; (* r1 := (RW, data_b, data_b+1, data_b) *)
      Add r_t5 r_t3 1;    (* r5 := data_b + 2 *)
      Subseg r_t4 r_t3 r_t5 (* r4 := (RW, data_b+1, data_b+2, data_b) *)
      ]
      ++ mutual_attest_enclave_B_mod_encoding
      ++ encodeInstrsLW [
      (* continue here  *)
      Restrict r_t1 (encodePerm O);
      Restrict r_t4 (encodePerm O);

      (* sign x and sign x+1 *)
      Lea r_t6 1;            (* r6 := (SU, σ+1, σ+2, σ+1) *)
      Seal r_t1 r_t6 r_t1;
      Seal r_t2 r_t6 r_t4;

      GetA r_t3 r_t6;        (* r3 := σ+1 *)
      Add r_t4 r_t3 1;       (* r4 := σ+2 *)
      Subseg r_t6 r_t3 r_t4; (* r6 := (SU, σ+1, σ+2, σ+1) *)
      Restrict r_t6 (encodeSealPerms (false,true));

      (* clear regs and jmp to adv *)
      Mov r_t3 r_t6;
      Mov r_t4 0;
      Mov r_t5 0;
      Mov r_t6 0;
      Jmp r_t0
    ].

  (* Enclave Identity Table --- pre-hashed code *)
  Definition hash_mutual_attest_A_pre : Z :=
    hash_concat (hash ma_addr_A) (hash mutual_attest_enclave_A_code_pre).
  Definition hash_mutual_attest_B_pre : Z :=
    hash_concat (hash ma_addr_B) (hash mutual_attest_enclave_B_code_pre).

  Definition mutual_attest_eid_table : list LWord :=
    [ LWInt hash_mutual_attest_A_pre ; LWInt hash_mutual_attest_B_pre].


  (* Fully hashed enclaves --- machine hashed enclaves *)
  Definition mutual_attest_enclave_A_code : list LWord :=
   (mutual_attest_enclave_A_code_pre ++ mutual_attest_eid_table).
  Definition mutual_attest_enclave_B_code : list LWord :=
   (mutual_attest_enclave_B_code_pre ++ mutual_attest_eid_table).

  Definition hash_mutual_attest_A : Z :=
    hash_concat (hash ma_addr_A) (hash mutual_attest_enclave_A_code).
  Definition hash_mutual_attest_B : Z :=
    hash_concat (hash ma_addr_B) (hash mutual_attest_enclave_B_code).

  Definition mutual_attest_enclave_A (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_A_code ++ mutual_attest_eid_table.
  Definition mutual_attest_enclave_B (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_B_code  ++ mutual_attest_eid_table.



  (* Sealed predicate for enclave A *)
  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Program Definition f1 : Addr := (finz.FinZ 1 eq_refl eq_refl).
  Definition prot_sealed_A (a : Addr) : Addr :=
    if (decide (a `mod` 2%nat = 0 )%Z) then f42 else f1.

  Definition sealed_enclaveA : LWord → iProp Σ :=
    λ w, (∃ (b e : Addr) v,
             ⌜ w = LCap O b e (prot_sealed_A b) v ⌝)%I.
  Definition sealed_enclaveA_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveA w%I.

  Instance sealed_enclaveA_persistent (w : LWord) : Persistent (sealed_enclaveA w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveA (τ : OType) := seal_pred τ sealed_enclaveA.
  Definition valid_sealed_enclaveA_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveA.
  Lemma sealed_enclaveA_interp (lw : LWord) : sealed_enclaveA lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.




  (* Sealed predicate for enclave B *)
  Program Definition f43 : Addr := (finz.FinZ 43 eq_refl eq_refl).
  Definition prot_sealed_B (a : Addr) : Addr :=
    if (decide (a `mod` 2%nat = 0 )%Z) then f43 else f1.

  Definition sealed_enclaveB : LWord → iProp Σ :=
    λ w, (∃ (b e : Addr) v,
             ⌜ w = LCap O b e (prot_sealed_B b) v ⌝)%I.
  Definition sealed_enclaveB_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveB w%I.

  Instance sealed_enclaveB_persistent (w : LWord) : Persistent (sealed_enclaveB w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveB (τ : OType) := seal_pred τ sealed_enclaveB.
  Definition valid_sealed_enclaveB_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveB.
  Lemma sealed_enclaveB_interp (lw : LWord) : sealed_enclaveB lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.




  (* Trusted Compute Custom Predicates *)
  Definition mutual_attest_enclave_A_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_A_code
      ma_addr_A
      (λ w, False%I)
      sealed_enclaveA.
  Definition mutual_attest_enclave_B_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_B_code
      ma_addr_B
      (λ w, False%I)
      sealed_enclaveB.

  Definition ma_enclaves_map : custom_enclaves_map :=
   {[ hash_mutual_attest_A := mutual_attest_enclave_A_pred;
      hash_mutual_attest_B := mutual_attest_enclave_B_pred
   ]}.

  Lemma wf_ma_enclaves_map :
    custom_enclaves_map_wf ma_enclaves_map.
  Proof.
    rewrite /custom_enclaves_map_wf /ma_enclaves_map.
    apply (map_Forall_insert_2 (λ (I : Z) (ce : CustomEnclave), _)).
    - by rewrite /hash_mutual_attest_A /=.
    - by rewrite map_Forall_singleton /hash_mutual_attest_B /=.
  Qed.

End mutual_attest_example.
