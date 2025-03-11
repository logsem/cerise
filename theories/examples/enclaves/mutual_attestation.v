From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

Section sealed_42.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Definition sealed_42 : LWord → iProp Σ :=
    λ w, (∃ b e v, ⌜w = LCap O b e f42 v⌝)%I.
  Definition sealed_42_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_42 w%I.

  Instance sealed_42_persistent (w : LWord) : Persistent (sealed_42 w).
  Proof. apply _. Qed.

  Definition seal_pred_42 (τ : OType) := seal_pred τ sealed_42.
  Definition valid_sealed_42_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_42.
  Lemma sealed_42_interp (lw : LWord) : sealed_42 lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed". iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.
End sealed_42.

Section sealed_43.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Program Definition f43 : Addr := (finz.FinZ 43 eq_refl eq_refl).
  Definition sealed_43 : LWord → iProp Σ :=
    λ w, (∃ b e v, ⌜w = LCap O b e f43 v⌝)%I.
  Definition sealed_43_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_43 w%I.

  Instance sealed_43_persistent (w : LWord) : Persistent (sealed_43 w).
  Proof. apply _. Qed.

  Definition seal_pred_43 (τ : OType) := seal_pred τ sealed_43.
  Definition valid_sealed_43_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_43.
  Lemma sealed_43_interp (lw : LWord) : sealed_43 lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed". iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.
End sealed_43.


Section mutual_attest_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context (assert_entry_point : LWord).

  (* -------------------------------------- *)
  (* ------ MUTUAL ATTEST *ENCLAVES* ------ *)
  (* -------------------------------------- *)

  (* Expects:
     - r_t0 contains return pointer to adv
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  Definition mutual_attest_enclave_A_code_pre : list LWord :=
    encodeInstrsLW [
      (* fetch sign key *)
      (* signs {42}_signed_A *)
      (* call ENCLAVE B with
        r_t1 := {42}_signed_A;
        r_t2 := pub_sign_key_A;
      *)

      (* ---- we only arrive here if B has successfully attested A ---- *)
      (* receives:
         r_t1 := {43}_signed_B;
         r_t2 := pub_sign_key_B;
      *)

      (* CHECK ATTESTS B *)
      (* get idT(B) in r_t2 *)
      (* get hash(idT) in r_t3 *)
      (* get hash_concat(idT(B),idT) in r_t3 *)

      (* compare identity(r_t1) == r_t3 *)

      (* assert unsealed( {43}_signed_B ) = 43 *)

      Jmp r_t0
      (* REST OF CODE OF A *)
    ]
    ++ [assert_entry_point].

  (* Expects:
     - r_t0 contains return pointer to caller
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  Definition mutual_attest_enclave_B_code_pre : list LWord :=
    encodeInstrsLW [
      (* CODE INITIALISATION ENCLAVE B *)

      (* receives:
         r_t1 := {42}_signed_A;
         r_t2 := pub_sign_key_A;
      *)

      (* CHECK ATTESTS A *)
      (* get idT(A) in r_t2 *)
      (* get hash(idT) in r_t3 *)
      (* get hash_concat(idT(A),idT) in r_t3 *)

      (* compare identity(r_t1) == r_t3 *)

      (* assert unsealed( {42}_signed_A ) = 42 *)

      (* fetch sign key *)
      (* signs {43}_signed_B *)
      (* return to ENCLAVE A with
        r_t1 := {43}_signed_B;
        r_t2 := pub_sign_key_B;
      *)
      Jmp r_t0
    ]
    ++ [assert_entry_point].

  Definition mutual_attest_eid_table : list LWord :=
    [
      LWInt (hash (mutual_attest_enclave_A_code_pre));
      LWInt (hash (mutual_attest_enclave_B_code_pre))
    ].

  Definition mutual_attest_enclave_A_code : list LWord :=
    mutual_attest_enclave_A_code_pre ++ mutual_attest_eid_table .

  Definition mutual_attest_enclave_B_code : list LWord :=
    mutual_attest_enclave_B_code_pre ++ mutual_attest_eid_table .

  Definition mutual_attest_enclave_A (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::(mutual_attest_enclave_A_code ).

  Definition mutual_attest_enclave_B (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::(mutual_attest_enclave_B_code ).

  Definition hash_mutual_attest_enclave_A (tc_addr : Addr) : Z :=
    hash_concat (hash tc_addr) (hash mutual_attest_enclave_A_code).

  Definition hash_mutual_attest_enclave_B (tc_addr : Addr) : Z :=
    hash_concat (hash tc_addr) (hash mutual_attest_enclave_B_code).

  (* Trusted Compute Custom Predicates *)
  Definition mutual_attest_enclave_A_pred (ma_addr_A : Addr) : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_A_code
      ma_addr_A
      (λ w, False%I)
      sealed_42.
  Definition mutual_attest_enclave_B_pred (ma_addr_B : Addr) : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_B_code
      ma_addr_B
      (λ w, False%I)
      sealed_43.

  Definition ma_enclaves_map (ma_addr_A ma_addr_B : Addr) : custom_enclaves_map :=
   {[ hash_mutual_attest_enclave_A ma_addr_A := mutual_attest_enclave_A_pred ma_addr_A;
      hash_mutual_attest_enclave_B ma_addr_B := mutual_attest_enclave_B_pred ma_addr_B
   ]}.

  Lemma wf_ma_enclaves_map (ma_addr_A ma_addr_B : Addr) :
    custom_enclaves_map_wf (ma_enclaves_map ma_addr_A ma_addr_B).
  Proof.
    rewrite /custom_enclaves_map_wf /ma_enclaves_map.
    apply (map_Forall_insert_2 (λ (I : Z) (ce : CustomEnclave), _)).
    - by rewrite /hash_mutual_attest_enclave_A /=.
    - by rewrite map_Forall_singleton /hash_mutual_attest_enclave_B /=.
  Qed.

  Lemma tc_contract (ma_addr_A ma_addr_B : Addr) :
    custom_enclave_contract (ma_enclaves_map ma_addr_A ma_addr_B).
  Proof.
  Admitted.

End mutual_attest_example.
