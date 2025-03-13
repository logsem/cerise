From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
(* From cap_machine Require Import macros_new. *)
Open Scope Z_scope.

Section mutual_attest_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context (malloc_entry_point : LWord).
  Context (ma_addr_A ma_addr_B : Addr).

  (* -------------------------------------- *)
  (* ------ MUTUAL ATTEST *ENCLAVES* ------ *)
  (* -------------------------------------- *)

  (* Expects:
     - r_t0 contains return pointer to adv
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  (* Dynamic check:
     data[0] = #A
     data[1] = #A
     data[2] = malloc_entry_point
   *)
  Definition mutual_attest_enclave_A_code : list LWord :=
    encodeInstrsLW [

      (* fetch ?malloc *)
      (* hash ?malloc *)
      (* if #?malloc =! #malloc_entry_point --> fail *)

      (* malloc a buffer b of size 3:
         will be used to communicate
      *)

      (* let idA := hash PC[1::-] *)
      (* let idT := data[0-1] *)

      (* if idA != idT, then fail *)

      (* hash idT *)

      (* let mbA := base(b) % 3 *)
      (* if mbA == 0,
         then we can use
         + mbA[0] for #idT
         + mbA[1] for 42    // attestation of A for B
         + mbA[2] for 1     // attestation of A for main
       *)
      (* if mbA == 1,
         then we can use
         + mbA[0] for 1     // attestation of A for main
         + mbA[1] for #idT
         + mbA[2] for 42    // attestation of A for B
       *)
      (* if mbA == 2,
         then we can use
         + mbA[0] for 42    // attestation of A for B
         + mbA[1] for 1     // attestation of A for main
         + mbA[2] for #idT
       *)

      (* fetch sign key *)
      (* signs { mbA[#idT] }_signed_A *)
      (* signs { mbA[w42] }_signed_A *)

      (* call ENCLAVE B with
        r_t30 := return pointer;
        r_t1  := { mbA[#idT] }_signed_A;
        r_t2  := { mbA[w42] }_signed_A;
        r_t3  := pub_sign_key_A;
      *)

      (* ---- we only arrive here if B has successfully attested A ---- *)
      (* receives:
        r_t1  := { mbB[#idT] }_signed_B;
        r_t2  := { mbB[w43] }_signed_B;
        r_t3  := pub_sign_key_B;
      *)

      (* ATTEST B *)
      (* TODO @June: how do I attest
         the value returned by B
      *)
      (* if mbA[#idT] != mbB[#idT], then fail *)

      (* CHECK ATTESTS B *)
      (* get idT(B) in r_t2 *)
      (* get hash(idT) in r_t3 *)
      (* get hash_concat(idT(B),idT) in r_t3 *)

      (* compare identity(r_t1) == r_t3 *)

      (* assert unsealed( {43}_signed_B ) = 43 *)

      Jmp r_t0
      (* REST OF CODE OF A *)
    ].

  (* Expects:
     - r_t0 contains return pointer to caller
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  Definition mutual_attest_enclave_B_code : list LWord :=
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
    ].

  Definition hash_mutual_attest_A : Z :=
    (hash_concat (hash ma_addr_A) (hash mutual_attest_enclave_A_code)).
  Definition hash_mutual_attest_B : Z :=
    (hash_concat (hash ma_addr_B) (hash mutual_attest_enclave_B_code)).

  Definition mutual_attest_eid_table : list LWord :=
    [ LWInt hash_mutual_attest_A; LWInt hash_mutual_attest_B ].

  Definition mutual_attest_enclave_A (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_A_code.

  Definition mutual_attest_enclave_B (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_B_code.

  Definition mutual_attestN : namespace := nroot .@ "mutual_attest".

  Axiom hash_pos : forall {A : Type} (a : A), hash a >= 0.

  (* Sealed predicate for enclave A *)
  Definition prot_sealed_A (a : Addr) (lw : LWord) : iProp Σ:=
    ⌜ if (decide (a `mod` 3 = 0 ))
      then
        ( (∃ (w' : LWord), lw = LInt (hash [LInt hash_mutual_attest_A; w'])) )
      else
        if (decide (a `mod` 3 = 1 ))
        then lw = LInt 42
        else lw = LInt 1 ⌝%I.

  Definition sealed_enclaveA : LWord → iProp Σ :=
    λ w, (∃ a v,
             ⌜ w = LCap RO a (a^+1)%a a v ⌝
             ∗ ⌜(a+1)%a = Some (a^+1)%a ⌝
             ∗ (inv (logN.@(a, v)) (∃ lw, (a,v) ↦ₐ lw ∗ prot_sealed_A a lw)))%I.
  Definition sealed_enclaveA_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveA w%I.

  Instance sealed_enclaveA_persistent (w : LWord) : Persistent (sealed_enclaveA w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveA (τ : OType) := seal_pred τ sealed_enclaveA.
  Definition valid_sealed_enclaveA_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveA.
  Lemma sealed_enclaveA_interp (lw : LWord) : sealed_enclaveA lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (a v -> HB) "Hinv".
    rewrite fixpoint_interp1_eq /=.
    rewrite finz_seq_between_singleton; auto.
    iApply big_sepL_singleton.
    iExists (λne (lw : leibnizO LWord), prot_sealed_A a lw).
    iFrame "Hinv".
    iSplit.
    - iPureIntro. intros lw. apply _.
    - iNext ; iModIntro.
      iIntros (lw Hlw); cbn.
      destruct (decide (a `mod` 3 = 0)); first (destruct Hlw as [n Hlw] ; simplify_eq; by rewrite fixpoint_interp1_eq).
      destruct (decide (a `mod` 3 = 1)); simplify_eq; by rewrite fixpoint_interp1_eq.
  Qed.


  (* Sealed predicate for enclave B *)
  Definition prot_sealed_B (a : Addr) (lw : LWord) : iProp Σ:=
    ⌜ if (decide ( a `mod` 2 = 0 ) )
      then lw = LInt (hash [LInt hash_mutual_attest_A; LInt hash_mutual_attest_B])
      else lw = LInt 43 ⌝%I.

  Definition sealed_enclaveB : LWord → iProp Σ :=
    λ w, (∃ a v,
             ⌜ w = LCap RO a (a^+1)%a a v ⌝
             ∗ ⌜(a+1)%a = Some (a^+1)%a ⌝
             ∗ (inv (logN.@(a, v)) (∃ lw, (a,v) ↦ₐ lw ∗ prot_sealed_B a lw)))%I.
  Definition sealed_enclaveB_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveB w%I.

  Instance sealed_enclaveB_persistent (w : LWord) : Persistent (sealed_enclaveB w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveB (τ : OType) := seal_pred τ sealed_enclaveB.
  Definition valid_sealed_enclaveB_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveB.
  Lemma sealed_enclaveB_interp (lw : LWord) : sealed_enclaveB lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (a v -> HB) "Hinv".
    rewrite fixpoint_interp1_eq /=.
    rewrite finz_seq_between_singleton; auto.
    iApply big_sepL_singleton.
    iExists (λne (lw : leibnizO LWord), prot_sealed_B a lw).
    iFrame "Hinv".
    iSplit.
    - iPureIntro. intros lw. apply _.
    - iNext ; iModIntro.
      iIntros (lw Hlw); cbn.
      destruct (decide (a `mod` 2 = 0)); simplify_eq; by rewrite fixpoint_interp1_eq.
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



  Lemma mutual_attest_contract :
    custom_enclave_contract ma_enclaves_map.
  Proof.
    rewrite /custom_enclave_contract.
    iIntros (I b e a v b' e' a' v' enclave_data ot ce
      Hwf_cemap Hcode_ce Hot Hb' Hwfbe HIhash Hb He)
      "(#Henclaves_inv & #Hma_inv & #HPenc & #HPsign)".
    clear HIhash.

    rewrite /ma_enclaves_map in Hcode_ce.
    simplify_map_eq.

    assert (I = hash_mutual_attest_A \/ I = hash_mutual_attest_B) as HI.
    { rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      done.
    }
    destruct HI ; simplify_map_eq.
    - rewrite fixpoint_interp1_eq /=.
      iIntros (lregs); iNext ; iModIntro.
      iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
      rewrite /interp_conf.
      iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Htc_data]  & Hna & Hclose)"; [solve_ndisj ..|].
      rewrite /registers_mapsto.
      iExtract "Hrmap" PC as "HPC".
      remember ma_addr_A as pc_b in |- * at 7.
      remember (ma_addr_A ^+ (1%nat + 1))%a as pc_e in |- * at 4.
      (* assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (4%nat + 1))%a) by (subst; solve_addr). *)
  Admitted.

End mutual_attest_example.
