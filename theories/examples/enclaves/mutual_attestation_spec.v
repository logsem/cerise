From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import mutual_attestation_code.
From cap_machine Require Import
  mutual_attestation_code
  mutual_attestation_A_spec
  mutual_attestation_B_spec.


Section mutual_attest_main.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.


  (* -------------------------------------------------- *)
  (* ------------------- ENCLAVES --------------------- *)
  (* -------------------------------------------------- *)

  Lemma mutual_attest_contract :
    custom_enclave_contract ma_enclaves_map.
  Proof.
    rewrite /custom_enclave_contract.
    iIntros (I b e a v b' e' a' v' enclave_data ot ce
      Hwf_cemap Hcode_ce Hot Hb' HIhash Hb He)
      "(#Henclaves_inv & #Hma_inv & #HPenc & #HPsign)".
    clear HIhash.
    clear Hwf_cemap.
    assert (e = (b ^+ (length (code ce) + 1))%a) as -> by solve_addr+He.

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
    - iApply ( mutual_attest_A_contract with "[]") ; last iFrame "#"; eauto.
    - rewrite lookup_insert_ne // in Hcode_ce.
      2:{ rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
          intro Hcontra.
          apply hash_concat_inj' in Hcontra.
          destruct Hcontra as [_ Hcontra].
          rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra.
          by injection Hcontra.
      }
      simplify_map_eq.
      iApply ( mutual_attest_B_contract with "[]") ; last iFrame "#"; eauto.
  Admitted.

  (* -------------------------------------------------- *)
  (* ---------------------- MAIN ---------------------- *)
  (* -------------------------------------------------- *)



End mutual_attest_main.
