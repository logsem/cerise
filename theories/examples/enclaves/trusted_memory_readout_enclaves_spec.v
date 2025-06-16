From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import trusted_memory_readout_code
  trusted_memory_readout_client_spec
  trusted_memory_readout_sensor_spec.

Section EnclavesProof.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {nainv: logrel_na_invs Σ} {reservedaddresses : ReservedAddresses}
    {oneshotg : one_shotG Σ}
    `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  Lemma enclaves_contract :
    ⊢ custom_enclave_contract_gen.
  Proof.
    iLöb as "Henclave_contract".
    iIntros (Ep I code_b code_e code_v data_b data_e data_a data_v
               enclave_data ot ce Hcode_ce Hot HIhash
               Hcode_b Hcode_e).
    iIntros "(#Hcustoms_inv & Hcode & Hdata & #HPenc & #HPsign & Henclave_cur)".

    iDestruct (region_mapsto_cons with "Hcode") as "[Hdatacap Hcode]"; last iFrame.
    { transitivity (Some (code_b ^+ 1)%a); solve_addr. }
    { solve_addr. }

    iAssert (⌜ (data_b < data_e)%a ⌝)%I as "%Hdata_b_lt_e".
    { iDestruct (big_sepL2_length with "Hdata") as "%Hdata_len". iPureIntro.
      rewrite map_length finz_seq_between_length /finz.dist /= in Hdata_len.
      clear - Hdata_len. solve_addr. }

    iDestruct (region_mapsto_cons with "Hdata") as "[Hkeys Hdata]"; last iFrame.
    { transitivity (Some (data_b ^+ 1)%a); try solve_addr. }
    { solve_addr. }

    assert (I = hash_sensor \/ I = hash_client) as HI.
    { rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      done.
    }

    destruct HI as [-> | ->].
    - (* Sensor enclave *)
      rewrite /ts_enclaves_map lookup_insert in Hcode_ce. simplify_eq.
      change (code_region sensor_enclave_pred) with sensor_begin_addr in *.
      assert (code_e = sensor_begin_addr ^+ (length sensor_lcode + 1)%nat)%a
        as -> by solve_addr.

      change ((λ w : Word, word_to_lword w code_v) <$>
                code sensor_enclave_pred) with sensor_lcode.
      iApply (sensor_enclave_correct with
               "[$Henclave_contract $Hcustoms_inv $HPsign Hcode $Hdatacap $Hkeys $Hdata]");
        try solve_addr; auto.
      replace (sensor_begin_addr ^+ (length sensor_lcode + 1)%nat)%a
        with ((sensor_begin_addr ^+ 1) ^+ length sensor_lcode)%a by solve_addr.
      done.
    - (* Client enclave *)
      rewrite /ts_enclaves_map lookup_insert_ne // in Hcode_ce;
        auto using hash_client_sensor.
      rewrite // lookup_insert in Hcode_ce. simplify_eq.
      change (code_region client_enclave_pred) with client_begin_addr in *.
      assert (code_e = client_begin_addr ^+ (length client_lcode + 1)%nat)%a
        as -> by solve_addr.

      change ((λ w : Word, word_to_lword w code_v) <$>
                code client_enclave_pred) with client_lcode.
      iApply (client_enclave_correct with
               "[$Henclave_contract $Hcustoms_inv $HPsign Hcode $Hdatacap $Hkeys $Hdata]");
        try solve_addr; auto.
      replace (client_begin_addr ^+ (length client_lcode + 1)%nat)%a
        with ((client_begin_addr ^+ 1) ^+ length client_lcode)%a by solve_addr.
      done.
  Qed.

End EnclavesProof.
