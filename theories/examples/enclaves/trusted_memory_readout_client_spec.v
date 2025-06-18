From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import trusted_memory_readout_code.

Section ClientEnclaveProofs.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {nainv: logrel_na_invs Σ} {oneshotg : one_shotG Σ}
    {reservedaddresses : ReservedAddresses}
    `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  #[local] Notation pc_b := client_begin_addr.
  #[local] Notation pc_e := (pc_b ^+ (Z.of_nat (length client_lcode) + 1))%a.
  #[local] Notation cf_b := (pc_b ^+ 1)%a.
  #[local] Notation cf_e := (cf_b ^+ Z.of_nat (length client_lcode))%a.

  Definition client_one_shot_inv (γ : gname) data_b data_e data_v : iProp Σ :=
    (pending_auth γ ∗ (∃ enclave_data, [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]) ∨
                        shot_token γ ∗
     (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∧
      ∃ sensor_b sensor_e sensor_a sensor_v,
        ((data_b ^+ 1)%a, data_v) ↦ₐ LCap E sensor_b sensor_e sensor_a sensor_v
        ∗ □ sensor_enclave_read_sensor_contract sensor_b sensor_e sensor_a sensor_v
    )).

  Definition client_na_inv γ pc_v data_b data_e data_a data_v ot : iProp Σ :=
    (codefrag cf_b pc_v client_lcode
     ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
     ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
     ∗ (client_one_shot_inv γ data_b data_e data_v)).

  Lemma client_one_shot_update γ data_b data_e data_v (Hdatarange : (data_b < data_e)%a) :
    client_one_shot_inv γ data_b data_e data_v ==∗ shot_token γ ∗
    (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = false ⌝ ∨
     (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∧
       ∃ lw, ((data_b ^+ 1)%a, data_v) ↦ₐ lw))%I.
  Proof.
    iIntros "[(Hauth & %enclave_data & Hdata)|(Htoken & %Hdatabounds & Hdata)]".
    - iMod (shoot with "Hauth") as "[H Htoken]". iModIntro. iFrame.
      iDestruct (big_sepL2_length with "Hdata") as "%Hdata_len".
      rewrite map_length finz_seq_between_length /finz.dist /= in Hdata_len.
      destruct enclave_data as [|lw enclave_data].
      + iLeft. iPureIntro. apply andb_false_intro2. solve_addr.
      + iRight.
        assert (data_b ^+ 2 <= data_e)%a by solve_addr.
        iDestruct (region_mapsto_cons with "Hdata") as "[Hts_sensor Hts_data]"; last iFrame.
        { transitivity (Some (data_b ^+ 2)%a); solve_addr. }
        { assumption. }
        iSplit. iPureIntro. apply le_addr_withinBounds; solve_addr.
        iExists _. iFrame.
    - iModIntro. iSplitL "Htoken". done. iRight. iSplitR. done.
      iDestruct "Hdata" as (sensor_b sensor_e sensor_a sensor_v) "[Hdata _]".
      iExists _. done.
  Qed.

  Lemma client_enclave_use_correct pc_v data_b data_e data_a data_v γ ot :
      shot_token γ
    ∗ na_inv logrel_nais ts_clientN (client_na_inv γ pc_v data_b data_e data_a data_v ot)

    ⊢ client_enclave_use_contract pc_b pc_e (cf_b ^+ client_use_off)%a pc_v.
  Proof.
    iIntros "#(Htoken & Hclient_inv)".
    iIntros (E ret φ HclientN HsensorN) "(Hna & HPC & Hr0 & [%lw1 Hr1] & [%lw2 Hr2] & [%lw3 Hr3]& Hret)".

    iMod (na_inv_acc with "Hclient_inv Hna") as
      "(Hinv & Hna & Hclose)"; [solve_ndisj ..|].
    iDestruct "Hinv" as "(>Hts_code & >Hts_keys & >Hts_addr & Hts_data)".

    (* Code memory *)
    codefrag_facts "Hts_code".

    assert (SubBounds pc_b pc_e cf_b cf_e).
    { solve_addr. }
    assert (withinBounds pc_b pc_e pc_b = true) as Hpcbounds.
    { apply le_addr_withinBounds; solve_addr. }

    (* Data memory *)
    iDestruct ("Hts_data") as "[(>Hauth & _)|(_ & Hts_data)]".
    { iCombine "Hauth Htoken" gives % [Hl _]%auth_both_valid_discrete.
      exfalso. clear -Hl. apply option_included in Hl.
      destruct Hl as [|(? & ? & ? & ? & ?)]; discriminate. }

    (* Prove the spec *)
    iInstr "Hts_code". (* Mov r_t1 PC *)

    iInstr "Hts_code". (* Lea r_t1 (begin - use) *)
    { transitivity (Some pc_b); [|easy].
      rewrite /client_use_off. solve_addr. }

    iInstr "Hts_code". (* Load r_t1 r_t1 *)
    iInstr "Hts_code". (* GetB r_t2 r_t1 *)
    iInstr "Hts_code". (* GetA r_t3 r_t1 *)
    iInstr "Hts_code". (* Sub r_t2 r_t2 r_t3 *)
    iInstr "Hts_code". (* Lea r_t1 r_t2 *)
    { transitivity (Some data_b); solve_addr. }

    (* Load sensor enclave read entry point *)
    iDestruct ("Hts_data") as "(%Hwb & %sensor_b & %sensor_e & %sensor_a & %sensor_v & Hdata_sensor & #Hsensor_contract)".
    iInstr "Hts_code". (* Lea r_t1 1 *)
    { transitivity (Some (data_b ^+ 1)%a); solve_addr. }
    iInstr "Hts_code". (* Load r_t1 r_t1 *)

    (* Save return pointer to a register unclobbered by sensor read *)
    iInstr "Hts_code". (* Mov r_t3 r_t0 *)

    (* Setup callback and jump to read sensor entry point. *)
    iInstr "Hts_code". (* Mov r_t0 PC *)
    iInstr "Hts_code". (* Lea r_t0 3 *)
    iInstr "Hts_code". (* Jmp r_t1 *)
    iApply "Hsensor_contract"; [|iFrame "Hna HPC Hr0"].
    solve_ndisj.
    iSplitL "Hr1". iExists _. iExact "Hr1".
    iSplitL "Hr2". iExists _. iExact "Hr2".

    (* Use Callback *)
    clear lw3. cbn [updatePcPermL].
    iIntros "!> (Hna & HPC & Hr0 & [%mmio_a Hr1] & Hr2)".

    (* Perform computation on the sensor value *)
    iInstr "Hts_code". (* Add r_t2 r_t2 r_t2 *)

    (* Restore return pointer and kill callback capability. *)
    iInstr "Hts_code". (* Mov r_t0 r_t3 *)
    iInstr "Hts_code". (* Mov r_t3 0 *)

    (* Return to caller *)
    iInstr "Hts_code". (* Jmp r_t0 *)

    (* Close the opened invariant *)
    iMod ("Hclose" with "[$Hna $Hts_code $Hts_addr $Hts_keys Htoken Hdata_sensor]") as "Hna".
    iNext. iRight. iFrame "Htoken".
    iSplit; [easy|]. do 4 iExists _. by iFrame.

    iApply ("Hret" with "[$Hna $HPC $Hr0 Hr1 Hr2 Hr3]").
    { iSplitL "Hr1". by auto.
      iSplitL "Hr2". by auto.
      iExists _.
      iSplitL "Hr3". by auto.
      iApply interp_int.
    }
  Qed.

  Lemma sealed_client_interp (lw : LWord) :
    □ custom_enclave_contract_gen ∗ system_inv
    ⊢ sealed_client lw -∗ fixpoint interp1 lw.
  Proof.
    rewrite /sealed_sensor.
    iIntros "[#Henclave_contract #Henclave_inv] Hsealed".
    iDestruct "Hsealed" as (code_b code_e code_a code_v) "(-> & #Hclient_contract)".
    rewrite fixpoint_interp1_eq /=.

    iIntros (lregs); iNext; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".

    (* Prepare the necessary resources *)
    (* Registers *)
    assert (exists w0, lregs !! r_t0 = Some w0) as Hrt0 by apply (Hfullmap r_t0).
    destruct Hrt0 as [w0 Hr0].
    replace (delete PC lregs)
      with (<[r_t0:=w0]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w1, lregs !! r_t1 = Some w1) as Hrt1 by apply (Hfullmap r_t1).
    destruct Hrt1 as [w1 Hr1].
    replace (delete PC lregs)
      with (<[r_t1:=w1]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w2, lregs !! r_t2 = Some w2) as Hrt2 by apply (Hfullmap r_t2).
    destruct Hrt2 as [w2 Hr2].
    replace (delete PC lregs)
      with (<[r_t2:=w2]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w3, lregs !! r_t3 = Some w3) as Hrt3 by apply (Hfullmap r_t3).
    destruct Hrt3 as [w3 Hr3].
    replace (delete PC lregs)
      with (<[r_t3:=w3]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    (* EXTRACT REGISTERS FROM RMAP *)
    (* iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3] as ["Hr0";"Hr1";"Hr2";"Hr3"]. *)
    iDestruct (big_sepM_delete _ _ r_t0 with "Hrmap") as "[Hr0 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr1 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
    { by simplify_map_eq. }
    replace (delete r_t3 _) with
      ( delete r_t3 (delete r_t2 (delete r_t1 (delete r_t0 (delete PC lregs))))).
    2:{
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t0) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t1) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t2) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t3) //.
      done.
    }
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map";eauto;done. }

    iApply ("Hclient_contract" with "[%] [%] [$Hna $HPC $Hr0 Hr1 Hr2 Hr3 Hrmap]");
      [solve_ndisj|solve_ndisj|].
    iSplitL "Hr1". iExists _. iExact "Hr1".
    iSplitL "Hr2". iExists _. iExact "Hr2".
    iSplitL "Hr3". iExists _. iExact "Hr3".

    iDestruct (jmp_to_unknown with "[$Henclave_contract $Henclave_inv] [$Hinterp_w0]") as "Hjmp".

    clear w3 Hr3.
    iIntros "!> (Hna & HPC & Hr0 & [%mmio_a Hr1] & Hr2 & (%w3 & Hr3 & #Hinterp_w3))".

    (* Wrap up the registers *)
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
    { do 3 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 3 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    { do 2 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 2 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
    { do 1 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 1 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hrmap $Hr3]") as "Hrmap".
    { do 0 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 0 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    set (rmap' := (<[r_t3:=_]> _)).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
      iApply big_sepM_insert_2; first done.
      iApply big_sepM_insert_2; first (iApply interp_int).
      iApply big_sepM_insert_2; first (iApply interp_int).
      iApply big_sepM_insert_2; first done.
      iApply big_sepM_intro.
      iIntros "!>" (r w Hrr).
      assert (is_Some (delete PC lregs !! r)) as His_some by auto.
      rewrite lookup_delete_is_Some in His_some.
      destruct His_some as [Hr _].
      rewrite lookup_delete_ne in Hrr; auto.
      iApply ("Hinterp_map" $! r w); auto.
    }
    assert (dom rmap' = all_registers_s ∖ {[PC]}).
    {
      repeat (rewrite dom_insert_L).
      rewrite dom_delete_L.
      rewrite regmap_full_dom; auto.
    }

    iApply ("Hjmp" with "[]") ; eauto ; iFrame.
  Qed.

  Lemma client_enclave_correct
    (Ep : coPset)
    (pc_v : Version)
    (data_b data_e data_a : finz.finz MemNum)
    (data_v : Version)
    (enclave_data : list LWord)
    (client_ot : finz.finz ONum) :

    (pc_b + (length client_lcode + 1))%a = Some pc_e ->
    (client_ot + 2)%f = Some (client_ot ^+ 2)%f ->
    (data_b < data_e)%a ->

    (□ ▷ custom_enclave_contract_gen)
    ∗ system_inv
    ∗ seal_pred (client_ot ^+ 1)%f (Psign client_enclave_pred)
    ∗ codefrag cf_b pc_v client_lcode
    ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
    ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) client_ot (client_ot ^+ 2)%f client_ot
    ∗ [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]
    ⊢ |={Ep}=> interp (LCap E pc_b pc_e cf_b pc_v).
  Proof.
    iIntros (Hpcrange Hot Hdatarange)
      "(#Henclave_contract & #Henclave_inv & #HPsign & Hts_code & Hts_addr & Hts_keys & Hts_data)".

    iMod pending_alloc as (γ) "Hauth".

    iMod (na_inv_alloc logrel_nais _ ts_clientN
            (client_na_inv γ pc_v data_b data_e data_a data_v client_ot)
           with "[$Hts_code $Hts_addr $Hts_keys Hauth Hts_data]") as "#Hts_inv".
    { iNext. iLeft. iFrame "Hauth". by iExists enclave_data. }
    clear enclave_data.

    assert (SubBounds pc_b pc_e cf_b cf_e) by
      (rewrite /client_code_len; solve_addr).
    assert (withinBounds pc_b pc_e pc_b = true) as Hpcbounds
      by (apply le_addr_withinBounds; solve_addr).
    assert (withinBounds data_b data_e data_b = true) as Hdatabounds
      by (apply le_addr_withinBounds; solve_addr).

    iModIntro.
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Hts_inv Hna") as
      "((>Hts_code & >Hts_addr & >Hts_keys & Hts_data) & Hna & Hclose)";
      [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".

    (* Prepare the necessary resources *)
    (* Registers *)
    assert (exists w0, lregs !! r_t0 = Some w0) as Hrt0 by apply (Hfullmap r_t0).
    destruct Hrt0 as [w0 Hr0].
    replace (delete PC lregs)
      with (<[r_t0:=w0]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w1, lregs !! r_t1 = Some w1) as Hrt1 by apply (Hfullmap r_t1).
    destruct Hrt1 as [w1 Hr1].
    replace (delete PC lregs)
      with (<[r_t1:=w1]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w2, lregs !! r_t2 = Some w2) as Hrt2 by apply (Hfullmap r_t2).
    destruct Hrt2 as [w2 Hr2].
    replace (delete PC lregs)
      with (<[r_t2:=w2]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w3, lregs !! r_t3 = Some w3) as Hrt3 by apply (Hfullmap r_t3).
    destruct Hrt3 as [w3 Hr3].
    replace (delete PC lregs)
      with (<[r_t3:=w3]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w4, lregs !! r_t4 = Some w4) as Hrt4 by apply (Hfullmap r_t4).
    destruct Hrt4 as [w4 Hr4].
    replace (delete PC lregs)
      with (<[r_t4:=w4]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w5, lregs !! r_t5 = Some w5) as Hrt5 by apply (Hfullmap r_t5).
    destruct Hrt5 as [w5 Hr5].
    replace (delete PC lregs)
      with (<[r_t5:=w5]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    (* EXTRACT REGISTERS FROM RMAP *)
    (* iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3] as ["Hr0";"Hr1";"Hr2";"Hr3"]. *)
    iDestruct (big_sepM_delete _ _ r_t0 with "Hrmap") as "[Hr0 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr1 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t5 with "Hrmap") as "[Hr5 Hrmap]".
    { by simplify_map_eq. }
    replace (delete r_t5 _) with
      ( delete r_t5 ( delete r_t4 ( delete r_t3 (delete r_t2 (delete r_t1 (delete r_t0 (delete PC lregs))))))).
    2:{
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t0) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t1) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t2) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t3) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t4) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t5) //.
      done.
    }
    iAssert (interp w1) as "Hinterp_w1".
    { iApply "Hinterp_map";eauto;done. }
    iAssert (interp w2) as "Hinterp_w2".
    { iApply "Hinterp_map";eauto;done. }
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map";eauto;done. }

    codefrag_facts "Hts_code".

    (* Prove the spec *)
    iInstr "Hts_code". (* Mov r_t3 PC *)

    (* Get and keep a pointer to a fail instruction. *)
    iInstr "Hts_code". (* Lea r_t3 (fail - init) *)

    (* Unseal the read entry point capabilitiy. *)
    wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hr1") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap Hi]"); eauto; simplify_map_eq; eauto;
      try solve_pure.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ sensor_seal_perms sensor_ot_b sensor_ot_e sensor_ot_a sensor_sb XZ ? Hps Hbounds Hregs'|]; cycle 1.
    { wp_pure. wp_end. by iIntros (?). }
    incrementLPC_inv as (?p&?b&?e&?pc_a&?pc_v'& x & HPC & Hx & Hregs'); simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    replace x with (cf_b ^+ 3)%a by solve_addr.
    clear x Hx.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr2 Hr1] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hts_code".
    iDestruct (interp_valid_sealed with "Hinterp_w2") as (Φ) "Hseal_valid".


    (* Attest the sensor enclave's signing key. *)
    iInstr "Hts_code". (* GetA r_t4 r_t1 *)

    (* EStoreId r_t1 r_t4 *)
    wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    iMod (inv_acc with "Henclave_inv") as "(Hcemap & Hsystem_close)"; first solve_ndisj.
    iDestruct "Hcemap" as (ECn OTn) "(>HEC & ECn_OTn & Hallocated_seals & Hfree_seals & #Hcemap)".

    iApply (wp_estoreid_success_unknown_ec with "[HPC Hr1 Hr4 Hi $HEC]"); try iFrame; try solve_pure.
    iIntros "!> %retv (Hi & Hr4 & HEC & [(-> & HPC & H)|(-> & HPC & Hr1)])".
    all: iMod ("Hsystem_close" with "[HEC ECn_OTn Hallocated_seals Hfree_seals Hcemap]") as "_"
    ; [ iExists ECn, OTn; iFrame "HEC Hcemap ECn_OTn Hallocated_seals Hfree_seals"; eauto | iModIntro]
    ; wp_pure; iInstr_close "Hts_code".
    2: { wp_end. by iIntros (?). }
    iDestruct "H" as (I tid) "(Hr1 & #Hts_env & [%Hseal %Htidx])".

    iInstr "Hts_code". (* Sub r_t1 r_t1 hash_sensor *)

    destruct (decide (I = hash_sensor)) as [-> | HnI]; cycle 1.
    { iInstr "Hts_code". (* Jnz r_t3 r_t1 *)
      by (injection; intro Hcontra; lia).
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?). }
    replace ( _ - _) with 0 by lia.

    (* Extranct the Psign predicate for the signed sensor read entry point. *)
    iAssert (
        if Z.even sensor_ot_a
        then seal_pred sensor_ot_a (Penc sensor_enclave_pred) ∗
             seal_pred (sensor_ot_a ^+ 1)%f (Psign sensor_enclave_pred)
        else seal_pred (sensor_ot_a ^+ -1)%f (Penc sensor_enclave_pred) ∗
             seal_pred sensor_ot_a (Psign sensor_enclave_pred))%I as "Hts".
    { iApply "Hcemap"; iFrame "%#∗".
      iPureIntro. rewrite /custom_enclaves /= /ts_enclaves_map.
      by simplify_map_eq. }

    destruct Z.even
    ; iDestruct "Hts" as "[Hts_Penc Hts_Psign]"
    ; iEval (cbn) in "Hts_Penc"
    ; iEval (cbn) in "Hts_Psign".
    {
      iDestruct (seal_pred_valid_sealed_eq with "[$Hts_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }

    iDestruct (seal_pred_valid_sealed_eq with "[Hts_Psign] Hseal_valid") as "Heqv".
    by apply sealed_sensor_persistent.
    iExact "Hts_Psign".
    iSpecialize ("Heqv" $! (LWSealable sensor_sb)).

    iInstr "Hts_code". (* Jnz r_t3 r_t1 *)

    iAssert (sealed_sensor (LWSealable sensor_sb))%I as "Hseal_sensor".
    { iDestruct "Hseal_valid" as (sb) "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iRewrite "Heqv".
      iFrame "HΦ". }
    iClear "Heqv Hts_Penc Hts_Psign Hcemap Hseal_valid".
    unfold sealed_sensor.
    iDestruct "Hseal_sensor"
      as (sensor_b sensor_e sensor_a sensor_v) "[%Hsensor_sb #Hsensor_contract]".
    injection Hsensor_sb as ->.

    (* Get the data capability *)
    iInstr "Hts_code". (* Lea r_t3 (begin - fail) *)
    { transitivity (Some pc_b); [|easy].
      rewrite /client_fail_off. solve_addr. }
    iInstr "Hts_code". (* Load r_t1 r_t3 *)
    split; [easy|by solve_addr].
    iInstr "Hts_code". (* GetB r_t4 r_t1 *)
    iInstr "Hts_code". (* GetA r_t5 r_t1 *)
    iInstr "Hts_code". (* Sub r_t4 r_t4 r_t5 *)
    iInstr "Hts_code". (* Lea r_t1 r_t4 *)
    { transitivity (Some data_b); [solve_addr|easy]. }

    (* Store read sensor capability in private data. *)
    iInstr "Hts_code". (* Lea r_t1 1 *)
    { transitivity (Some (data_b ^+ 1)%a); [solve_addr|easy]. }
    iMod (client_one_shot_update with "Hts_data")
      as "[#Htoken Hts_data]"; try solve_addr.
    iDestruct "Hts_data" as "[%Hdatabounds1|(%Hdatabounds1 & %lw & Hdata_sensor_field)]".
    { (* Data section too small *)
      wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hr1 $Hr2]");
        try solve_pure; auto.
      iIntros "!> _".
      wp_pure. wp_end; by iIntros (?).
    }
    iInstr "Hts_code". (* Store r_t1 r_t2 *)
    clear lw.

    (* Get the seal/unseal master capability and switch to signing.  *)
    iInstr "Hts_code". (* Lea r_t1 (-1)%Z *)
    { transitivity (Some data_b); solve_addr. }
    iInstr "Hts_code". (* Load r_t2 r_t1 *)
    easy.
    iInstr "Hts_code". (* Lea r_t2 1%Z *)
    { transitivity (Some (client_ot ^+1)%ot); solve_addr. }

    (* Construct use entry point. *)
    iInstr "Hts_code". (* Lea r_t3 (use - begin) *)
    { transitivity (Some (cf_b ^+ client_use_off))%a; [|easy].
      rewrite /client_use_off. solve_addr. }
    iInstr "Hts_code". (* Restrict r_t3 Eperm *)
    { by rewrite decode_encode_perm_inv. }
    rewrite decode_encode_perm_inv.

    (* Sign the entry point capability. *)
    iInstr "Hts_code"; auto. (* Seal r_t1 r_t2 r_t3 *)
    { apply le_addr_withinBounds; solve_addr. }

    (* Create signing public key *)
    iInstr "Hts_code". (* GetA r_t3 r_t1 *)
    iInstr "Hts_code". (* GetE r_t4 r_t1 *)
    iInstr "Hts_code". (* Subseg r_t2 r_t3 r_t4 *)
    { apply isWithin_of_le; solve_finz. }
    (* Restrict r_t2 U *)
    iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    wp_instr.
    iApply (wp_restrict_success_z_sr with "[HPC Hr2 Hi]")
    ; try iFrame
    ; try solve_pure
    ; repeat (rewrite decode_encode_seal_perms_inv)
    ; try done.
    iNext; iIntros "(HPC & Hi & Hr2)".
    wp_pure; iInstr_close "Hts_code".

    (* Jump back to adversary. *)
    iDestruct (jmp_to_unknown with "[$Henclave_contract $Henclave_inv] [$Hinterp_w0]") as "Hjmp".
    iInstr "Hts_code". (* Jmp r_t0 *)

    (* ----- Prepare the use of FTLR ----- *)

    set (lsealed_entry_use_cap := LSealedCap (client_ot ^+ 1)%f _ _ _ _ _).
    iAssert (interp lsealed_entry_use_cap) as "Hinterp_sealed_entry_use_cap".
    { iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_client; iFrame "%#". iSplit.
      - iPureIntro; intro; apply sealed_client_persistent.
      - iNext. do 4 iExists _.
        iSplit; first done.
        iModIntro.
        iApply (client_enclave_use_correct with "[$]").
    }
    iAssert (
        interp (LSealRange (false, true) (client_ot ^+ 1)%f (client_ot ^+ 2)%f (client_ot ^+ 1)%f)
      ) as "Hinterp_sealr_ot".
    { iEval (rewrite /= fixpoint_interp1_eq /= /safe_to_unseal).
      iSplit; first done.
      rewrite finz_seq_between_singleton ; last solve_finz.
      iSplit; last done.
      iSplit; last done.
      iExists sealed_client_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply (sealed_client_interp with "[$Henclave_contract $Henclave_inv]").
    }

    (* Close the opened invariant *)
    iMod ("Hclose" with "[$Hna $Hts_code $Hts_addr $Hts_keys $Htoken Hdata_sensor_field]") as "Hna".
    iNext. iRight.
    iSplit; [easy|].
    do 4 iExists _. iFrame "Hdata_sensor_field Hsensor_contract".

    (* Wrap up the registers *)
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
    { do 5 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 5 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    { do 4 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 4 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
    { do 3 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 3 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hrmap $Hr3]") as "Hrmap".
    { do 2 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 2 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t4 with "[$Hrmap $Hr4]") as "Hrmap".
    { do 1 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 1 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hrmap $Hr5]") as "Hrmap".
    { do 0 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 0 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    set (rmap' := (<[r_t5:=_]> _)).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
      iApply big_sepM_insert_2; first (iApply interp_int).
      iApply big_sepM_insert_2; first (iApply interp_int).
      iApply big_sepM_insert_2; first (iApply interp_int).
      repeat (iApply big_sepM_insert_2; first done).
      iApply big_sepM_intro.
      iIntros "!>" (r w Hrr).
      assert (is_Some (delete PC lregs !! r)) as His_some by auto.
      rewrite lookup_delete_is_Some in His_some.
      destruct His_some as [Hr _].
      rewrite lookup_delete_ne in Hrr; auto.
      iApply ("Hinterp_map" $! r w); auto.
    }
    assert (dom rmap' = all_registers_s ∖ {[PC]}).
    {
      repeat (rewrite dom_insert_L).
      rewrite dom_delete_L.
      rewrite regmap_full_dom; auto.
    }

    iApply ("Hjmp" with "[]") ; eauto ; iFrame.
  Qed.

End ClientEnclaveProofs.
