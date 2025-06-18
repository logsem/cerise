From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import trusted_memory_readout_code.

Section SensorEnclaveProofs.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {nainv: logrel_na_invs Σ} {oneshotg : one_shotG Σ}
    {reservedaddresses : ReservedAddresses}
    `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  #[local] Notation pc_b := sensor_begin_addr.
  #[local] Notation pc_e := (pc_b ^+ (Z.of_nat (length sensor_lcode) + 1))%a.
  #[local] Notation cf_b := (pc_b ^+ 1)%a.
  #[local] Notation cf_e := (cf_b ^+ Z.of_nat (length sensor_lcode))%a.

  Definition sensor_one_shot_inv (γ : gname) data_b data_e data_a data_v : iProp Σ :=
      (pending_auth γ ∗ ∃ enclave_data, [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]])
    ∨ (shot_token γ ∗
       ⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∗
       ⌜ data_b = data_a ⌝ ∗
       ∃ mmio_b mmio_e mmio_a mmio_v,
         ((data_b ^+ 1)%a, data_v) ↦ₐ LCap RW mmio_b mmio_e mmio_a mmio_v
         ∗ ⌜ withinBounds mmio_b mmio_e mmio_a = true ⌝
         ∗ (mmio_a, mmio_v) ↦ₐ LInt 21).

  Definition sensor_na_inv pc_v data_b data_e data_a data_v ot γ : iProp Σ :=
    (codefrag cf_b pc_v sensor_lcode
     ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
     ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
     ∗ (sensor_one_shot_inv γ data_b data_e data_a data_v)).

  Lemma sensor_one_shot_update γ data_b data_e data_a data_v (Hdatarange : (data_b < data_e)%a) :
    sensor_one_shot_inv γ data_b data_e data_a data_v ==∗ shot_token γ ∗
    (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = false ⌝ ∨
     (⌜ withinBounds data_b data_e (data_b ^+ 1)%a = true ⌝ ∧
       ∃ lw, ((data_b ^+ 1)%a, data_v) ↦ₐ lw))%I.
  Proof.
    iIntros "[(Hauth & %enclave_data & Hdata)|(Htoken & %Hdatabounds & Heq_b_a & Hdata)]".
    - iMod (shoot with "Hauth") as "[H Htoken]". iModIntro. iFrame.
      iDestruct (big_sepL2_length with "Hdata") as "%Hdata_len".
      rewrite map_length finz_seq_between_length /finz.dist /= in Hdata_len.
      destruct enclave_data as [|lw enclave_data].
      + iLeft. iPureIntro. apply andb_false_intro2. solve_addr.
      + iRight.
        assert (data_b ^+ 2 <= data_e)%a by solve_addr.
        iDestruct (region_mapsto_cons with "Hdata") as "[Hts_mmio Hts_data]"; last iFrame.
        { transitivity (Some (data_b ^+ 2)%a); solve_addr. }
        { assumption. }
        iSplit. iPureIntro. apply le_addr_withinBounds; solve_addr.
        iExists _. iFrame.
    - iModIntro. iSplitL "Htoken". done. iRight. iSplitR. done.
      iDestruct "Hdata" as "(%mmio_b & %mmio_e & %mmio_a & %mmio_v & Hdata & H & Hmmio)".
      iExists _. done.
  Qed.

  Lemma sensor_enclave_read_sensor_correct pc_v data_b data_e data_a data_v γ ot:
      shot_token γ
    ∗ na_inv logrel_nais ts_sensorN (sensor_na_inv pc_v data_b data_e data_a data_v ot γ)
    ⊢ sensor_enclave_read_sensor_contract pc_b pc_e (cf_b ^+ sensor_read_off)%a pc_v.
  Proof.
    iIntros "#(Htoken & Hts_inv)".
    iIntros (E ret φ HsensorN) "(Hna & HPC & Hr0 & [%lw1 Hr1] & [%lw2 Hr2] & Hret)".

    iMod (na_inv_acc with "Hts_inv Hna") as "(>Hinv & Hna & Hclose)"; [solve_ndisj ..|].
    iDestruct "Hinv" as "(Hts_code & Hts_keys & Hts_addr & Hts_data)".

    (* Code memory *)
    codefrag_facts "Hts_code".

    assert (SubBounds pc_b pc_e cf_b cf_e).
    { solve_addr. }
    assert (withinBounds pc_b pc_e pc_b = true) as Hpcbounds.
    { apply le_addr_withinBounds; solve_addr. }

    (* Data memory *)
    iDestruct ("Hts_data") as "[(Hauth & _)|(_ & %Hwb & %Heq_b_a & %mmio_b & %mmio_e & %mmio_a & %mmio_v & Hts_data & %Hmmiobounds & Hts_mmio)]".
    { iCombine "Hauth Htoken" gives % [Hl _]%auth_both_valid_discrete.
      exfalso. clear -Hl. apply option_included in Hl.
      destruct Hl as [|(? & ? & ? & ? & ?)]; discriminate. }


    (* Prove the spec *)
    iInstr "Hts_code". (* Mov r_t1 PC *)

    iInstr "Hts_code". (* Lea r_t1 (begin - read) *)
    { transitivity (Some pc_b); [|easy].
      rewrite /sensor_read_off. solve_addr. }

    iInstr "Hts_code". (* Load r_t1 r_t1 *)
    iInstr "Hts_code". (* Lea r_t1 1 *)
    { transitivity (Some (data_b ^+ 1)%a); solve_addr. }

    iInstr "Hts_code". (* Load r_t1 r_t1 *)
    iInstr "Hts_code". (* Load r_t2 r_t1 *)
    auto.
    wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    iApply (wp_Get_same_success with "[$HPC $Hi $Hr1]"); try solve_pure.
    iNext. iIntros "(HPC & Hi & Hr1)".
    wp_pure. iInstr_close "Hts_code".

    iInstr "Hts_code". (* Jmp r_t0 *)

    (* Close the opened invariant *)
    iMod ("Hclose" with "[$Hna $Hts_code $Hts_addr $Hts_keys Htoken Hts_data Hts_mmio]") as "Hna".
    iNext. iRight. iFrame "Htoken".
    iSplit; [easy|]. iSplit; [easy|]. do 4 iExists _. by iFrame.

    iApply ("Hret" with "[$Hna $HPC $Hr0 Hr1 $Hr2]").
    eauto.
  Qed.

  Lemma sealed_sensor_interp (lw : LWord) :
    □ custom_enclave_contract_gen ∗ system_inv
    ⊢ sealed_sensor lw -∗ fixpoint interp1 lw.
  Proof.
    rewrite /sealed_sensor.
    iIntros "[#Henclave_contract #Henclave_inv] Hsealed".
    iDestruct "Hsealed" as (code_b code_e code_a code_v) "(-> & #Hsensor_contract)".
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

    (* EXTRACT REGISTERS FROM RMAP *)
    (* iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3] as ["Hr0";"Hr1";"Hr2";"Hr3"]. *)
    iDestruct (big_sepM_delete _ _ r_t0 with "Hrmap") as "[Hr0 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr1 Hrmap]".
    { by simplify_map_eq. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
    { by simplify_map_eq. }
    replace (delete r_t2 _) with
      ( delete r_t2 (delete r_t1 (delete r_t0 (delete PC lregs)))).
    2:{
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t0) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t1) //.
      rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t2) //.
      done.
    }
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map";eauto;done. }

    iApply ("Hsensor_contract" with "[%] [$Hna $HPC $Hr0 Hr1 Hr2 Hrmap]");
      first solve_ndisj.
    iSplitL "Hr1". iExists _. iExact "Hr1".
    iSplitL "Hr2". iExists _. iExact "Hr2".

    iDestruct (jmp_to_unknown with "[$Henclave_contract $Henclave_inv] [$Hinterp_w0]") as "Hjmp".
    iIntros "!> (Hna & HPC & Hr0 & [%mmio_a Hr1] & Hr2)".

    (* Wrap up the registers *)
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
    { do 2 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 2 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    { do 1 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 1 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
    { do 0 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 0 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    set (rmap' := (<[r_t2:=_]> _)).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
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

  Lemma sensor_enclave_correct
    (Ep : coPset)
    (pc_v : Version)
    (data_b data_e data_a : finz.finz MemNum)
    (data_v : Version)
    (enclave_data : list LWord)
    (ot : finz.finz ONum) :

    let pc_b := sensor_begin_addr in
    let pc_e := (pc_b ^+ (sensor_code_len + 1))%a in
    let cf_b := (pc_b ^+ 1)%a in
    let cf_e := (cf_b ^+ length sensor_lcode)%a in

    (pc_b + (sensor_code_len + 1))%a = Some pc_e ->
    (ot + 2)%f = Some (ot ^+ 2)%f ->
    (data_b < data_e)%a ->

    (□ ▷ custom_enclave_contract_gen)
    ∗ system_inv
    ∗ seal_pred (ot ^+ 1)%f (Psign sensor_enclave_pred)
    ∗ codefrag cf_b pc_v sensor_lcode
    ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
    ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
    ∗ [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]
    ⊢ |={Ep}=> interp (LCap E pc_b pc_e (sensor_begin_addr ^+ 1)%a pc_v).
  Proof.
    iIntros (pc_b pc_e cf_b cf_e Hpcrange Hot Hdatarange)
      "(#Henclave_contract & #Henclave_inv & #HPsign & Hts_code & Hts_addr & Hts_keys & Hts_data)".

    iMod pending_alloc as (γ) "Hauth".

    iMod (na_inv_alloc logrel_nais _ ts_sensorN
            (sensor_na_inv pc_v data_b data_e data_a data_v ot γ)
           with "[$Hts_code $Hts_addr $Hts_keys Hauth Hts_data]") as "#Hts_inv".
    { iNext. iLeft. iFrame "Hauth". by iExists enclave_data. }
    clear enclave_data.

    assert (SubBounds pc_b pc_e cf_b cf_e) by
      (subst pc_e pc_b cf_e cf_b; rewrite /sensor_code_len; solve_addr).
    assert (withinBounds pc_b pc_e pc_b = true) as Hpcbounds
      by (subst pc_e; apply le_addr_withinBounds; solve_addr).
    assert (withinBounds data_b data_e data_b = true) as Hdatabounds
      by (apply le_addr_withinBounds; solve_addr).

    iModIntro.
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Hts_inv Hna") as
      "(>(Hts_code & Hts_addr & Hts_keys & Hts_data) & Hna & Hclose)";
      [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    change (sensor_begin_addr ^+ 1)%a with cf_b.

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
    iInstr "Hts_code". (* Mov r_t2 PC *)

    (* Check for exclusive access to sensor. *)
    iInstr "Hts_code". (* Lea r_t2 (fail - init) *)

    (* GetWType r_t3 r_t1 *)
    (* Sub r_t3 r_t3 (encodeWordType (WCap O 0 0 0)%a) *)
    (* Jnz r_t2 r_t3 *)
    destruct w1 as [z|[mmio_p mmio_b mmio_e mmio_a mmio_v|sr_p sr_b sr_e sr_a]|otls ls].
    { (* LInt *)
      iInstr "Hts_code".
      iInstr "Hts_code".
      iInstr "Hts_code".
      { clear. inversion 1.
        apply (encodeWordType_correct (WInt z) (WCap O 0%a 0%a 0%a)).
        cbn. lia.
      }
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    all: cycle 1.
    { (* LWSealRange *)
      iInstr "Hts_code".
      iInstr "Hts_code".
      iInstr "Hts_code".
      { clear. inversion 1.
        apply (encodeWordType_correct (WSealRange sr_p sr_b sr_e sr_a) (WCap O 0%a 0%a 0%a)).
        cbn. lia.
      }
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    { (* LWSealed *)
      iInstr "Hts_code".
      iInstr "Hts_code".
      iInstr "Hts_code".
      { clear. inversion 1.
        apply (encodeWordType_correct (WSealed otls (lsealable_get_sealable ls)) (WCap O 0%a 0%a 0%a)).
        cbn. lia.
      }
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    (* LCap *)
    iInstr "Hts_code". (* GetWType r_t3 r_t1 *)
    iInstr "Hts_code". (* Sub r_t3 r_t3 (encodeWordType (WCap O 0 0 0)%a) *)
    pose proof (encodeWordType_correct
                  (lword_get_word (LCap mmio_p mmio_b mmio_e mmio_a mmio_v))
                  (WCap O 0%a 0%a 0%a)) as ->.
    rewrite Z.sub_diag.
    iInstr "Hts_code". (* Jnz r_t2 r_t3 *)

    (* Check that we get RW permissions. *)
    iInstr "Hts_code". (* GetP r_t3 r_t1 *)
    iInstr "Hts_code". (* Sub r_t3 r_t3 (encodePerm RW) *)
    (* Jnz r_t2 r_t3 *)
    destruct (decide (encodePerm mmio_p = encodePerm RW)) as [Hperm|Hperm].
    2: {
      iInstr "Hts_code".
      { clear - Hperm. inversion 1. lia. }
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    apply encodePerm_inj in Hperm. subst mmio_p. rewrite Z.sub_diag.
    iInstr "Hts_code".

    (* Check that we have exclusive access to the mmio capability. *)
    (* IsUnique r_t3 r_t1 *)
    wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    iDestruct (readAllowed_not_reserved with "Hinterp_w1") as "%Hnotreserved".
    { done. }
    iApply (wp_isunique_success' with "[HPC Hr1 Hr3 Hi]"); try iFrame; try solve_pure.
    iNext. iIntros "[(HPC & Hr3 & Hr1 & Hi & [%lmmio Hlmmio]) | (HPC & Hr3 & Hr1 & Hi)]".
    2: {
      (* Success false *)
      wp_pure. iInstr_close "Hts_code".
      iInstr "Hts_code". (* Sub r_t3 1 r_t3 *)
      iInstr "Hts_code". (* Jnz r_t2 r_t3 *)
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    (* Success true *)
    wp_pure. iInstr_close "Hts_code".
    iInstr "Hts_code". (* Sub r_t3 1 r_t3 *)
    iInstr "Hts_code". (* Jnz r_t2 r_t3 *)

    (* "Initialize" the sensor. *)
    destruct (withinBounds mmio_b mmio_e mmio_a) eqn:Hmmiobounds.
    2: {
      (* Failure. Cursor out of bounds. *)
      wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
      iApply (wp_store_fail_z with "[$HPC $Hi $Hr1]");
        try solve_pure; auto.
      iIntros "!> _".
      wp_pure. wp_end; by iIntros (?).
    }

    iAssert ((∃ lw_a, (mmio_a, (mmio_v + 1)%nat) ↦ₐ lw_a)%I)
      with "[Hlmmio]" as "[%lw_a Hmmio_a]".
    {
      pose proof (withinBounds_in_seq_1 _ _ _ Hmmiobounds) as Hlookup.
      pose proof (elem_of_list_fmap_1 (λ a : Addr, (a, (mmio_v + 1)%nat)) _ _ Hlookup)
                 as Hlookup2.
      apply elem_of_list_lookup in Hlookup2.
      destruct Hlookup2 as [i Hlookup2].
      by iDestruct (big_sepL2_extract_l' _ _ _ _ _ Hlookup2 with "Hlmmio")
        as "[_ ?]".
    }
    iInstr "Hts_code". (* Store r_t1 42 *)
    clear lw_a.

    (* Get the data capability *)
    iInstr "Hts_code". (* Mov r_t3 r_t2 *)
    iInstr "Hts_code". (* Lea r_tr (begin - fail) *)
    transitivity (Some pc_b); [rewrite /sensor_fail_off; subst cf_b; solve_addr|easy].
    iInstr "Hts_code". (* Load r_t3 r_t3 *)
    iInstr "Hts_code". (* GetB r_t4 r_t3 *)
    iInstr "Hts_code". (* GetA r_t5 r_t3 *)
    iInstr "Hts_code". (* Sub r_t4 r_t4 r_t5 *)

    destruct (decide (data_b = data_a)) as [Heq_b_a|Hneq]; cycle 1.
    { iInstr "Hts_code". (* Jnz r_t2 r_t4 *)
      { injection. solve_addr. }
      iInstr "Hts_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    subst data_a.
    replace (data_b - data_b) with 0%Z by lia.

    iInstr "Hts_code". (* Jnz r_t2 r_t4 *)
    iInstr "Hts_code". (* Lea r_t3 1 *)
    transitivity (Some (data_b ^+ 1)%a); solve_addr.

    (* Store mmio capability. *)
    iMod (sensor_one_shot_update with "Hts_data") as "[#Htoken Hts_data]"; try solve_addr.
    iDestruct "Hts_data" as "[%Hdatabounds1|(%Hdatabounds1 & %lw & Hts_mmio)]".
    { (* Data section too small *)
      wp_instr. iInstr_lookup "Hts_code" as "Hi" "Hts_code".
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hr3 $Hr1]");
        try solve_pure; auto.
      iIntros "!> _".
      wp_pure. wp_end; by iIntros (?).
    }
    iInstr "Hts_code". (* Store r_t3 r_t1 *)
    clear lw.

    (* Get the seal/unseal master capability and switch to signing.  *)
    iInstr "Hts_code". (* Lea r_t3 (-1)%Z *)
    { transitivity (Some data_b); solve_addr. }
    iInstr "Hts_code". (* Load r_t2 r_t3 *)
    easy.
    iInstr "Hts_code". (* Lea r_t2 1%Z *)
    { transitivity (Some (ot ^+1)%ot); solve_addr. }

    (* Construct read_sensor entry point. *)
    iInstr "Hts_code". (* Lea r_t1 (read - fail) *)
    { transitivity (Some (cf_b ^+ sensor_read_off))%a; [|easy].
      rewrite /sensor_read_off /sensor_fail_off. subst cf_b. solve_addr. }
    iInstr "Hts_code". (* Restrict r_t2 Eperm *)
    { by rewrite decode_encode_perm_inv. }
    rewrite decode_encode_perm_inv.

    (* Sign the entry point capability. *)
    iInstr "Hts_code"; auto. (* Seal r_t1 r_t2 r_t1 *)
    { apply le_addr_withinBounds; solve_addr. }

    (* Create signing public key *)
    iInstr "Hts_code". (* GetA r_t3 r_t2 *)
    iInstr "Hts_code". (* GetE r_t4 r_t2 *)
    iInstr "Hts_code". (* Subseg r_t2 r_t3 r_t4 *)
    { apply isWithin_of_le; solve_finz. }
    (* Restrict r_t2 Uperm *)
    iInstr_lookup "Hts_code" as "Hi" "Hts_code".
    wp_instr.
    iApply (wp_restrict_success_z_sr with "[HPC Hr1 Hi]")
    ; try iFrame
    ; try solve_pure
    ; repeat (rewrite decode_encode_seal_perms_inv)
    ; try done.
    iNext; iIntros "(HPC & Hi & Hr1)".
    wp_pure; iInstr_close "Hts_code".

    (* Jump back to adversary. *)
    iDestruct (jmp_to_unknown with "[$Henclave_contract $Henclave_inv] [$Hinterp_w0]") as "Hjmp".
    iInstr "Hts_code". (* Jmp r_t0 *)

    (* ----- Prepare the use of FTLR ----- *)

    set (lsealed_entry_read_cap := LSealedCap _ _ _ _ _ _).
    iAssert (interp lsealed_entry_read_cap) as "Hinterp_sealed_entry_read_cap".
    { iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_sensor; iFrame "%#". iSplit.
      - iPureIntro; intro; apply sealed_sensor_persistent.
      - iNext. do 4 iExists _.
        iSplit; first done.
        iModIntro.
        iApply (sensor_enclave_read_sensor_correct with "[$]").
    }
    iAssert (
        interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f)
      ) as "Hinterp_sealr_ot".
    { iEval (rewrite /= fixpoint_interp1_eq /= /safe_to_unseal).
      iSplit; first done.
      rewrite finz_seq_between_singleton ; last solve_finz.
      iSplit; last done.
      iSplit; last done.
      iExists sealed_sensor_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply (sealed_sensor_interp with "[$Henclave_contract $Henclave_inv]").
    }

    (* Close the opened invariant *)
    iMod ("Hclose" with "[$Hna $Hts_code $Hts_addr $Hts_keys Htoken Hts_mmio Hmmio_a]") as "Hna".
    iNext. iRight. iFrame "Htoken".
    iSplit; [easy|]. iSplit; [easy|]. do 4 iExists _. by iFrame "Hts_mmio Hmmio_a".

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

End SensorEnclaveProofs.
