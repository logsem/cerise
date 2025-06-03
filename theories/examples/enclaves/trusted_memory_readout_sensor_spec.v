From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import trusted_memory_readout_code.

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

  (* Definition sensor_dataN := nroot .@ "sensor" .@ "data". *)

End SensorEnclaveData.

Section SensorEnclaveProofs.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {nainv: logrel_na_invs Σ} {oneshotg : one_shotG Σ}
    {reservedaddresses : ReservedAddresses}
    `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  Definition one_shot_inv (γ : gname) data_b data_e data_v : iProp Σ :=
    (pending_auth γ ∗ (∃ enclave_data, [[(data_b ^+ 1)%a,data_e]]↦ₐ{data_v}[[enclave_data]]) ∨
     shot_token γ ∗ (∃ mmio_b mmio_e mmio_a mmio_v,
       ((data_b ^+ 1)%a, data_v) ↦ₐ LCap RW mmio_b mmio_e mmio_a mmio_v))%I.

  Lemma one_shot_update γ data_b data_e data_v (Hdatarange : (data_b < data_e)%a) :
    one_shot_inv γ data_b data_e data_v ==∗ shot_token γ ∗
    (⌜ (data_b ^+ 1)%a = data_e ⌝ ∨
     (∃ lw, ((data_b ^+ 1)%a, data_v) ↦ₐ lw))%I.
  Proof.
    iIntros "[(Hauth & %enclave_data & Hdata)|[Htoken Hdata]]".
    - iMod (shoot with "Hauth") as "[_ Htoken]". iModIntro. iFrame.
      iDestruct (big_sepL2_length with "Hdata") as "%Hdata_len".
      rewrite map_length finz_seq_between_length /finz.dist /= in Hdata_len.
      destruct enclave_data as [|lw enclave_data].
      + iLeft. iPureIntro. solve_addr.
      + iRight.
        iDestruct (region_mapsto_cons with "Hdata") as "[Hts_mmio Hts_data]"; last iFrame.
        { transitivity (Some (data_b ^+ 2)%a); try solve_addr. }
        { solve_addr. }
        iExists _. iFrame.
    - iModIntro. iSplitL "Htoken". done. iRight.
      iDestruct "Hdata" as "(%mmio_b & %mmio_e & %mmio_a & %mmio_v & H)".
      iExists _. done.
  Qed.

  Lemma sensor_enclave_read_sensor_correct n pc_v data_b data_e data_a data_v
    ot ret φ :
    let pc_b := sensor_begin_addr in
    let pc_e := (pc_b ^+ (sensor_code_len + 1))%a in
    let cf_b := (pc_b ^+ 1)%a in
    let cf_e := (cf_b ^+ sensor_read_len)%a in
    (pc_b + (sensor_code_len + 1) = Some pc_e)%a ->
    (data_b < data_e)%a ->

      system_inv
    ∗ na_inv logrel_nais n
        (codefrag cf_b pc_v sensor_lcode
         ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
         ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
         ∗ (∃ γ : gname, one_shot_inv γ data_b data_e data_v))
    ⊢ sensor_enclave_read_sensor_contract pc_b pc_e (pc_b ^+ sensor_read_off)%a pc_v ret φ.
  Proof.
    iIntros (pc_b pc_e cf_b cf_e Hpc_b_e Hdata_b_e) "[#Henclave_inv #Hts_inv] !>".
    iIntros "(Hna & HPC & Hr0 & [%lw1 Hr1] & [%lw2 Hr2] & [%lw3 Hr3] & Hret)".

    assert (SubBounds pc_b pc_e cf_b cf_e).
    { subst pc_e pc_b cf_e cf_b.
      rewrite /sensor_code_len /sensor_read_off /sensor_read_len.
      solve_addr. }
    assert (withinBounds pc_b pc_e pc_b = true) as Hpcbounds.
    { subst pc_e; apply le_addr_withinBounds; solve_addr. }
    assert (withinBounds data_b data_e data_b = true) as Hdatabounds.
    { apply le_addr_withinBounds; solve_addr. }

    iMod (na_inv_acc with "Hts_inv Hna") as
      "(>(Hts_code & Hts_keys & Hts_addr & [%γ Hts_data]) & Hna & Hclose)"; [solve_ndisj ..|].

    (* Code memory *)
    codefrag_facts "Hts_code".

  Admitted.

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

    iMod (na_inv_alloc logrel_nais _ (system_invN.@hash_sensor)
            (codefrag cf_b pc_v sensor_lcode
             ∗ (pc_b, pc_v) ↦ₐ LCap RW data_b data_e data_a data_v
             ∗ (data_b, data_v) ↦ₐ LSealRange (true, true) ot (ot ^+ 2)%f ot
             ∗ ∃ γ, one_shot_inv γ data_b data_e data_v)%I
           with "[$Hts_code $Hts_addr $Hts_keys Hauth Hts_data]") as "#Hts_inv".
    { iNext. iExists γ. iLeft. iFrame "Hauth". by iExists enclave_data. }
    clear γ enclave_data.

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
      "(>(Hts_code & Hts_addr & Hts_keys & [%γ Hts_data]) & Hna & Hclose)";
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
    iApply (wp_isunique_success' with "[HPC Hr1 Hr3 Hi]"); try iFrame; try solve_pure.
    { admit. }
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
    2: { (* Store fail *) admit. }

    iAssert ((∃ lw_a, (mmio_a, (mmio_v + 1)%nat) ↦ₐ lw_a)%I)
      with "[Hlmmio]" as "[%lw_a Hmmio_a]".
    { pose proof (withinBounds_in_seq_1 _ _ _ Hmmiobounds) as Hlookup.
      apply elem_of_list_lookup in Hlookup.
      destruct Hlookup as [i Hlookup].
      assert (exists lw_a, lmmio !! i = Some lw_a) as [lw_a Hlookup2] by admit.
      iExists lw_a.
      iDestruct (big_sepL2_lookup_acc with "Hlmmio") as "[Hmmio_a _]"; eauto.
      now rewrite list_lookup_fmap Hlookup.
    }
    iInstr "Hts_code". (* Store r_t1 42 *)
    clear lw_a.

    (* Get the data capability *)
    iInstr "Hts_code". (* Lea r_t2 (begin - init) *)
    transitivity (Some pc_b); [rewrite /sensor_fail_off; subst cf_b; solve_addr|easy].
    iInstr "Hts_code". (* Load r_t3 r_t2 *)
    easy.
    iInstr "Hts_code". (* GetB r_t4 r_t3 *)
    iInstr "Hts_code". (* GetA r_t5 r_t3 *)
    iInstr "Hts_code". (* Sub r_t4 r_t4 r_t5 *)
    iInstr "Hts_code". (* Lea r_t3 r_t4 *)
    transitivity (Some data_b); solve_addr.
    iInstr "Hts_code". (* Lea r_t3 1 *)
    transitivity (Some (data_b ^+ 1)%a); solve_addr.

    (* Store mmio capability. *)
    iMod (one_shot_update with "Hts_data") as "[#Htoken Hts_data]"; try solve_addr.
    iDestruct "Hts_data" as "[%Heq|[%lw Hts_mmio]]".
    { admit. }
    iInstr "Hts_code". (* Store r_t3 r_t1 *)
    admit. (* TODO: check for bounds in code *)
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
    { transitivity (Some (pc_b ^+ sensor_read_off))%a; [|easy].
      rewrite /sensor_read_off. solve_addr. }
    iInstr "Hts_code". (* Restrict r_t1 Eperm *)
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
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_sensor; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_sensor_persistent. }
      { iNext. do 4 iExists _. iSplit; [easy|]. iIntros (ret φ).
        iApply (sensor_enclave_read_sensor_correct with "[$Henclave_inv $Hts_inv]");
          subst cf_b cf_e pc_b pc_e; solve_addr.
      }
    }
    iAssert (
        interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f)
      ) as "Hinterp_sealr_ot".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /safe_to_unseal).
      iSplit ; first done.
      rewrite finz_seq_between_singleton ; last solve_finz.
      iSplit ; last done.
      iSplit ; last done.
      iExists sealed_sensor_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply sealed_sensor_interp.
    }

    (* Close the opened invariant *)
    iMod ("Hclose" with "[$Hna $Hts_code $Hts_addr $Hts_keys Htoken Hts_mmio]") as "Hna".
    iNext. iExists γ. iRight. iFrame "Htoken". do 4 iExists _. by iFrame.

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
  Admitted.

End SensorEnclaveProofs.
