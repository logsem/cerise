From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import trusted_compute_code.
Open Scope Z_scope.


Section trusted_compute_enclave.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.
  Context {TC : TrustedCompute}.

  Lemma tc_enclave_contract :
    ⊢ custom_enclave_contract (enclaves_map := contract_tc_enclaves_map).
  Proof.
    iLöb as "IH".
    rewrite -/custom_enclave_contract.
    iEval (rewrite /custom_enclave_contract).
    iIntros (I b e v b' e' a' v' enclave_data ot ce
      Hcode_ce Hot HIhash Hb He)
      "(#Hcustoms_inv & #Htc_inv & #HPenc & #HPsign)".
    assert (e = (b ^+ (length (code ce) + 1))%a) as -> by solve_addr+He.
    simplify_map_eq.
    rewrite /tcenclaves_map in Hcode_ce.
    replace ((λ w : Word, word_to_lword w v) <$> code ce) with trusted_compute_enclave_lcode.
    2:{ simplify_map_eq. cbn. rewrite /encodeInstrWL. done. }
    simplify_map_eq.
    rewrite -H; clear H.
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext ; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Htc_inv Hna") as "(>[Htc_code Htc_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    remember tc_addr as pc_b in |- * at 7.
    remember (tc_addr ^+ (20%nat + 1))%a as pc_e in |- * at 4.
    assert (SubBounds pc_b pc_e tc_addr (tc_addr ^+ (20%nat + 1))%a) by (subst; solve_addr).

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
    (* Code memory *)
    iDestruct (region_mapsto_cons with "Htc_code") as "[Htc_addr Htc_code]"; last iFrame.
    { transitivity (Some (tc_addr ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }
    iAssert (codefrag (tc_addr ^+ 1%nat)%a v trusted_compute_enclave_lcode)
      with "[Htc_code]" as "Htc_code".
    {
      rewrite /codefrag /=.
      by replace ((tc_addr ^+ 1%nat) ^+ 20%nat)%a with (tc_addr ^+ 21%nat)%a by solve_addr.
    }
    codefrag_facts "Htc_code".

    (* Data memory *)
    iAssert (⌜ (b' < e')%a ⌝)%I as "%Hb'".
    {
      iDestruct (big_sepL2_length with "Htc_data") as "%Htc_data_len".
      rewrite map_length /= in Htc_data_len.
      iPureIntro.
      clear - Htc_data_len.
      destruct (decide (b' < e')) as [He' | He']; cycle 1.
      - rewrite finz_seq_between_empty in Htc_data_len; last solve_addr.
        cbn in * ; discriminate.
      - done.
    }
    iDestruct (region_mapsto_cons with "Htc_data") as "[Htc_keys Htc_data]"; last iFrame.
    { transitivity (Some (b' ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }


    (* Prove the spec *)
    iInstr "Htc_code". (* Mov r_t1 PC *)
    iInstr "Htc_code". (* Lea r_t1 (-1)%Z *)
    transitivity (Some tc_addr); auto ; solve_addr.

    iInstr "Htc_code". (* Load r_t1 r_t1 *)
    apply le_addr_withinBounds; solve_addr.
    iInstr "Htc_code". (* GetB r_t2 r_t1 *)
    iInstr "Htc_code". (* GetA r_t3 r_t1 *)
    iInstr "Htc_code". (* Sub r_t2 r_t2 r_t3 *)
    iInstr "Htc_code". (* Lea r_t1 r_t2 *)
    transitivity (Some b'); auto ; solve_addr.

    iInstr "Htc_code". (* Load r_t1 r_t1 *)
    apply le_addr_withinBounds; solve_addr.
    iInstr "Htc_code". (* GetE r_t3 r_t1 *)
    iInstr "Htc_code". (* Sub r_t3 r_t2 1 *)
    replace (((ot ^+ 2)%f - 1)) with (ot + 1) by solve_finz.
    iInstr "Htc_code". (* Subseg r_t1 r_t2 r_t3 *)
    transitivity (Some (ot ^+1)%ot); auto ; solve_finz.
    apply isWithin_of_le; solve_finz.

    iInstr "Htc_code". (* Mov r_t2 PC *)
    iInstr "Htc_code". (* GetA r_t3 r_t2 *)
    iInstr "Htc_code". (* Sub r_t3 42 r_t3 *)

    assert (
        ((tc_addr ^+ 1) ^+ 11 + (42 - ((tc_addr ^+ 1) ^+ 11)))%a = Some f42)
      as Hoffset by (by rewrite finz_incr_minus_id).
    iInstr "Htc_code". (* Lea r_t2 r_t3 *)
    iInstr "Htc_code". (* Restrict r_t2 (encodePerm O) *)
    by rewrite decode_encode_perm_inv.
    rewrite decode_encode_perm_inv.
    iInstr "Htc_code". (* Lea r_t1 1 *)
    transitivity (Some (ot ^+ 1)%ot); auto ; solve_finz.
    iInstr "Htc_code". (* Seal r_t2 r_t2 r_t1 *)
    by cbn.
    apply le_addr_withinBounds; solve_finz.

    (* Restrict r_t1 (encodeSealPerms (false, true)) *)
    iInstr_lookup "Htc_code" as "Hi" "Htc_code".
    wp_instr.
    iApply (wp_restrict_success_z_sr with "[HPC Hr1 Hi]")
    ; try iFrame
    ; try solve_pure
    ; repeat (rewrite decode_encode_seal_perms_inv)
    ; try done.
    iNext; iIntros "(HPC & Hi & Hr1)".
    all: wp_pure; iInstr_close "Htc_code".

    (* Prepare the jump to adversary: prove all registers contain safe values *)
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map" ; eauto; done. }

    iAssert (interp (LSealedCap (ot ^+ 1)%f O tc_addr (tc_addr ^+ 21%nat)%a f42 v))
      as "Hinterp_sealed42".
    {
      iClear "Hinterp_map Hinterp_w0".
      rewrite /= fixpoint_interp1_eq /= /interp_sb.
      iExists sealed_42; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_42_persistent. }
      { iNext; by iExists _,_,_. }
    }

    iAssert (interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f))
      as "Hinterp_sign".
    {
      iClear "Hinterp_map Hinterp_w0 Hinterp_sealed42".
      rewrite /= fixpoint_interp1_eq /= /safe_to_unseal.
      iSplit ; first done.
      rewrite finz_seq_between_singleton; cbn ; last solve_finz.
      iSplit ; last done.
      iSplit ; last done.
      iExists sealed_42_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply sealed_42_interp.
    }

    iDestruct (jmp_to_unknown with "[] [$Hinterp_w0]") as "Hjmp"; eauto.
    {
      iSplit; last iFrame "#".
      iModIntro.
      by iApply custom_enclave_contract_inv.
    }
    iInstr "Htc_code". (* Jmp r_t0 *)

    (* Close the opened invariant *)
    iDestruct (region_mapsto_cons with "[Htc_addr Htc_code]") as "Htc_code"
    ; try iFrame
    ; try solve_addr.
    iDestruct (region_mapsto_cons with "[Htc_keys Htc_data]") as "Htc_data"
    ; try iFrame
    ; try solve_addr.
    replace ((tc_addr ^+ 1%nat)%a ^+ length trusted_compute_enclave_lcode)%a with
      (tc_addr ^+ 21%nat)%a by solve_addr.
    iMod ("Hclose" with "[$Hna $Htc_code $Htc_data]") as "Hna".
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

    set ( rmap' := <[r_t3:=LInt (42 - ((tc_addr ^+ 1) ^+ 11)%a)]>
                            (<[r_t2:=LSealedCap (ot ^+ 1)%f O tc_addr (tc_addr ^+ 21%nat)%a f42 v]>
                               (<[r_t1:=LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f]>
                                  (<[r_t0:=w0]> (delete PC lregs))))).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      subst pc_b pc_e.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
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
End trusted_compute_enclave.
