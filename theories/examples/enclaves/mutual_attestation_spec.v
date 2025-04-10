From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import assert macros_new.
From cap_machine Require Import
  mutual_attestation_code
  mutual_attestation_A_spec
  mutual_attestation_B_spec
.


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
  Qed.

  (* -------------------------------------------------- *)
  (* ---------------------- MAIN ---------------------- *)
  (* -------------------------------------------------- *)


  Lemma mutual_attestation_main_attest_or_fail_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (expected_hash : Z) (r : RegName) (w w5 w6: LWord)
    φ :
    let code :=  mutual_attestation_main_attest_or_fail r expected_hash in
    let otype_w := match lword_get_word w with
                   | WSealed o _ => o
                   | _ => (-1)%Z
                   end
    in
    let pc_a' := (pc_a ^+ length code)%a in
    (pc_a + length code)%a = Some pc_a' ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ (length code))%a ->

    ( PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v
      ∗ r ↦ᵣ w ∗ r_t5 ↦ᵣ w5 ∗ r_t6 ↦ᵣ w6
      ∗ codefrag pc_a pc_v code
      ∗ ▷ ( (∃ tid,
                ⌜ has_seal otype_w tid ⌝
                ∗ enclave_all tid expected_hash
                ∗ PC ↦ᵣ LCap RX pc_b pc_e pc_a' pc_v
                ∗ r ↦ᵣ w ∗ (∃ w5', r_t5 ↦ᵣ w5') ∗ (∃ w6', r_t6 ↦ᵣ w6')
                ∗ codefrag pc_a pc_v code)
            -∗ WP Seq (Instr Executable) {{ v, φ v ∨ ⌜ v = FailedV ⌝ }}
      )
    )
   ⊢ WP Seq (Instr Executable) {{ v, φ v ∨ ⌜ v = FailedV ⌝ }}.
  Proof.
    intros code otype_w pc_a' Hpc_a' Hbounds; subst code.
    iIntros "(HPC & Hr & Hr5 & Hr6 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    iInstr "Hcode".
    { transitivity (Some otype_w); auto.
      destruct w ; auto.
      by destruct sb.
    }

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_estoreid_success_unknown with "[$HPC $Hr6 $Hr5 $Hi]"); try solve_pure.
    iNext. iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr5 & [(-> & HPC & H)|(-> & HPC & Hr6)])".
    1: iDestruct "H" as (I tid) "(Hr6 & #Hma_env & %Hseal)".
    all: wp_pure; iInstr_close "Hcode".
    2:{ wp_end; by iRight. }

    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    destruct (decide (I = expected_hash)) as [-> | HnI]
    ; cycle 1.
    { (* Not the right enclave *)
      iInstr "Hcode". (* Jnz *)
      by (injection; intro Hcontra; lia).
      iInstr "Hcode". (* Fail *)
      wp_end; by iRight.
    }
    replace ( _ - _)%Z with 0%Z by lia.
    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    iApply "Hφ".
    iExists tid; iFrame "∗#%".
    iSplitL "Hr5" ; iExists _ ; iFrame.
  Qed.

  Lemma mutual_attestation_main_get_confirm_or_fail_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (r r' : RegName) (ot_w : OType) sb_w
    (w' w5 w6: LWord)
    (tid : TIndex) (expected_hash : Z)
    (mutual_attest_enclave_pred : @CustomEnclave Σ)
    φ (Φ : LWord → iProp Σ)
    `{ HPenc : Penc mutual_attest_enclave_pred = (λ _ : LWord, False)%I}
    `{ HPsign_pers :∀ lw, Persistent (Psign mutual_attest_enclave_pred lw) }
    :
    let code := mutual_attestation_main_get_confirm_or_fail r r' in
    let pc_a' := (pc_a ^+ (length code))%a in
    (pc_a + (length code))%a = Some pc_a' ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ (length code))%a ->
    has_seal ot_w tid ->
    ma_enclaves_map !! expected_hash = Some mutual_attest_enclave_pred ->

    ( (∀ w, (Psign mutual_attest_enclave_pred w) -∗
          ⌜ ∃ b e a v, w = LCap O b e a v ∧ ( (b `mod` 2)%Z ≠ 0 -> a = f1) ⌝)
      ∗ custom_enclave_inv ma_enclaves_map
      ∗ enclave_all tid expected_hash
      ∗ □ valid_sealed (LWSealed ot_w sb_w) ot_w Φ
      ∗ PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v
      ∗ r ↦ᵣ LWSealed ot_w sb_w ∗ r' ↦ᵣ w' ∗ r_t5 ↦ᵣ w5 ∗ r_t6 ↦ᵣ w6
      ∗ codefrag pc_a pc_v code
      ∗ ▷ ( (PC ↦ᵣ LCap RX pc_b pc_e pc_a' pc_v
            ∗ r ↦ᵣ LInt f1 ∗ r' ↦ᵣ w' ∗ (∃ w5', r_t5 ↦ᵣ w5') ∗ (∃ w6', r_t6 ↦ᵣ w6')
            ∗ codefrag pc_a pc_v code)
            -∗ WP Seq (Instr Executable) {{ v, φ v ∨ ⌜ v = FailedV ⌝ }}
      )
    )
   ⊢ WP Seq (Instr Executable) {{ v, φ v ∨ ⌜ v = FailedV ⌝ }}.
  Proof.
    intros code pc_a' Hpc_a' Hbounds Hseal Hma_expected_enclave; subst code.
    iIntros "(Hpsign & #Henclaves_inv & #Htid & #Hseal_valid & HPC & Hr & Hr' & Hr5 & Hr6 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    iDestruct ( regname_neq with "[$HPC] [$Hr]") as %HPCr.
    iDestruct ( regname_neq with "[$HPC] [$Hr']") as %HPCr'.
    iDestruct ( regname_neq with "[$Hr] [$Hr']") as %Hrr'.

    wp_instr.
    iMod (inv_acc with "Henclaves_inv") as "(Henclaves_inv_open & Hclose_inv)"; first solve_ndisj.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr Hr'") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds' Hregs'|]; cycle 1.
    { iMod ("Hclose_inv" with "Henclaves_inv_open") as "_". iModIntro.
      by wp_pure; wp_end; by iRight.
    }
    iDestruct "Henclaves_inv_open" as (ECn) "(HEC & #Hcemap)".
    iMod ("Hclose_inv" with "[HEC Hcemap]") as "_"; iModIntro.
    { iExists ECn. iFrame "HEC Hcemap". }
    incrementLPC_inv as (p''&pc_b'&pc_e'&pc_a''&pc_v'& ? & HPC & Z & Hregs');
      simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    replace x with (pc_a'' ^+ 1)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr Hr'] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hcode".

    iAssert (
        if Z.even a
        then seal_pred a (Penc mutual_attest_enclave_pred)
             ∗ seal_pred (a ^+ 1)%f (Psign mutual_attest_enclave_pred)
        else seal_pred (a ^+ -1)%f (Penc mutual_attest_enclave_pred)
             ∗ seal_pred a (Psign mutual_attest_enclave_pred)
      )%I as "Hma".
    {
      iApply "Hcemap"; iFrame "%#∗".
      + iPureIntro. admit.
      + iPureIntro; apply wf_ma_enclaves_map.
    }
    rewrite HPenc.
    destruct (Z.even (finz.to_z a)) eqn:HEven_a
    ; iDestruct "Hma" as "[Hma_Penc Hma_Psign]"
    ; iEval (cbn) in "Hma_Penc"
    ; iEval (cbn) in "Hma_Psign".
    { iDestruct (seal_pred_valid_sealed_eq with "[$Hma_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }
    iDestruct (seal_pred_valid_sealed_eq with "[$Hma_Psign] Hseal_valid") as "Heqv".
    iAssert (▷ (Psign mutual_attest_enclave_pred) (LWSealable sb))%I as "Hseal".
    { iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      iRewrite "Heqv".
      iFrame "HΦ". }
    iClear "Heqv Hma_Penc".

    iDestruct ("Hpsign" with "Hseal") as ">%Hseal'".
    destruct Hseal' as (b' & e' & a' & v' & -> & Hmod).

    iInstr "Hcode".
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hr5 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hi & Hr5)".
    iEval (cbn) in "Hr5".
    wp_pure; iInstr_close "Hcode".

    iInstr "Hcode".
    iInstr "Hcode".
    destruct (decide ((b' `mod` 2%nat)%Z = 0%Z)) as [-> | Hfb].
    {
      (* Jnz r_t5 r_t2 *)
      iInstr "Hcode".
      (* Fail *)
      iInstr "Hcode".
      wp_end ; by iRight.
    }

    iInstr "Hcode".
    { by intro Hcontra; inv Hcontra. }
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply (wp_Get_same_success with "[$HPC $Hr $Hi]"); try solve_pure.
    iNext. iIntros "(HPC & Hi & Hr)".
    wp_pure; iInstr_close "Hcode".

    rewrite Hmod; auto.
    iApply "Hφ"; iFrame.
    iSplitL "Hr5" ; iExists _ ; iFrame.
  Admitted.



  Lemma mutual_attestation_main_get_confirm_or_fail_spec'
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (r r' : RegName) (w w' : LWord) φ
    :
    let code := mutual_attestation_main_get_confirm_or_fail r r' in
    let pc_a' := (pc_a ^+ (length code))%a in
    (pc_a + (length code))%a = Some pc_a' ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ (length code))%a ->
    is_sealedL w = false ->

    ( PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v
      ∗ r ↦ᵣ w ∗ r' ↦ᵣ w'
      ∗ codefrag pc_a pc_v code
    )
   ⊢ WP Seq (Instr Executable) {{ v, φ v ∨ ⌜ v = FailedV ⌝ }}.
  Proof.
    intros code pc_a' Hpc_a' Hbounds Hsealed; subst code.
    iIntros "(HPC & Hr & Hr' & Hcode)".
    codefrag_facts "Hcode".
    iDestruct ( regname_neq with "[$HPC] [$Hr]") as %HPCr.
    iDestruct ( regname_neq with "[$HPC] [$Hr']") as %HPCr'.
    iDestruct ( regname_neq with "[$Hr] [$Hr']") as %Hrr'.
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr Hr'") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds' Hregs'|]; cycle 1.
    { by wp_pure; wp_end; iRight. }
    simplify_map_eq.
  Qed.


  Definition mutual_attestationN : namespace := nroot .@ "mutual_attestation".
  (* Define all the invariants *)
  (* Linking table invariant *)
  Definition link_tableN := (mutual_attestationN.@"link_table").
  Definition link_table_inv
    v_link
    assert_entry b_assert e_assert v_assert :=
    na_inv logrel_nais link_tableN
         ((assert_entry, v_link) ↦ₐ LCap E b_assert e_assert b_assert v_assert)%I.

  (* Assert invariant *)
  Definition assertN := (mutual_attestationN.@"assert").
  Definition assert_inv b_a a_flag e_a v_assert :=
    na_inv logrel_nais assertN (assert_inv b_a a_flag e_a v_assert).

  Definition flag_assertN := (mutual_attestationN.@"flag_assert").
  Definition flag_inv a_flag v_flag :=
    inv flag_assertN ((a_flag,v_flag) ↦ₐ LInt 0%Z).


  Lemma mutual_attest_full_run_spec
    (pc_b pc_e : Addr)
    (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (* assert *)

    (rmap : LReg)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let code := mutual_attestation_main_code assert_lt_offset in
    let e_main := (pc_b ^+ (length code))%a in
    let a_data := (e_main ^+ 1)%a in

    (e_main + 1)%a = Some a_data ->
    (a_data + 1)%a = Some pc_e ->
    SubBounds pc_b pc_e pc_b e_main ->


    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->

    (link_table_inv v_link assert_entry b_assert e_assert v_assert
    ∗ assert_inv b_assert a_flag e_assert v_assert
    ∗ flag_inv a_flag v_assert)
    ∗ custom_enclave_inv ma_enclaves_map
    ∗ full_map rmap
    ∗ (∀ (r : RegName) (lv : LWord), ⌜r ≠ PC⌝ → ⌜rmap !! r = Some lv⌝ → fixpoint interp1 lv)

    ⊢ ( codefrag pc_b pc_v code
        ∗ (a_data, pc_v) ↦ₐ link_cap
        ∗ PC ↦ᵣ LCap RX pc_b pc_e pc_b pc_v
        ∗ registers_mapsto rmap
        ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable)
               {{λ v, (⌜v = HaltedV⌝ →
                       ∃ r : LReg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)%I
                      ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros ????? He_main Ha_data HsubBounds Hassert Hlink.
    iIntros "( #(HlinkInv & HassertInv & HflagInv)  & #Hcemap_inv & %Hfullmap & #Hrmap_interp)
             (Hcode & Hadata & HPC & Hrmap & Hna)".
    rewrite /registers_mapsto.
    (* Prepare the necessary resources *)
    (* Registers *)
    assert (exists w0, rmap !! r_t0 = Some w0) as [w0 Hr0] by apply (Hfullmap r_t0).
    assert (exists w1, rmap !! r_t1 = Some w1) as [w1 Hr1] by apply (Hfullmap r_t1).
    assert (exists w2, rmap !! r_t2 = Some w2) as [w2 Hr2] by apply (Hfullmap r_t2).
    assert (exists w3, rmap !! r_t3 = Some w3) as [w3 Hr3] by apply (Hfullmap r_t3).
    assert (exists w4, rmap !! r_t4 = Some w4) as [w4 Hr4] by apply (Hfullmap r_t4).
    assert (exists w5, rmap !! r_t5 = Some w5) as [w5 Hr5] by apply (Hfullmap r_t5).
    assert (exists w6, rmap !! r_t6 = Some w6) as [w6 Hr6] by apply (Hfullmap r_t6).

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
    iDestruct (big_sepM_delete _ _ r_t6 with "Hrmap") as "[Hr6 Hrmap]".
    { by simplify_map_eq. }
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hrmap_interp";eauto;done. }
    iAssert (interp w2) as "Hinterp_w2".
    { iApply "Hrmap_interp";eauto;done. }

    subst e_main a_data.
    replace ((pc_b ^+ length (mutual_attestation_main_code assert_lt_offset)) ^+ 1)%a
      with (pc_e ^+ (-1)%Z)%a by solve_addr.
    codefrag_facts "Hcode".

    (* BLOCK 0: attest A *)
    focus_block_0 "Hcode" as "Hcode" "Hcode_cont".
    destruct (is_sealedL w0) eqn:Hw0; cycle 1.
    {
      iApply (mutual_attestation_main_attest_or_fail_spec with "[- $HPC $Hcode $Hr0 $Hr5 $Hr6]"); eauto.
      { solve_addr. }
      iNext ; iIntros "H".
      iDestruct "H" as (tid) "(%Hhas_seal & #Henclave_tid & HPC & Hr0 & Hr5 & Hr6 & Hcode)".
      iDestruct "Hr5" as (w5') "Hr5".
      iDestruct "Hr6" as (w6') "Hr6".
      unfocus_block "Hcode" "Hcode_cont" as "Hcode".
      focus_block 1 "Hcode" as a_block1 Ha_block1 "Hcode" "Hcode_cont".
      iApply (mutual_attestation_main_get_confirm_or_fail_spec'
              with "[- $HPC $Hr0 $Hr1 $Hcode]"); eauto; solve_addr.
    }
    destruct w0 as [| | ot_w0 sb_w0]; cbn in Hw0; try congruence.
    iDestruct (interp_valid_sealed with "Hinterp_w0") as (Φ_A) "Hseal_valid_w0".
    iApply (mutual_attestation_main_attest_or_fail_spec
             with "[- $HPC $Hcode $Hr0 $Hr5 $Hr6]"); eauto.
    { solve_addr. }
    iNext ; iIntros "H".
    iDestruct "H" as (tid_A) "(%Hhas_seal_A & #Henclave_tid_A & HPC & Hr0 & Hr5 & Hr6 & Hcode)".
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 1: get confirm A *)
    focus_block 1 "Hcode" as a_block1 Ha_block1 "Hcode" "Hcode_cont".
    iApply ( (mutual_attestation_main_get_confirm_or_fail_spec _ _ _ _ _ _ _ _ _ _ _ _ _ mutual_attest_enclave_A_pred )
             with "[- $HPC $Hcode $Hr0 $Hr1 $Hr5 $Hr6 $Hseal_valid_w0 $Henclave_tid_A $Hcemap_inv]"); eauto.
    { solve_addr. }
    { by rewrite /ma_enclaves_map ; simplify_map_eq. }
    iSplitR.
    { iIntros (lw) "H".
      cbn.
      rewrite /sealed_enclaveA.
      iDestruct "H" as (b e v) "->".
      iPureIntro.
      eexists _,_,_,_; split; auto.
      intros.
      rewrite /prot_sealed_A.
      destruct ( decide ((b `mod` 2%nat)%Z = 0%Z)); first lia.
      done.
    }
    iNext.
    iIntros "(HPC & Hr0 & Hr1 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 2: attest B *)
    focus_block 2 "Hcode" as a_block2 Ha_block2 "Hcode" "Hcode_cont".
    clear Ha_block1 a_block1.
    destruct (is_sealedL w2) eqn:Hw2; cycle 1.
    {
      iApply (mutual_attestation_main_attest_or_fail_spec
               with "[- $HPC $Hcode $Hr2 $Hr5 $Hr6]"); eauto.
      { solve_addr. }
      iNext ; iIntros "H".
      iDestruct "H" as (tid_B) "(%Hhas_seal_B & #Henclave_tid_B & HPC & Hr2 & Hr5 & Hr6 & Hcode)".
      clear w5' w6'.
      iDestruct "Hr5" as (w5') "Hr5".
      iDestruct "Hr6" as (w6') "Hr6".
      unfocus_block "Hcode" "Hcode_cont" as "Hcode".
      focus_block 3 "Hcode" as a_block3 Ha_block3 "Hcode" "Hcode_cont".
      iApply (mutual_attestation_main_get_confirm_or_fail_spec'
              with "[- $HPC $Hr2 $Hr3 $Hcode]"); eauto; solve_addr.
    }
    destruct w2 as [| | ot_w2 sb_w2]; cbn in Hw2; try congruence.
    iDestruct (interp_valid_sealed with "Hinterp_w2") as (Φ_B) "Hseal_valid_w2".
    iApply (mutual_attestation_main_attest_or_fail_spec
             with "[- $HPC $Hcode $Hr2 $Hr5 $Hr6]"); eauto.
    { solve_addr. }
    iNext ; iIntros "H".
    iDestruct "H" as (tid_B) "(%Hhas_seal_B & #Henclave_tid_B & HPC & Hr2 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 3: get confirm attest B *)
    focus_block 3 "Hcode" as a_block3 Ha_block3 "Hcode" "Hcode_cont".
    clear Ha_block2 a_block2.
    iApply ( (mutual_attestation_main_get_confirm_or_fail_spec _ _ _ _ _ _ _ _ _ _ _ _ _ mutual_attest_enclave_B_pred )
             with "[- $HPC $Hcode $Hr2 $Hr3 $Hr5 $Hr6 $Hseal_valid_w2 $Henclave_tid_B $Hcemap_inv]"); eauto.
    { solve_addr. }
    { rewrite /ma_enclaves_map.
      rewrite lookup_insert_ne //; first by simplify_map_eq.
      rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
      intro Hcontra.
      apply hash_concat_inj' in Hcontra.
      destruct Hcontra as [_ Hcontra].
      rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra.
      by injection Hcontra.
    }
    iSplitR.
    { iIntros (lw) "H".
      cbn.
      rewrite /sealed_enclaveB.
      iDestruct "H" as (b e v) "->".
      iPureIntro.
      eexists _,_,_,_; split; auto.
      intros.
      rewrite /prot_sealed_B.
      destruct ( decide ((b `mod` 2%nat)%Z = 0%Z)); first lia.
      done.
    }
    iNext.
    iIntros "(HPC & Hr2 & Hr3 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 4: prepare assert A *)
    focus_block 4 "Hcode" as a_block4 Ha_block4 "Hcode" "Hcode_cont".
    clear Ha_block3 a_block3.
    assert ( ((a_block4 ^+ 1)%a + (pc_e - (a_block4 ^+ 1)))%a = Some pc_e) as Hpc_e by solve_addr.
    iGo "Hcode".
    { transitivity (Some (pc_e ^+ -1)%a); solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    iGo "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 5: assert (confirm A) == 1 *)
    focus_block 5 "Hcode" as a_block5 Ha_block5 "Hcode" "Hcode_cont".
    clear Hpc_e Ha_block4 a_block4.
    iMod (na_inv_acc with "HlinkInv Hna") as "(>Hassert_entry & Hna & Hclose)"; [ solve_ndisj.. |].
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try reflexivity.
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr1 & Hr2 & Hr4 & Hr5 & Hcode & Hna & Hassert_entry)".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 6: prepare assert B *)
    focus_block 6 "Hcode" as a_block6 Ha_block6 "Hcode" "Hcode_cont".
    clear Ha_block5 a_block5.
    iInstr "Hcode".
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 7: assert (confirm B) == 1 *)
    focus_block 7 "Hcode" as a_block7 Ha_block7 "Hcode" "Hcode_cont".
    clear Ha_block6 a_block6.
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try reflexivity.
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr3 & Hr2 & Hr4 & Hr5 & Hcode & Hna & Hassert_entry)".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 8: halt *)
    focus_block 8 "Hcode" as a_block8 Ha_block8 "Hcode" "Hcode_cont".
    clear Ha_block7 a_block7.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    iMod ("Hclose" with "[$Hassert_entry $Hna]") as "Hna".
    wp_end; iLeft.
    iIntros "_".
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
    { do 6 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 6 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    { do 5 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 5 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
    { do 4 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 4 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hrmap $Hr3]") as "Hrmap".
    { do 3 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 3 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t4 with "[$Hrmap $Hr4]") as "Hrmap".
    { do 2 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 2 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hrmap $Hr5]") as "Hrmap".
    { do 1 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 1 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hrmap $Hr6]") as "Hrmap".
    { do 0 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 0 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    match goal with
    | H: _ |- context [ <[r_t6:=LInt 1]> ?x ] =>
        set (rmap' := <[r_t6:=LInt 1]> x )
    end.
    iExists rmap'; iFrame.
    iPureIntro.
    intros r; subst rmap'; cbn.
    destruct ((decide (r = r_t6))); simplify_map_eq; first done.
    destruct ((decide (r = r_t5))); simplify_map_eq; first done.
    destruct ((decide (r = r_t4))); simplify_map_eq; first done.
    destruct ((decide (r = r_t3))); simplify_map_eq; first done.
    destruct ((decide (r = r_t2))); simplify_map_eq; first done.
    destruct ((decide (r = r_t1))); simplify_map_eq; first done.
    destruct ((decide (r = r_t0))); simplify_map_eq; done.
  Qed.


End mutual_attest_main.
