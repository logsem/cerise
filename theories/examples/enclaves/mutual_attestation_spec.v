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
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.


  (* -------------------------------------------------- *)
  (* ------------------- ENCLAVES --------------------- *)
  (* -------------------------------------------------- *)

  Lemma mutual_attest_contract :
    ⊢ custom_enclave_contract (enclaves_map := contract_ma_enclaves_map).
  Proof.
    iLöb as "IH".
    iEval (rewrite /custom_enclave_contract).
    iIntros (I b e v b' e' a' v' enclave_data ot ce
      Hcode_ce Hot HIhash Hb He)
      "(#Henclaves_inv & #Hma_inv & #HPenc & #HPsign)".
    assert (e = (b ^+ (length (code ce) + 1))%a) as -> by solve_addr+He.

    assert (I = hash_mutual_attest_A \/ I = hash_mutual_attest_B) as HI.
    { rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      done.
    }
    destruct HI.
		- rewrite H in HIhash.
			simplify_map_eq.
			rewrite /ma_enclaves_map lookup_insert // in Hcode_ce; simplify_eq.
      replace ( ((λ w : Word, word_to_lword w v) <$> code mutual_attest_enclave_A_pred) )
        with mutual_attest_enclave_A_lcode.
      2:{ simplify_map_eq; cbn. rewrite /encodeInstrWL; done. }
			iApply ( mutual_attest_A_contract with "[]") ; last iFrame "#"; eauto.
    - rewrite lookup_insert_ne // in Hcode_ce.
      2:{
        rewrite H.
        rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
        intro Hcontra.
          apply hash_concat_inj' in Hcontra.
          destruct Hcontra as [_ Hcontra].
          by injection Hcontra.
      }
      replace ( ((λ w : Word, word_to_lword w v) <$> code ce) )
        with mutual_attest_enclave_B_lcode.
      2:{ simplify_map_eq; cbn. rewrite /encodeInstrWL; done. }
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
      ∗ system_inv (enclaves_map := contract_ma_enclaves_map)
      ∗ ▷ ( (∃ tid ECn,
                ⌜ has_seal otype_w tid ⌝
                ∗ ⌜ 0 <= tid < ECn ⌝
                ∗ (
                    □ ∀ (I : EIdentity) (tid : TIndex) (ot : OType) (ce : CustomEnclave),
                      (⌜(0 <= tid < ECn)⌝) -∗
                      enclave_all tid I
                      ∗ ⌜ ma_enclaves_map !! I = Some ce ⌝
                      ∗ ⌜ has_seal ot tid ⌝ -∗
                      if (Z.even (finz.to_z ot))
                      then (seal_pred ot (Penc ce) ∗ seal_pred (ot ^+ 1)%ot (Psign ce))
                      else (seal_pred (ot ^+ (-1))%ot (Penc ce) ∗ seal_pred ot (Psign ce))
                  )%I
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
    iIntros "(HPC & Hr & Hr5 & Hr6 & Hcode & Hcemap_inv & Hφ)".
    codefrag_facts "Hcode".
    iInstr "Hcode".
    { transitivity (Some otype_w); auto.
      destruct w ; auto.
      by destruct sb.
    }

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hcemap_inv") as "(Hcemap & Hclose)"; first solve_ndisj.
    iDestruct "Hcemap" as (ECn OTn) "(>HEC & ECn_OTn & Hallocated_seals & Hfree_seals & #Hcemap)".
    iApply (wp_estoreid_success_unknown_ec with "[HPC Hr6 Hr5 Hi $HEC]"); try iFrame; try solve_pure.
    iNext.
    iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr5 & HEC & [(-> & HPC & H)|(-> & HPC & Hr6)])".
    1: iDestruct "H" as (I tid) "(Hr6 & #Htc_env & [%Hseal %Htidx])".
    all: iMod ("Hclose" with "[HEC ECn_OTn Hallocated_seals Hfree_seals Hcemap]") as "_"
    ; [ iExists ECn, OTn; iFrame "HEC Hcemap ECn_OTn Hallocated_seals Hfree_seals"; eauto | iModIntro].
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
    iExists tid, ECn; iFrame "∗#%".
    iSplitL "Hr5" ; iExists _ ; iFrame.
  Qed.

  Lemma mutual_attestation_main_get_confirm_or_fail_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (r r' : RegName) (ot_w : OType) sb_w
    (w' w5 w6: LWord)
    (tid : TIndex) (ECn : nat) (expected_hash : Z)
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
      ∗ ⌜ 0 <= tid < ECn ⌝
      ∗ (
          □ ∀ (I : EIdentity) (tid : TIndex) (ot : OType) (ce : CustomEnclave),
            (⌜(0 <= tid < ECn)⌝) -∗
            enclave_all tid I
            ∗ ⌜ ma_enclaves_map !! I = Some ce ⌝
            ∗ ⌜ has_seal ot tid ⌝ -∗
            if (Z.even (finz.to_z ot))
            then (seal_pred ot (Penc ce) ∗ seal_pred (ot ^+ 1)%ot (Psign ce))
            else (seal_pred (ot ^+ (-1))%ot (Penc ce) ∗ seal_pred ot (Psign ce))
        )%I
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
    iIntros "(Hpsign & %Htid & #Hcemap & #Htid & #Hseal_valid & HPC & Hr & Hr' & Hr5 & Hr6 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    iDestruct ( regname_neq with "[$HPC] [$Hr]") as %HPCr.
    iDestruct ( regname_neq with "[$HPC] [$Hr']") as %HPCr'.
    iDestruct ( regname_neq with "[$Hr] [$Hr']") as %Hrr'.

    wp_instr.
    (* iMod (inv_acc with "Henclaves_inv") as "(Henclaves_inv_open & Hclose_inv)"; first solve_ndisj. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr Hr'") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds' Hregs'|]; cycle 1.
    {
      (* iMod ("Hclose_inv" with "Henclaves_inv_open") as "_". iModIntro. *)
      by wp_pure; wp_end; by iRight.
    }
    (* iDestruct "Henclaves_inv_open" as (ECn) "(HEC & #Hcemap)". *)
    (* iMod ("Hclose_inv" with "[HEC Hcemap]") as "_"; iModIntro. *)
    (* { iExists ECn. iFrame "HEC Hcemap". } *)
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
    { iApply "Hcemap"; iFrame "%#∗". }
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
  Qed.



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


  (* Definition mutual_attestationN : namespace := nroot .@ "mutual_attestation". *)
  (* Define all the invariants *)
  (* Linking table invariant *)
  (* Definition link_tableN := (mutual_attestationN.@"link_table"). *)
  Definition link_table_inv
    v_link
    assert_entry b_assert e_assert v_assert link_tableN :=
    na_inv logrel_nais link_tableN
         ((assert_entry, v_link) ↦ₐ LCap E b_assert e_assert b_assert v_assert)%I.

  (* Assert invariant *)
  (* Definition assertN := (mutual_attestationN.@"assert"). *)
  Definition assert_inv b_a a_flag e_a v_assert assertN :=
    na_inv logrel_nais assertN (assert_inv b_a a_flag e_a v_assert).

  (* Definition flag_assertN := (mutual_attestationN.@"flag_assert"). *)
  Definition flag_inv a_flag v_flag flag_assertN :=
    inv flag_assertN ((a_flag,v_flag) ↦ₐ LInt 0%Z).

  Lemma mutual_attest_callback_spec
    (E : coPset) (b_main pc_b pc_e : Addr) (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)

    (* (rmap : LReg) *)
    (w0 w1 w2 w3 w4 w5 w6 : LWord)
    (φ : val → iPropI Σ)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ mutual_attestation_main_len)%a in
    let a_callback := (b_main ^+ mutual_attestation_main_init_len)%a in
    let a_data := (b_main ^+ mutual_attestation_main_code_len)%a in

    let mutual_attestation_main := mutual_attestation_main_code assert_lt_offset in
    ContiguousRegion b_main mutual_attestation_main_len ->

    ↑link_tableN ⊆ E ->
    ↑assertN ⊆ E ->
    assertN ## link_tableN ->

    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->
    SubBounds pc_b pc_e b_main e_main ->
    pc_e = e_main ->

    (link_table_inv v_link assert_entry b_assert e_assert v_assert link_tableN
    ∗ assert_inv b_assert a_flag e_assert v_assert assertN
    ∗ flag_inv a_flag v_assert flag_assertN)
		∗ system_inv (enclaves_map := contract_ma_enclaves_map)
    ∗ interp w0
    ∗ interp w2
    ⊢ (
        codefrag b_main pc_v mutual_attestation_main
        ∗ (a_data, pc_v) ↦ₐ link_cap
        ∗ PC ↦ᵣ LCap RX pc_b pc_e a_callback pc_v
        ∗ r_t0 ↦ᵣ w0
        ∗ r_t1 ↦ᵣ w1
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        ∗ r_t4 ↦ᵣ w4
        ∗ r_t5 ↦ᵣ w5
        ∗ r_t6 ↦ᵣ w6
        ∗ na_own logrel_nais E
        ∗ ▷ ( ∀ w0' w1' w2' w3' w4' w5' w6',
                codefrag b_main pc_v mutual_attestation_main
                ∗ (a_data, pc_v) ↦ₐ link_cap
                ∗ PC ↦ᵣ LCap RX pc_b pc_e (e_main ^+ (-2))%a pc_v
                ∗ r_t0 ↦ᵣ w0'
                ∗ r_t1 ↦ᵣ w1'
                ∗ r_t2 ↦ᵣ w2'
                ∗ r_t3 ↦ᵣ w3'
                ∗ r_t4 ↦ᵣ w4'
                ∗ r_t5 ↦ᵣ w5'
                ∗ r_t6 ↦ᵣ w6'
                ∗ na_own logrel_nais E
                  -∗ WP (Instr Halted) {{ φ }}))
          -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /mutual_attestation_main_len in H
                  | H: SubBounds _ _ _ _  |- _ =>
                      rewrite /SubBounds /mutual_attestation_main_len in H
                end)
      ; rewrite !/mutual_attestation_main_code_len /mutual_attestation_main_len
          /mutual_attestation_main_init_len /mutual_attestation_main_callback_len
      ; solve_addr.

    intros ?????? Hregion HE HE' HE_disj Hassert Hlink Hpcbounds ->.
    iIntros "( #(HlinkInv & HassertInv & HflagInv) & #Hcemap_inv & #Hinterp_w0 & #Hinterp_w2)
             (Hcode & Hadata & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6 & Hna & Hφ)".
    codefrag_facts "Hcode".

    (* BLOCK 1: attest A *)
    subst mutual_attestation_main.
    rewrite /mutual_attestation_main_code.
    subst a_callback.
    replace mutual_attestation_main_init_len
      with (Z.of_nat (length mutual_attestation_main_code_init))
           by (by rewrite /mutual_attestation_main_init_len; cbn).
    rewrite /mutual_attestation_main_code_callback.

    focus_block 1%nat "Hcode" as a_block1 Ha_block1 "Hcode" "Hcode_cont".
    destruct (is_sealedL w0) eqn:Hw0; cycle 1.
    {
      iApply (mutual_attestation_main_attest_or_fail_spec with "[- $HPC $Hcode $Hr0 $Hr5 $Hr6 $Hcemap_inv]"); eauto.
      { solve_addr. }
      { solve_addr'. }
      iNext ; iIntros "H".
      iDestruct "H" as (tid ECn) "(%Hhas_seal & %Htid & #Hcemap & #Henclave_tid & HPC & Hr0 & Hr5 & Hr6 & Hcode)".
      iDestruct "Hr5" as (w5') "Hr5".
      iDestruct "Hr6" as (w6') "Hr6".
      unfocus_block "Hcode" "Hcode_cont" as "Hcode".
      focus_block 2 "Hcode" as a_block2 Ha_block2 "Hcode" "Hcode_cont".
      iApply (mutual_attestation_main_get_confirm_or_fail_spec'
              with "[- $HPC $Hr0 $Hr1 $Hcode]"); eauto; solve_addr'.
    }
    destruct w0 as [| | ot_w0 sb_w0]; cbn in Hw0; try congruence.
    iDestruct (interp_valid_sealed with "Hinterp_w0") as (Φ_A) "Hseal_valid_w0".
    iApply (mutual_attestation_main_attest_or_fail_spec
             with "[- $HPC $Hcode $Hr0 $Hr5 $Hr6 $Hcemap_inv]"); eauto.
    { solve_addr'. }
    { solve_addr'. }
    iNext ; iIntros "H".
    iDestruct "H" as (tid_A ECn_A) "(%Hhas_seal_A & %Htid_A & Hcemap_A & #Henclave_tid_A & HPC & Hr0 & Hr5 & Hr6 & Hcode)".
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 2: get confirm A *)
    focus_block 2 "Hcode" as a_block2 Ha_block2 "Hcode" "Hcode_cont".
    clear Ha_block1 a_block1.
    iApply ( (mutual_attestation_main_get_confirm_or_fail_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ mutual_attest_enclave_A_pred )
             with "[- $HPC $Hcode $Hr0 $Hr1 $Hr5 $Hr6 $Hseal_valid_w0 $Henclave_tid_A $Hcemap_A]"); eauto.
    { solve_addr'. }
    { solve_addr'. }
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
    iSplitR; first done.
    iNext.
    iIntros "(HPC & Hr0 & Hr1 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 3: attest B *)
    focus_block 3 "Hcode" as a_block3 Ha_block3 "Hcode" "Hcode_cont".
    clear Ha_block2 a_block2.
    destruct (is_sealedL w2) eqn:Hw2; cycle 1.
    {
      iApply (mutual_attestation_main_attest_or_fail_spec
               with "[- $HPC $Hcode $Hr2 $Hr5 $Hr6 $Hcemap_inv]"); eauto.
      { solve_addr'. }
      { solve_addr'. }
      iNext ; iIntros "H".
      iDestruct "H" as (tid_B ECn_B) "(%Hhas_seal_B & %Htid_B & #Hcemap_B & #Henclave_tid_B & HPC & Hr2 & Hr5 & Hr6 & Hcode)".
      clear w5' w6'.
      iDestruct "Hr5" as (w5') "Hr5".
      iDestruct "Hr6" as (w6') "Hr6".
      unfocus_block "Hcode" "Hcode_cont" as "Hcode".
      focus_block 4 "Hcode" as a_block4 Ha_block4 "Hcode" "Hcode_cont".
      iApply (mutual_attestation_main_get_confirm_or_fail_spec'
              with "[- $HPC $Hr2 $Hr3 $Hcode]"); eauto; solve_addr'.
    }
    destruct w2 as [| | ot_w2 sb_w2]; cbn in Hw2; try congruence.
    iDestruct (interp_valid_sealed with "Hinterp_w2") as (Φ_B) "Hseal_valid_w2".
    iApply (mutual_attestation_main_attest_or_fail_spec
             with "[- $HPC $Hcode $Hr2 $Hr5 $Hr6 $Hcemap_inv]"); eauto.
    { solve_addr'. }
    { solve_addr'. }
    iNext ; iIntros "H".
    iDestruct "H" as (tid_B ECn_B) "(%Hhas_seal_B & %Htid_B & #Hcemap_B & #Henclave_tid_B & HPC & Hr2 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 4: get confirm attest B *)
    focus_block 4 "Hcode" as a_block4 Ha_block4 "Hcode" "Hcode_cont".
    clear Ha_block3 a_block3.
    iApply ( (mutual_attestation_main_get_confirm_or_fail_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ mutual_attest_enclave_B_pred )
             with "[- $HPC $Hcode $Hr2 $Hr3 $Hr5 $Hr6 $Hseal_valid_w2 $Henclave_tid_B $Hcemap_B]"); eauto.
    { solve_addr'. }
    { solve_addr'. }
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
    iSplitR; first done.
    iNext.
    iIntros "(HPC & Hr2 & Hr3 & Hr5 & Hr6 & Hcode)".
    clear w5' w6'.
    iDestruct "Hr5" as (w5') "Hr5".
    iDestruct "Hr6" as (w6') "Hr6".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 5: prepare assert A *)
    focus_block 5 "Hcode" as a_block5 Ha_block5 "Hcode" "Hcode_cont".
    clear Ha_block4 a_block4.
    assert (SubBounds pc_b e_main a_block5 (a_block5 ^+ 11%nat)%a) by (subst; solve_addr').
    assert ( ((a_block5 ^+ 1)%a + (e_main - (a_block5 ^+ 1)))%a = Some e_main) as He_main by solve_addr.
    iGo "Hcode".
    { transitivity (Some (e_main ^+ -1)%a); solve_addr'. }
    replace ((b_main ^+ 73) ^+ -1)%a with a_data by solve_addr'.
    iInstr "Hcode".
    iGo "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 6: assert (confirm A) == 1 *)
    focus_block 6 "Hcode" as a_block6 Ha_block6 "Hcode" "Hcode_cont".
    clear He_main Ha_block5 a_block5.
    iMod (na_inv_acc with "HlinkInv Hna") as "(>Hassert_entry & Hna & Hclose)"; [ solve_ndisj.. |].
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try reflexivity.
    { solve_addr'. }
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr1 & Hr2 & Hr4 & Hr5 & Hcode & Hna & Hassert_entry)".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 7: prepare assert B *)
    focus_block 7 "Hcode" as a_block7 Ha_block7 "Hcode" "Hcode_cont".
    clear Ha_block6 a_block6.
    assert (SubBounds pc_b e_main a_block7 (a_block7 ^+ 2%nat)%a) by (subst; solve_addr').
    iInstr "Hcode".
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 8: assert (confirm B) == 1 *)
    focus_block 8 "Hcode" as a_block8 Ha_block8 "Hcode" "Hcode_cont".
    clear Ha_block7 a_block7.
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try reflexivity.
    { solve_addr'. }
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr3 & Hr2 & Hr4 & Hr5 & Hcode & Hna & Hassert_entry)".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    (* BLOCK 9: halt *)
    focus_block 9 "Hcode" as a_block9 Ha_block9 "Hcode" "Hcode_cont".
    clear Ha_block8 a_block8.
    assert (SubBounds pc_b e_main a_block9 (a_block9 ^+ 1%nat)%a) by (subst; solve_addr').
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcode_cont" as "Hcode".

    iMod ("Hclose" with "[$Hassert_entry $Hna]") as "Hna".
    replace a_block9 with (b_main ^+ 71%nat)%a by solve_addr'.
    replace (b_main ^+ 71%nat)%a with (e_main ^+ -2)%a by solve_addr'.

    iApply (wp_wand _ _ _ (fun v => φ v) (fun v => φ v ∨ ⌜v = FailedV⌝) with "[-]")%I; cycle 1.
    { iIntros (?) "?"; by iLeft. }
    iApply ("Hφ"); iFrame.
  Qed.

  Definition ma_main_inv b_main pc_v main_code a_data link_cap ma_mainN
    := na_inv logrel_nais ma_mainN
         (codefrag b_main pc_v main_code ∗ (a_data, pc_v) ↦ₐ link_cap).

  Lemma mutual_attest_main_code_callback_sentry
    (b_main : Addr) (pc_v : Version) (ma_mainN : namespace)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ mutual_attestation_main_len)%a in
    let a_callback := (b_main ^+ mutual_attestation_main_init_len)%a in
    let a_data := (b_main ^+ mutual_attestation_main_code_len)%a in

    let mutual_attestation_main := mutual_attestation_main_code assert_lt_offset in

    assertN ## link_tableN ->
    assertN ## ma_mainN ->
    link_tableN ## ma_mainN ->

    ContiguousRegion b_main mutual_attestation_main_len ->
    SubBounds b_main e_main b_main e_main ->

    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->
    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert link_tableN
     ∗ assert_inv b_assert a_flag e_assert v_assert assertN
     ∗ flag_inv a_flag v_assert flag_assertN
     ∗ ma_main_inv b_main pc_v mutual_attestation_main a_data link_cap ma_mainN
    )
    ∗ (system_inv (enclaves_map := contract_ma_enclaves_map))
    ⊢ interp (LCap E b_main e_main (b_main ^+ mutual_attestation_main_init_len)%a pc_v).
  Proof.
    intros ?????? HN HN' HN'' HcontRegion HsubBounds Hassert Hlink.
    iIntros "[#(HlinkInv & HassertInv & HflagInv & HcodeInv) #Hcemap_inv]".
    iEval (rewrite fixpoint_interp1_eq /=).
    iIntros (regs); iNext ; iModIntro.
    iIntros "( [%Hrmap_full #Hrmap_interp] & Hrmap & Hna)".
    rewrite /interp_conf.

    (* Prepare the necessary resources *)
    (* Registers *)
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    assert (exists w0, regs !! r_t0 = Some w0) as [w0 Hr0] by apply (Hrmap_full r_t0).
    assert (exists w1, regs !! r_t1 = Some w1) as [w1 Hr1] by apply (Hrmap_full r_t1).
    assert (exists w2, regs !! r_t2 = Some w2) as [w2 Hr2] by apply (Hrmap_full r_t2).
    assert (exists w3, regs !! r_t3 = Some w3) as [w3 Hr3] by apply (Hrmap_full r_t3).
    assert (exists w4, regs !! r_t4 = Some w4) as [w4 Hr4] by apply (Hrmap_full r_t4).
    assert (exists w5, regs !! r_t5 = Some w5) as [w5 Hr5] by apply (Hrmap_full r_t5).
    assert (exists w6, regs !! r_t6 = Some w6) as [w6 Hr6] by apply (Hrmap_full r_t6).

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


    iApply (wp_wand _ _ _
              ( fun v =>
                  ((⌜v = HaltedV⌝ →
                    ∃ lregs : LReg, full_map lregs
                                    ∧ registers_mapsto lregs
                                    ∗ na_own logrel_nais ⊤)
                   ∨ ⌜v = FailedV⌝
                  )%I)
             with "[-]"); cycle 1.
    { iEval (cbn). iIntros (v) "H ->".
      iDestruct "H" as "[H|%]"; last congruence.
      by iApply "H".
    }
    iMod (na_inv_acc with "HcodeInv Hna") as "[>(Hcode & Hdata) [Hna Hcls] ]"
    ;[solve_ndisj|solve_ndisj|].

    iApply ( (mutual_attest_callback_spec (⊤ ∖ ↑ma_mainN))
             with "[$HlinkInv $HassertInv $HflagInv $Hcemap_inv Hinterp_w0 Hinterp_w2]
                 [$HPC $Hcode $Hdata $Hna Hcls $Hr0 $Hr1 $Hr2 $Hr3 $Hr4 $Hr5 $Hr6 Hrmap]")
    ; eauto
    ; try solve_ndisj
    ; try iFrame "∗#".
    iNext; iIntros (???????) "(Hcode & Hadata & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6 & Hna)".
    iMod ("Hcls" with "[$Hcode $Hadata $Hna]") as "Hna".
    iDestruct (big_sepM_insert _ _ PC with "[$Hrmap $HPC]") as "Hrmap".
    { do 7 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 7 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
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
    | H: _ |- context [ <[r_t6:=?w6]> ?x ] =>
        set (rmap' := <[r_t6:=w6]> x )
    end.

    wp_end. iIntros (_).
    iExists rmap'; iFrame.
    iPureIntro.
    intros r; subst rmap'; cbn.
    destruct ((decide (r = r_t6))); simplify_map_eq; first done.
    destruct ((decide (r = r_t5))); simplify_map_eq; first done.
    destruct ((decide (r = r_t4))); simplify_map_eq; first done.
    destruct ((decide (r = r_t3))); simplify_map_eq; first done.
    destruct ((decide (r = r_t2))); simplify_map_eq; first done.
    destruct ((decide (r = r_t1))); simplify_map_eq; first done.
    destruct ((decide (r = r_t0))); simplify_map_eq; first done.
    destruct ((decide (r = PC))); simplify_map_eq; done.
  Qed.

  Lemma mutual_attestation_main_init_spec
    (b_main : Addr)
    (pc_v : Version)
    (assert_lt_offset : Z)
    (w1 wadv : LWord)
    φ :

    let e_main := (b_main ^+ mutual_attestation_main_len)%a in
    let a_callback := (b_main ^+ mutual_attestation_main_init_len)%a in
    let a_data := (b_main ^+ mutual_attestation_main_code_len)%a in

    let mutual_attestation_main := mutual_attestation_main_code assert_lt_offset in
    ContiguousRegion b_main mutual_attestation_main_len ->
    ⊢ ((
          codefrag b_main pc_v mutual_attestation_main

          ∗ PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
          ∗ r_t0 ↦ᵣ wadv
          ∗ r_t1 ↦ᵣ w1
          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag b_main pc_v mutual_attestation_main
                ∗ PC ↦ᵣ updatePcPermL wadv
                ∗ r_t0 ↦ᵣ wadv
                ∗ r_t1 ↦ᵣ (LCap E b_main e_main a_callback pc_v)
                  -∗ WP Seq (Instr Executable) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.

    (* We define a local version of solve_addr, which subst and unfold every computed addresses  *)
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /mutual_attestation_main_len in H
                end)
      ; rewrite !/mutual_attestation_main_code_len /mutual_attestation_main_len
          /mutual_attestation_main_init_len /mutual_attestation_main_callback_len
      ; solve_addr.

    intros ???? Hregion.
    iIntros "(Hcode & HPC & Hr0 & Hr1 & Hφ)".
    codefrag_facts "Hcode".
    iGo "Hcode".
    rewrite decode_encode_perm_inv; by cbn.
    rewrite decode_encode_perm_inv.
    iGo "Hcode".
    iApply "Hφ".
    iFrame.
  Qed.

  Lemma mutual_attest_full_run_spec
    (b_main : Addr) (pc_v : Version) (ma_mainN : namespace)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)

    (rmap : LReg)
    (wadv : LWord)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ mutual_attestation_main_len)%a in
    let a_callback := (b_main ^+ mutual_attestation_main_init_len)%a in
    let a_data := (b_main ^+ mutual_attestation_main_code_len)%a in

    let mutual_attestation_main := mutual_attestation_main_code assert_lt_offset in

    assertN ## link_tableN ->
    assertN ## ma_mainN ->
    link_tableN ## ma_mainN ->

    ContiguousRegion b_main mutual_attestation_main_len ->
    SubBounds b_main e_main b_main e_main ->

    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->

    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →

    (link_table_inv v_link assert_entry b_assert e_assert v_assert link_tableN
    ∗ assert_inv b_assert a_flag e_assert v_assert assertN
    ∗ flag_inv a_flag v_assert flag_assertN
    ∗ ma_main_inv b_main pc_v mutual_attestation_main a_data link_cap ma_mainN)
		∗ system_inv (enclaves_map := contract_ma_enclaves_map)
    ∗ interp wadv

    ⊢ ( PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
        ∗ r_t0 ↦ᵣ wadv
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_zL w = true⌝)
        ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable)
               {{λ v, (⌜v = HaltedV⌝ →
                       ∃ r : LReg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)%I
                      ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros ?????? ??? Hregion HsubBounds Hassert Hlink Hdom.
    iIntros "( #(HlinkInv & HassertInv & HflagInv & HcodeInv)  & #Hcemap_inv & #Hinterp_wadv)
             (HPC & Hr0 & Hrmap & Hna)".
    rewrite /registers_mapsto.
    (* Prepare the necessary resources *)
    (* Registers *)
    iDestruct (jmp_to_unknown wadv with "[] [$Hinterp_wadv]") as "Hjmp".
    { iSplit; last iFrame "Hcemap_inv".
      iModIntro.
      iApply custom_enclave_contract_inv.
      iApply mutual_attest_contract.
    }

    iMod (na_inv_acc with "HcodeInv Hna") as "[>(Hcode & Hdata) [Hna Hcls] ]"
    ;[solve_ndisj|solve_ndisj|].
    codefrag_facts "Hcode".
    iExtract "Hrmap" r_t1 as "[Hr1 _]".
    iApply (mutual_attestation_main_init_spec with "[-]"); eauto; iFrame.
    iNext; iIntros "(Hcode & HPC & Hr0 & Hr1)".
    iMod ("Hcls" with "[$Hcode $Hdata $Hna]") as "Hna".

    set (rmap' := delete r_t1 rmap).
    (* Show that the contents of unused registers is safe *)
    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn.
      iIntros "[Hr %Hw]". iFrame.
      destruct_word w; try by inversion Hw. rewrite fixpoint_interp1_eq //.
    }

    iDestruct (mutual_attest_main_code_callback_sentry
                with "[$HlinkInv $HassertInv $HflagInv $HcodeInv $Hcemap_inv]")
      as "#Hinterp_wret"; eauto.

    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1 $Hinterp_wret]") as "Hrmap"
    ; first (apply lookup_delete_None ; left ; done).
    rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0 $Hinterp_wadv]") as "Hrmap"
    ; first (rewrite lookup_insert_ne //=; apply not_elem_of_dom_1; rewrite Hdom; set_solver).

    iApply (wp_wand with "[-]").
    - iApply ("Hjmp" with "[] [$HPC $Hrmap $Hna]") ;eauto.
      iPureIntro; rewrite !dom_insert_L Hdom; set_solver.
    - iIntros (v) "H"; by iLeft.
 Qed.

End mutual_attest_main.
