From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import mutual_attestation_code.
From cap_machine Require Import
  mutual_attestation_code
  (* mutual_attestation_A_spec *)
  (* mutual_attestation_B_spec *)
.


Section mutual_attest_main.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.


  (* -------------------------------------------------- *)
  (* ------------------- ENCLAVES --------------------- *)
  (* -------------------------------------------------- *)

  (* Lemma mutual_attest_contract : *)
  (*   custom_enclave_contract ma_enclaves_map. *)
  (* Proof. *)
  (*   rewrite /custom_enclave_contract. *)
  (*   iIntros (I b e a v b' e' a' v' enclave_data ot ce *)
  (*     Hwf_cemap Hcode_ce Hot Hb' HIhash Hb He) *)
  (*     "(#Henclaves_inv & #Hma_inv & #HPenc & #HPsign)". *)
  (*   clear HIhash. *)
  (*   clear Hwf_cemap. *)
  (*   assert (e = (b ^+ (length (code ce) + 1))%a) as -> by solve_addr+He. *)

  (*   rewrite /ma_enclaves_map in Hcode_ce. *)
  (*   simplify_map_eq. *)

  (*   assert (I = hash_mutual_attest_A \/ I = hash_mutual_attest_B) as HI. *)
  (*   { rewrite lookup_insert_Some in Hcode_ce. *)
  (*     destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto. *)
  (*     rewrite lookup_insert_Some in Hcode_ce. *)
  (*     destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto. *)
  (*     done. *)
  (*   } *)
  (*   destruct HI ; simplify_map_eq. *)
  (*   - iApply ( mutual_attest_A_contract with "[]") ; last iFrame "#"; eauto. *)
  (*   - rewrite lookup_insert_ne // in Hcode_ce. *)
  (*     2:{ rewrite /hash_mutual_attest_A /hash_mutual_attest_B. *)
  (*         intro Hcontra. *)
  (*         apply hash_concat_inj' in Hcontra. *)
  (*         destruct Hcontra as [_ Hcontra]. *)
  (*         rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra. *)
  (*         by injection Hcontra. *)
  (*     } *)
  (*     simplify_map_eq. *)
  (*     iApply ( mutual_attest_B_contract with "[]") ; last iFrame "#"; eauto. *)
  (* Admitted. *)

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
    let pc_a' := (pc_a ^+ (length code + 1))%a in
    (pc_a + (length code + 1))%a = Some pc_a' ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ (length code))%a ->

    ( PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v
      ∗ r ↦ᵣ w ∗ r_t5 ↦ᵣ w5 ∗ r_t6 ↦ᵣ w6
      ∗ codefrag pc_a pc_v code
      ∗ ▷ ( (∃ tid, ⌜ has_seal otype_w tid ⌝ ∗ enclave_all tid expected_hash
            ∗ PC ↦ᵣ LCap RX pc_b pc_e pc_a' pc_v
            ∗ r ↦ᵣ w ∗ (∃ w5', r_t5 ↦ᵣ w5') ∗ (∃ w6', r_t6 ↦ᵣ w6')
            ∗ codefrag pc_a pc_v code)
            -∗ WP Seq (Instr Executable) {{ v, ⌜ v = FailedV ⌝ ∨ φ v }}
      )
    )
   ⊢ WP Seq (Instr Executable) {{ v, ⌜ v = FailedV ⌝ ∨ φ v }}.
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
    2:{ wp_end; by iLeft. }
    (* iDestruct (interp_valid_sealed with "Hinterp_w1") as (Φ) "Hseal_valid". *)

    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    destruct (decide (I = expected_hash)) as [-> | HnI]
    ; cycle 1.
    { (* Not the right enclave *)
      iInstr "Hcode". (* Jnz *)
      by (injection; intro Hcontra; lia).
      iInstr "Hcode". (* Fail *)
      wp_end; by iLeft.
    }
    replace ( _ - _)%Z with 0%Z by lia.
    iInstr "Hcode".
    iInstr "Hcode".
    { transitivity (Some (pc_a')); subst pc_a' ; solve_addr. }
    iInstr "Hcode".
    iApply "Hφ".
    replace (pc_a ^+ (9%nat + 1))%a with pc_a' by (subst pc_a' ; solve_addr).
    iExists tid; iFrame "∗#%".
    iSplitL "Hr5" ; iExists _ ; iFrame.
  Qed.

  Lemma mutual_attestation_main_get_confirm_or_fail_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (r r' : RegName) (w w' w5 w6: LWord)
    φ :
    let code := mutual_attestation_main_get_confirm_or_fail r r' in
    let pc_a' := (pc_a ^+ (length code))%a in
    (pc_a + (length code))%a = Some pc_a' ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ (length code))%a ->

    ( PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v
      ∗ r ↦ᵣ w ∗ r' ↦ᵣ w' ∗ r_t5 ↦ᵣ w5 ∗ r_t6 ↦ᵣ w6
      ∗ codefrag pc_a pc_v code
      ∗ ▷ ( (PC ↦ᵣ LCap RX pc_b pc_e pc_a' pc_v
            ∗ r ↦ᵣ w ∗ r' ↦ᵣ w' ∗ (∃ w5', r_t5 ↦ᵣ w5') ∗ (∃ w6', r_t6 ↦ᵣ w6')
            ∗ codefrag pc_a pc_v code)
            -∗ WP Seq (Instr Executable) {{ v, ⌜ v = FailedV ⌝ ∨ φ v }}
      )
    )
   ⊢ WP Seq (Instr Executable) {{ v, ⌜ v = FailedV ⌝ ∨ φ v }}.
  Proof.
    intros code pc_a' Hpc_a' Hbounds; subst code.
    iIntros "(HPC & Hr & Hr' & Hr5 & Hr6 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    iAssert (⌜ PC ≠ r ⌝)%I as %HPCr. admit.
    iAssert (⌜ PC ≠ r' ⌝)%I as %HPCr'. admit.
    iAssert (⌜ r ≠ r' ⌝)%I as %Hrr'. admit.

    wp_instr.
    (* iMod (inv_acc with "Henclaves_inv") as "(Henclaves_inv_open & Hclose_inv)"; first solve_ndisj. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr Hr'") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds' Hregs'|]; cycle 1.
    { (* iMod ("Hclose_inv" with "Henclaves_inv_open") as "_". iModIntro. *)
      by wp_pure; wp_end; by iLeft.
    }
    (* iDestruct "Henclaves_inv_open" as (ECn) "(HEC & #Hcemap)". *)
    (* iMod ("Hclose_inv" with "[HEC Hcemap]") as "_"; iModIntro. *)
    (* { iExists ECn. iFrame "HEC Hcemap". } *)
    (* Opaque mutual_attest_enclave_B_code_pre encodeInstrsLW. *)
    incrementLPC_inv as (p''&pc_b'&pc_e'&pc_a''&pc_v'& ? & HPC & Z & Hregs');
      simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    (* repeat (rewrite insert_commute //= insert_insert) in H1. *)
    (* Transparent mutual_attest_enclave_B_code_pre encodeInstrsLW. *)
    replace x with (pc_a'' ^+ 1)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr Hr'] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hcode".




End mutual_attest_main.
