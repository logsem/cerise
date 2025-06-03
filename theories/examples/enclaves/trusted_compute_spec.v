From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import assert macros_new.
From cap_machine Require Import
  trusted_compute_code
  trusted_compute_enclave_spec
.

Section trusted_compute_main.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.
  Context {TC: TrustedCompute}.

  (* ---------------------------------- *)
  (* ----- TRUSTED COMPUTE *MAIN* ----- *)
  (* ---------------------------------- *)

  (* Expect:
     - PC := (RWX, main, main_end, main)
     - R0 := (RWX, adv, adv_end, adv)
   *)

  (** Specification init code *)
  Lemma trusted_compute_main_init_spec
    (b_main : Addr)
    (pc_v : Version)
    (assert_lt_offset : Z)
    (w1 wadv : LWord)
    φ :

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    ContiguousRegion b_main trusted_compute_main_len ->
    ⊢ ((
          codefrag b_main pc_v trusted_compute_main

          ∗ PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
          ∗ r_t0 ↦ᵣ wadv
          ∗ r_t1 ↦ᵣ w1
          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag b_main pc_v trusted_compute_main
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
                      rewrite /ContiguousRegion /trusted_compute_main_len in H
                end)
      ; rewrite !/trusted_compute_main_code_len /trusted_compute_main_len
          /trusted_compute_main_init_len /trusted_compute_main_callback_len
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

  (** Specification callback code *)

  (* Define all the invariants *)
  (* Linking table invariant *)
  Definition link_table_inv
    v_link
    assert_entry b_assert e_assert v_assert link_tableN :=
    na_inv logrel_nais link_tableN
         ((assert_entry, v_link) ↦ₐ LCap E b_assert e_assert b_assert v_assert)%I.

  (* Assert invariants *)
  Definition assert_inv b_a a_flag e_a v_assert assertN :=
    na_inv logrel_nais assertN (assert_inv b_a a_flag e_a v_assert).
  Definition flag_inv a_flag v_flag flag_assertN :=
    inv flag_assertN ((a_flag,v_flag) ↦ₐ LInt 0%Z).


  Lemma trusted_compute_callback_code_spec
    (E : coPset) (assertN flag_assertN link_tableN : namespace)
    (b_main pc_b pc_e : Addr)
    (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (* assert *)
    (w0 w1 w2 w3 w4 w5 : LWord)
    φ :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    ContiguousRegion b_main trusted_compute_main_len ->

    ↑link_tableN ⊆ E ->
    ↑assertN ⊆ E ->
    assertN ## link_tableN ->

    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->
    SubBounds pc_b pc_e b_main e_main ->

    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert link_tableN
    ∗ assert_inv b_assert a_flag e_assert v_assert assertN
    ∗ flag_inv a_flag v_assert flag_assertN)
    ∗ system_inv (enclaves_map := contract_tc_enclaves_map)
    ∗ interp w1
    ∗ interp w0

    ⊢ (( codefrag b_main pc_v trusted_compute_main
          ∗ ((a_data)%a, pc_v) ↦ₐ link_cap
          ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LCap RWX b_main e_main a_data pc_v)
          ∗ PC ↦ᵣ LCap RX pc_b pc_e a_callback pc_v
          ∗ r_t0 ↦ᵣ w0
          ∗ r_t1 ↦ᵣ w1
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          ∗ r_t4 ↦ᵣ w4
          ∗ r_t5 ↦ᵣ w5
          ∗ na_own logrel_nais E

          ∗ ▷ ( codefrag b_main pc_v trusted_compute_main
                ∗ ((a_data)%a, pc_v) ↦ₐ link_cap
                ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LCap RWX b_main e_main a_data pc_v)

                ∗ PC ↦ᵣ LCap RX pc_b pc_e (a_data ^+ (-2))%a pc_v
                ∗ r_t0 ↦ᵣ LInt 0
                ∗ r_t1 ↦ᵣ LInt 0
                ∗ r_t2 ↦ᵣ LInt 0
                ∗ r_t3 ↦ᵣ LInt 0
                ∗ r_t4 ↦ᵣ LInt 0
                ∗ r_t5 ↦ᵣ LInt 0
                ∗ na_own logrel_nais E

                  -∗ WP (Instr Halted) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.

    (* We define a local version of solve_addr, which subst and unfold every computed addresses  *)
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /trusted_compute_main_len in H
                end)
      ; rewrite !/trusted_compute_main_code_len /trusted_compute_main_len
          /trusted_compute_main_init_len /trusted_compute_main_callback_len
      ; solve_addr.

    intros ?????? Hregion HE HE' HE_disj Hassert Hlink Hpcbounds.

    iIntros "#[ [HlinkInv [HassertInv HflagInv] ] [ Hcemap_inv [ Hinterp_w1 Hinterp_w0]] ]
             (Hcode & Hlink_cap & Hdata1 & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hna & Hcont)".
    codefrag_facts "Hcode".

    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)

    destruct (is_sealedL w0) eqn:Hsealed_w0 ; cycle 1.
    { (* w0 is not a sealed  *)
      destruct_lword (w0) ; cbn in Hsealed_w0 ; try done.
      all: iInstr "Hcode". (* GetOType *)
      all: iInstr "Hcode". (* Sub *)
      all: replace (-1 - -1) with 0 by lia.
      all: iInstr "Hcode". (* Mov *)
      all: iInstr "Hcode". (* Lea *)
      all: iInstr "Hcode". (* Jnz *)
      all: iInstr "Hcode". (* Jmp *)
      all: iInstr "Hcode". (* Fail *)
      all: by (wp_end; iRight).
    }

    destruct w0 as [ ? | ? | o sw0 ]
    ; cbn in Hsealed_w0 ; try done; clear Hsealed_w0.

    iInstr "Hcode". (* GetOType *)
    iInstr "Hcode". (* Sub *)
    replace (o - -1) with (o + 1) by lia.
    assert (Ho : LInt (o + 1) ≠ LInt 0) by (clear ; intro ; inversion H ; solve_finz).
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)
    iInstr "Hcode". (* Jnz *)
    iInstr "Hcode". (* GetOType *)

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hcemap_inv") as "(Hcemap & Hclose)"; first solve_ndisj.
    iDestruct "Hcemap" as (ECn OTn) "(>HEC & ECn_OTn & Hallocated_seals & Hfree_seals & #Hcemap)".

    iApply (wp_estoreid_success_unknown_ec with "[HPC Hr2 Hr4 Hi $HEC]"); try iFrame; try solve_pure.
    iNext.
    iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr2 & HEC & [(-> & HPC & H)|(-> & HPC & Hr4)])".
    1: iDestruct "H" as (I tid) "(Hr4 & #Htc_env & [%Hseal %Htidx])".
    all: iMod ("Hclose" with "[HEC ECn_OTn Hallocated_seals Hfree_seals Hcemap]") as "_"
    ; [ iExists ECn, OTn; iFrame "HEC Hcemap ECn_OTn Hallocated_seals Hfree_seals"; eauto | iModIntro].
    all: wp_pure; iInstr_close "Hcode".
    2:{ wp_end; by iRight. }

    iInstr "Hcode". (* Sub *)
    destruct (decide (I = hash_trusted_compute_enclave)) as [-> | HnI]
    ; cycle 1.
    { (* Not the right enclave *)
      iInstr "Hcode". (* Jnz *)
      by (injection; intro Hcontra; lia).
      iInstr "Hcode". (* Fail *)
      wp_end; by iRight.
    }
    replace ( _ - _) with 0 by lia.
    iInstr "Hcode". (* Jnz *)
    iDestruct (interp_valid_sealed with "Hinterp_w0") as (Φ) "Hseal_valid".
    rewrite /system_inv.


    (* UnSeal *)
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr0") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap Hi]"); eauto; simplify_map_eq; eauto;
    try solve_pure.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds Hregs'|]; cycle 1.
    { by wp_pure; wp_end; iRight. }

    incrementLPC_inv as (p''&b_main'&e_main'&a_main'&pc_v'& ? & HPC & Z & Hregs'); simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    replace x with (b_main ^+ 18)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr0] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hcode".

    iAssert (
        if Z.even a
        then seal_pred a (Penc tc_enclave_pred)
             ∗ seal_pred (a ^+ 1)%f (Psign tc_enclave_pred)
        else seal_pred (a ^+ -1)%f (Penc tc_enclave_pred)
             ∗ seal_pred a (Psign tc_enclave_pred)
      )%I as "Htc".
    {
      iApply "Hcemap"; iFrame "%#∗".
      iPureIntro. rewrite /tcenclaves_map.
      by simplify_map_eq.
    }

    destruct (Z.even (finz.to_z a)) eqn:HEven_a
    ; iDestruct "Htc" as "[Htc_Penc Htc_Psign]"
    ; iEval (cbn) in "Htc_Penc"
    ; iEval (cbn) in "Htc_Psign".
    {
      iDestruct (seal_pred_valid_sealed_eq with "[$Htc_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }

    iDestruct (seal_pred_valid_sealed_eq with "[$Htc_Psign] Hseal_valid") as "Heqv".
    iAssert (▷ sealed_42 (LWSealable sb))%I as (fb fe fv) ">%Hseal42".
    { iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      iRewrite "Heqv".
      iFrame "HΦ". }
    destruct sb ; simplify_eq.
    iClear "Heqv Htc_Penc Hcemap Hcemap_inv".

    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* GetA *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)
    iInstr "Hcode". (* Load *)

    subst trusted_compute_main.
    rewrite /trusted_compute_main_code /trusted_compute_main_code_callback0.
    subst a_callback.
    rewrite /trusted_compute_main_init_len.

    subst e_main.
    focus_block 2%nat "Hcode" as addr_block2 Haddr_block2 "Hblock" "Hcode'".
    cbn in Haddr_block2.
    iMod (na_inv_acc with "HlinkInv Hna") as "(>Hassert_entry & Hna & Hclose)"; [ solve_ndisj.. |].
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try reflexivity.
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr1 & Hr2 & Hr4 & Hr5 & Hblock & Hna & Hassert_entry)".
    iMod ("Hclose" with "[$Hna $Hassert_entry]") as "Hna".
    iAssert (codefrag addr_block2 pc_v' (assert_reg_instrs assert_lt_offset r_t1)) with "[$Hblock]" as "Hblock".
    unfocus_block "Hblock" "Hcode'" as "Hcode".

    focus_block 3%nat "Hcode" as addr_block3 Haddr_block3 "Hblock" "Hcode'".
    iInstr "Hblock".
    iInstr "Hblock".
    iInstr "Hblock".
    unfocus_block "Hblock" "Hcode'" as "Hcode".
    replace (addr_block3 ^+ 2)%a with (a_data ^+ -2)%a by solve_addr'.

    iApply (wp_wand with "[-]") ; [  | iIntros (?) "H"; iLeft ; iApply "H"].
    iApply "Hcont"; iFrame.
  Qed.

  Definition tc_main_inv b_main e_main pc_v main_code a_data link_cap tc_mainN
    := na_inv logrel_nais tc_mainN
         (codefrag b_main pc_v main_code
          ∗ (a_data, pc_v) ↦ₐ link_cap
          ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ LCap RWX b_main e_main a_data pc_v).

  Lemma trusted_compute_callback_code_sentry
    (b_main : Addr) (pc_v : Version) (tc_mainN : namespace)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in

    assertN ## link_tableN ->
    assertN ## tc_mainN ->
    link_tableN ## tc_mainN ->

    ContiguousRegion b_main trusted_compute_main_len ->
    SubBounds b_main (b_main ^+ trusted_compute_main_len)%a b_main
      (b_main ^+ trusted_compute_main_len)%a ->

    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->
    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert link_tableN
     ∗ assert_inv b_assert a_flag e_assert v_assert assertN
     ∗ flag_inv a_flag v_assert flag_assertN
     ∗ tc_main_inv b_main e_main pc_v (trusted_compute_main_code assert_lt_offset) a_data link_cap tc_mainN
    )
    ∗ (system_inv (enclaves_map := contract_tc_enclaves_map))
    ⊢ interp (LCap E b_main (b_main ^+ trusted_compute_main_len)%a
                (b_main ^+ trusted_compute_main_init_len)%a pc_v).
  Proof.
    intros ????????? HcontRegion HsubBounds Hassert Hlink.
    iIntros "[#(HlinkInv & HassertInv & HflagInv & HcodeInv) #Hcemap_inv]".
    iEval (rewrite fixpoint_interp1_eq /=).
    iIntros (regs); iNext ; iModIntro.
    iIntros "( [%Hrmap_full #Hrmap_interp] & Hrmap & Hna)".
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    cbn in Hrmap_full.
    destruct (Hrmap_full r_t0) as [w0 Hr0].
    destruct (Hrmap_full r_t1) as [w1 Hr1].
    destruct (Hrmap_full r_t2) as [w2 Hr2].
    destruct (Hrmap_full r_t3) as [w3 Hr3].
    destruct (Hrmap_full r_t4) as [w4 Hr4].
    destruct (Hrmap_full r_t5) as [w5 Hr5].
    iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5]
      as ["Hr0";"Hr1";"Hr2";"Hr3";"Hr4";"Hr5"].

    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hrmap_interp";eauto;done. }
    iAssert (interp w1) as "Hinterp_w1".
    { iApply "Hrmap_interp";eauto;done. }


    rewrite /interp_conf.
    iApply (wp_wand _ _ _
              ( fun v =>
                  ((⌜v = HaltedV⌝ →
                    ∃ lregs : LReg, full_map lregs
                                    ∧ registers_mapsto lregs
                                    ∗ na_own logrel_nais ⊤)
                   ∨ ⌜v = FailedV⌝
                  )%I)
             with "[-]").

    - iMod (na_inv_acc with "HcodeInv Hna") as "[>(Hcode & Hdata & Hdata') [Hna Hcls] ]"
      ;[solve_ndisj|solve_ndisj|].

      iApply ( (trusted_compute_callback_code_spec (⊤ ∖ ↑tc_mainN))
               with "[$HlinkInv $HassertInv $HflagInv $Hcemap_inv Hinterp_w0 Hinterp_w1]
                 [$HPC $Hr0 $Hr1 $Hr2 $Hr3 $Hr4 $Hr5 $Hcode $Hdata $Hdata' $Hna Hcls Hrmap]")
      ; eauto
      ; try solve_ndisj
      ; try iFrame "∗#".
      iNext; iIntros "(Hcode & Hadata & Hadata' & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hna)".
      iMod ("Hcls" with "[$Hcode $Hadata $Hadata' $Hna]") as "Hna".
      wp_end. iIntros (_).
      iDestruct (big_sepM_insert _ _ r_t5 with "[$Hrmap $Hr5]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ r_t4 with "[$Hrmap $Hr4]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ r_t3 with "[$Hrmap $Hr3]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iDestruct (big_sepM_insert _ _ PC with "[$Hrmap $HPC]") as "Hrmap"
      ; first (by rewrite lookup_delete).
      rewrite insert_delete_insert; repeat (rewrite -delete_insert_ne //=).
      iExists _.
      iFrame "∗".


      iPureIntro; intros r; cbn.
      destruct (decide (r=PC)); simplify_map_eq;first done.
      destruct (decide (r=r_t5)); simplify_map_eq;first done.
      destruct (decide (r=r_t4)); simplify_map_eq;first done.
      destruct (decide (r=r_t3)); simplify_map_eq;first done.
      destruct (decide (r=r_t2)); simplify_map_eq;first done.
      destruct (decide (r=r_t1)); simplify_map_eq;first done.
      destruct (decide (r=r_t0)); simplify_map_eq;first done.
      apply Hrmap_full.
    - iEval (cbn). iIntros (v) "H ->".
      iDestruct "H" as "[H|%]"; last congruence.
      by iApply "H".
  Qed.

  Lemma trusted_compute_full_run_spec
    (b_main : Addr) (pc_v : Version) (tc_mainN : namespace)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)

    (rmap : LReg)
    (wadv : LWord)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in

    assertN ## link_tableN ->
    assertN ## tc_mainN ->
    link_tableN ## tc_mainN ->

    ContiguousRegion b_main trusted_compute_main_len ->
    SubBounds b_main (b_main ^+ trusted_compute_main_len)%a b_main
      (b_main ^+ trusted_compute_main_len)%a ->


    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->

    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →

    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert link_tableN
    ∗ assert_inv b_assert a_flag e_assert v_assert assertN
    ∗ flag_inv a_flag v_assert flag_assertN
    ∗ tc_main_inv b_main e_main pc_v (trusted_compute_main_code assert_lt_offset) a_data link_cap tc_mainN
    )
    ∗ (system_inv (enclaves_map := contract_tc_enclaves_map))
    ∗ interp wadv

    ⊢ (PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
          ∗ r_t0 ↦ᵣ wadv
          ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_zL w = true⌝)
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{λ v,
                  (⌜v = HaltedV⌝ → ∃ r : LReg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)%I
                  ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros ????????? Hregion HsubBounds Hassert Hlink Hrmap.

    iIntros "[  #(HlinkInv & HassertInv & HflagInv & HcodeInv) #[ Hcemap_inv Hinterp_wadv ] ]
             (HPC & Hr0 & Hrmap & Hna)".

    iDestruct (jmp_to_unknown wadv with "[] [$Hinterp_wadv]") as "Hjmp".
    { iSplit; last iFrame "Hcemap_inv".
      iModIntro.
      iApply custom_enclave_contract_inv.
      iApply tc_enclave_contract.
    }
    iMod (na_inv_acc with "HcodeInv Hna") as "[>(Hcode & Hadata & Hadata') [Hna Hcls] ]"
    ;[solve_ndisj|solve_ndisj|].

    iExtract "Hrmap" r_t1 as "[Hr1 _]".
    iApply (trusted_compute_main_init_spec with "[-]"); eauto; iFrame.
    iNext; iIntros "(Hcode & HPC & Hr0 & Hr1)".
    iMod ("Hcls" with "[$Hcode $Hadata $Hadata' $Hna]") as "Hna".

    set (rmap' := delete r_t1 rmap).
    (* Show that the contents of unused registers is safe *)
    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn.
      iIntros "[Hr %Hw]". iFrame.
      destruct_word w; try by inversion Hw. rewrite fixpoint_interp1_eq //.
    }

    (* Show the content of r1 is safe *)
    iDestruct (trusted_compute_callback_code_sentry
                with "[$HlinkInv $HassertInv $HflagInv $HcodeInv $Hcemap_inv]")
      as "Hinterp_wret"; eauto.
    (* Cannot use iInsert, because Qed is too long *)
    subst rmap'.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1 $Hinterp_wret]") as "Hrmap"
    ; first (apply lookup_delete_None ; left ; done).
    rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0 $Hinterp_wadv]") as "Hrmap"
    ; first (rewrite lookup_insert_ne //=; apply not_elem_of_dom_1; rewrite Hrmap; set_solver).

    (* Apply the result of the FTLR *)
    iApply (wp_wand with "[-]").
    - iApply ("Hjmp" with "[] [$HPC $Hrmap $Hna]") ;eauto.
      iPureIntro; rewrite !dom_insert_L Hrmap; set_solver.
    - iIntros (v) "H"; by iLeft.
  Qed.

End trusted_compute_main.
