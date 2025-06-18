From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import assert macros_new.
From cap_machine Require Import
  trusted_memory_readout_code
  trusted_memory_readout_enclaves_spec
  trusted_memory_readout_main_spec
.

Section trusted_memory_readout_full_run.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {oneshotg : one_shotG Σ} {nainv: logrel_na_invs Σ}
    {reservedaddresses : ReservedAddresses}
    `{MP: MachineParameters}.
  Context {CS: ClientSensor}.

  Lemma trusted_memory_readout_full_run_spec
    (b_main : Addr) (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (link_tableN : namespace) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (assertN flag_assertN : namespace) (* assert *)

    (rmap : LReg)
    (wadv : LWord)
    :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ trusted_memory_readout_main_len)%a in
    let a_callback := (b_main ^+ trusted_memory_readout_main_init_len)%a in
    let a_data := (b_main ^+ trusted_memory_readout_main_code_len)%a in

    let trusted_memory_readout_main := trusted_memory_readout_main_code assert_lt_offset in

    assertN ## link_tableN ->
    assertN ## ts_mainN ->
    link_tableN ## ts_mainN ->

    ContiguousRegion b_main trusted_memory_readout_main_len ->
    SubBounds b_main (b_main ^+ trusted_memory_readout_main_len)%a b_main
      (b_main ^+ trusted_memory_readout_main_len)%a ->


    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->

    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →

    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert link_tableN
    ∗ assert_inv b_assert a_flag e_assert v_assert assertN
    ∗ flag_inv a_flag v_assert flag_assertN
    ∗ ts_main_inv b_main e_main pc_v (trusted_memory_readout_main_code assert_lt_offset) a_data link_cap ts_mainN
    )
    ∗ (system_inv (enclaves_map := contract_ts_enclaves_map))
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
      iApply enclaves_contract.
    }
    iMod (na_inv_acc with "HcodeInv Hna") as "[>(Hcode & Hadata & Hadata') [Hna Hcls] ]"
    ;[solve_ndisj|solve_ndisj|].

    iExtract "Hrmap" r_t1 as "[Hr1 _]".
    iApply (trusted_memory_readout_main_init_spec with "[-]"); eauto; iFrame.
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
    iDestruct (trusted_memory_readout_callback_code_sentry
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

End trusted_memory_readout_full_run.
