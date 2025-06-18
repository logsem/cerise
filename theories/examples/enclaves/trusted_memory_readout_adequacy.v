From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import assert macros_new.
From cap_machine Require Import template_adequacy_attestation.
From cap_machine Require Import
  trusted_memory_readout_code
  trusted_memory_readout_enclaves_spec
  trusted_memory_readout_main_spec
  trusted_memory_readout_spec
.

(** MEMORY LAYOUT: The end-to-end theorem only relies on this layout. *)
Class memory_layout `{MachineParameters} := {
  (* Verifier code *)
  verifier_start : Addr;
  verifier_end : Addr;
  verifier_size: (verifier_start + trusted_memory_readout_main_len = Some verifier_end)%a;
  verifier_region: list Addr;
  verifier_region_correct:
    verifier_region = (finz.seq_between verifier_start verifier_end);

  (* Adversary code *)
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;
  adv_region: list Addr;
  adv_region_correct:
    adv_region = (finz.seq_between adv_start adv_end);

  (* Assert routine *)
  l_assert_start : Addr;
  l_assert_cap : Addr;
  l_assert_flag : Addr;
  l_assert_end : Addr;

  l_assert_code_size :
    (l_assert_start + length assert_subroutine_instrs)%a = Some l_assert_cap;
  l_assert_cap_size :
    (l_assert_cap + 1)%a = Some l_assert_flag;
  l_assert_flag_size :
    (l_assert_flag + 1)%a = Some l_assert_end;
  l_assert_region: list Addr;
  l_assert_region_correct:
    l_assert_region = (finz.seq_between l_assert_start l_assert_end);

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 1)%a = Some link_table_end;
  link_table_region: list Addr;
  link_table_region_correct:
    link_table_region = (finz.seq_between l_assert_start l_assert_end);

  regions_disjoints :
  verifier_region ## adv_region ∧
  verifier_region ## l_assert_region ∧
  verifier_region ## link_table_region ∧
  adv_region ## l_assert_region ∧
  adv_region ## link_table_region ∧
  l_assert_region ## link_table_region;

  (* TS sensor enclave *)
  ts_sensor_enclave_start : Addr;

  (* TS client enclave *)
  ts_client_enclave_start : Addr;
}.

Definition link_cap `{memory_layout} :=
 WCap RO link_table_start link_table_end link_table_start.

(** Instantiation of the layout. *)

(** 1) Instantiate the class specific to the TC enclave *)
Local Instance trusted_memory_readout_concrete `{memory_layout} : ClientSensor.
Proof. apply (Build_ClientSensor ts_sensor_enclave_start ts_client_enclave_start ts_client_enclave_start ). Defined.

(** 2) Instantiate the verifier's program.
    It is given by the code in `trusted_memory_readout_main_code`
    followed by the link capability and a data capability.
 *)
Program Definition ts_verifier_prog `{memory_layout} : prog :=
  let a_data := (verifier_start ^+ trusted_memory_readout_main_code_len)%a in
  let data_cap := WCap RWX verifier_start verifier_end a_data  in
  {| prog_start := verifier_start ;
     prog_end := verifier_end ;
     prog_instrs :=
      (lword_get_word <$> (trusted_memory_readout_main_code 0))
       ++ [link_cap ; data_cap];
     prog_size := _ |}.
Next Obligation.
  intros MP ML *.
  rewrite -verifier_size.
  rewrite app_length.
  rewrite fmap_length.
  by cbn.
Qed.

(** 3) Instantiate the adversary's program.
    It is arbitrary.
 *)
Definition adv_prog `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.

(** 4) Instantiate the assert library. *)
Program Definition AssertLib `{memory_layout} : assert_library :=
  {|
     assert_start := l_assert_start;
     assert_cap := l_assert_cap;
     assert_flag := l_assert_flag;
     assert_end := l_assert_end;

     assert_code_size := l_assert_code_size;
     assert_cap_size := l_assert_cap_size;
     assert_flag_size := l_assert_flag_size;
  |}.

Lemma adv_not_reserved `{memory_layout} (vinit : Version) :
  let RA := reserved_addresses_assert AssertLib vinit in
  adv_region  ## reserved_addresses.
Proof.
  intros.
  cbn.
  pose proof regions_disjoints as (_&_&_&Hdisj&_).
  rewrite l_assert_region_correct in Hdisj.
  rewrite elem_of_disjoint.
  intros a Ha Ha'.
  rewrite elem_of_disjoint in Hdisj.
  eapply Hdisj; eauto.
  rewrite elem_of_finz_seq_between.
  rewrite elem_of_list_singleton in Ha'; simplify_eq.
  pose proof l_assert_code_size.
  pose proof l_assert_cap_size.
  pose proof l_assert_flag_size.
  solve_addr.
Qed.

(** 5) Instantiate the linking table, containing only the `assert` routine. *)
Definition link_tbl `{memory_layout} : assert_tbl :=
  {|
    tbl_start := link_table_start;
    tbl_end :=link_table_end;
    tbl_size := link_table_size;
  |}.

(** 6) Align the full_run_spec with the specification of the adequacy. *)
Section ts_adequacy.
  Context {Σ:gFunctors}
          `{MP: MachineParameters}
          {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {oneshotg : one_shotG Σ}
          {nainv: logrel_na_invs Σ}
          {memlayout: memory_layout}
  .

  Definition trusted_memory_readoutN : namespace := nroot .@ "trusted_memory_readout".
  Definition link_tableN := (trusted_memory_readoutN.@"link_table").
  Definition ts_mainN := (trusted_memory_readoutN.@"main").
  Lemma ts_correct ecur etbl :
    let vinit := 0%nat in
    let P := ts_verifier_prog in
    let Adv := adv_prog in
    let RA := reserved_addresses_assert AssertLib vinit in
    let r_adv := r_t0 in

    let dom_etbl_all := seq 0 ecur : list TIndex in
    let dom_etbl_dead := filter (fun tidx => tidx ∉ dom etbl ) dom_etbl_all : list TIndex in
    let dummy_I := 0 : EIdentity in
    let etbl_dead := create_gmap_default dom_etbl_dead dummy_I : ETable in
    let etbl_all := etbl ∪ etbl_dead in

    is_initial_etable etbl ecur ->

    Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom (adequacy_flag_inv AssertLib)) m in
    (∀ rmap,
      dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep (adequacy_flag_inv AssertLib) vinit)
     ∗ na_inv logrel_nais assertN (assertInv AssertLib vinit)
     ∗ na_own logrel_nais ⊤ (*XXX*)

     (* Registers *)
     ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
     ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
     ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

     (* Memory *)
     (* P program *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
     (* Adv program  *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
     (* Linking Table *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region link_tbl AssertLib) vinit), a ↦ₐ w)

     ∗ EC⤇ ecur
     ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
     ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
  Proof.
    intros *.
    iIntros (Hetbl Hints Hfilter rmap Hdom)
      "(#Hinv & #Hassert & Hown & HPC & Hr_adv & Hrmap & Hprog & Hadv & Hlink & HEC & Hseal_store)".
    simpl.
    (* 1 - Allocate the system invariant *)
    iMod ( system_inv_alloc with "[$HEC $Hseal_store]") as "#Hsystem_inv"; eauto.

    (* 2 - Allocate the linking table invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ link_tableN
            (((tbl_start link_tbl), vinit) ↦ₐ word_to_lword (assert_entry_point AssertLib) vinit)
           with "[Hlink]") as "#Hinv_link".
    { iNext.
      rewrite /assert_tbl_region.
      rewrite /mkregion.
      cbn.
      rewrite finz_seq_between_cons.
      2:{ pose proof link_table_size as H; solve_addr + H. }
      rewrite finz_seq_between_empty.
      2:{ pose proof link_table_size as H; solve_addr + H. }
      cbn.
      rewrite memory_to_lmemory_insert /=.
      iDestruct (big_sepM_insert_delete with "Hlink") as "[$ _]".
    }

    (* 3 - Allocate validity of the adversary *)
    iAssert (|={⊤}=> interp (LCap RWX adv_start adv_end adv_start vinit))%I with "[Hadv]" as ">#Hadv".
    {
      pose proof adv_size as Hadv_size'.
      iApply (region_valid_in_regionL _ _ _ _ _ ((fun w=> word_to_lword w vinit) <$> adv_instrs));auto.
      - apply Forall_forall. intros. set_solver+.
      - rewrite -adv_region_correct.
        apply adv_not_reserved.
      - apply Forall_forall. intros.
        rewrite Forall_forall in Hints.
        apply elem_of_list_fmap_2 in H.
        destruct H as (w & -> & Hw).
        specialize (Hints w Hw).
        destruct Hints.
        + left. destruct w ; cbn in * ; done.
        + right.
          rewrite /in_regionL.
          rewrite /in_region in H.
          destruct w ; cbn in * ; try done.
          destruct sb ; cbn in * ; try done.
          naive_solver.
      - iApply (big_sepM_to_big_sepL2 with "[Hadv]").
        + apply finz_seq_between_NoDup.
        + rewrite fmap_length.
          rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.
        + subst Adv ; cbn.
          rewrite /prog_region /adv_prog; cbn.
          rewrite memory_to_lmemory_mk_logical_region_map.
          rewrite /logical_region_map.
          rewrite -logical_region_map_list_to_map; first done.
          * apply finz_seq_between_NoDup.
          * rewrite fmap_length.
            rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.
    }

    (* 4 - Allocate invariant of the code *)
    set (a_data := (prog_start P ^+ length (trusted_memory_readout_main_code 0))%a).
    set (link_capL := word_to_lword link_cap vinit).
    iMod (na_inv_alloc logrel_nais ⊤ ts_mainN
           (codefrag (prog_start P) vinit (trusted_memory_readout_main_code 0)
            ∗ (a_data, vinit) ↦ₐ link_capL
            ∗ ((a_data ^+ 1)%a, vinit) ↦ₐ LCap RWX (prog_start P) (prog_end P) a_data vinit)
         with "[Hprog]") as "#Hprog".
    { iNext.
      replace (prog_region P)
        with
        (mkregion verifier_start verifier_end
                 ((lword_get_word <$> trusted_memory_readout_main_code 0) ++
                 [link_cap;
                  WCap RWX verifier_start verifier_end (verifier_start ^+ trusted_memory_readout_main_code_len)%a])
              ) by done.
      pose proof verifier_size as Hsize_verifier.
      rewrite /trusted_memory_readout_main_len in Hsize_verifier.
      rewrite mkregion_app; last done.
      rewrite memory_to_lmemory_union.
      iDestruct (big_sepM_union with "Hprog") as "[Hprog Hdata]".
      { apply memory_to_lmemory_disjoint.
        rewrite /mkregion.
        apply map_disjoint_list_to_map_zip_l.
        + rewrite fmap_length.
          rewrite finz_seq_between_length.
          apply finz_dist_add.
          exists (verifier_start ^+ length (trusted_memory_readout_main_code 0))%a.
          cbn in *.
          solve_addr.
        + apply Forall_forall.
          intros a Ha.
          apply not_elem_of_list_to_map.
          rewrite fst_zip.
          * rewrite elem_of_finz_seq_between in Ha.
            rewrite not_elem_of_finz_seq_between.
            solve_addr.
          * rewrite fmap_length.
            rewrite finz_seq_between_length.
            cbn.
            rewrite finz_dist_S; last solve_addr.
            rewrite finz_dist_S; last solve_addr.
            rewrite finz_dist_0; last solve_addr.
            done.
      }
      replace ([link_cap; WCap RWX verifier_start verifier_end (verifier_start ^+ trusted_memory_readout_main_code_len)%a])
        with ([link_cap]++[WCap RWX verifier_start verifier_end (verifier_start ^+ trusted_memory_readout_main_code_len)%a]); last by cbn.
      rewrite mkregion_app; last solve_addr.
      rewrite memory_to_lmemory_union.
      iDestruct (big_sepM_union with "Hdata") as "[Hdata1 Hdata2]".
      { apply memory_to_lmemory_disjoint.
        rewrite /mkregion.
        apply map_disjoint_list_to_map_zip_l.
        + rewrite finz_seq_between_length.
          apply finz_dist_add.
          exists (verifier_start ^+ 38)%a.
          cbn in *.
          solve_addr.
        + apply Forall_forall.
          intros a Ha.
          apply not_elem_of_list_to_map.
          rewrite fst_zip.
          * rewrite elem_of_finz_seq_between in Ha.
            rewrite not_elem_of_finz_seq_between.
            solve_addr.
          * rewrite finz_seq_between_length.
            cbn.
            rewrite finz_dist_S; last solve_addr.
            rewrite finz_dist_0; last solve_addr.
            done.
      }

      iSplitL "Hprog"; [|iSplitL "Hdata1"].
      - rewrite /codefrag /region_mapsto.
        iApply (big_sepM_to_big_sepL2 with "[Hprog]").
        { apply NoDup_fmap; first (intros ? ? ?; by simplify_eq).
          apply finz_seq_between_NoDup.
        }
        { rewrite fmap_length.
          rewrite finz_seq_between_length.
          cbn.
          apply finz_dist_add.
          exists (verifier_start ^+ 37%nat)%a.
          solve_addr.
        }
        iEval (rewrite memory_to_lmemory_mk_logical_region_map) in "Hprog".
        iFrame.
      - iEval (rewrite memory_to_lmemory_mk_logical_region_map) in "Hdata1".
        rewrite finz_seq_between_cons; last solve_addr.
        rewrite finz_seq_between_empty; last solve_addr.
        iDestruct (big_sepM_insert_delete with "Hdata1") as "[$ _]".
      - iEval (rewrite memory_to_lmemory_mk_logical_region_map) in "Hdata2".
        rewrite finz_seq_between_cons; last solve_addr.
        rewrite finz_seq_between_empty; last solve_addr.
        iDestruct (big_sepM_insert_delete with "Hdata2") as "[$ _]".
    }
    iAssert (ts_main_inv verifier_start verifier_end vinit (trusted_memory_readout_main_code 0) a_data
               link_capL ts_mainN) with "Hprog" as "#Hprog_inv".

    (* 5 - Allocate invariant of the assert *)
    iAssert (assert_inv (assert_start AssertLib) (assert_flag AssertLib) (assert_end AssertLib)
               vinit assertN)
      with "Hassert" as "Hassert_inv".

    iAssert (flag_inv (assert_flag AssertLib) vinit invN) with "[Hinv]" as
      "#Hflag_inv".
    { iApply (inv_iff with "Hinv []").
      iNext. iModIntro.
      iSplit.
      - rewrite /minv_sep /=. iIntros "HH". iDestruct "HH" as (m) "(Hm & %Heq & %HOK)".
        assert (is_Some (m !! l_assert_flag)) as [? Hlook].
        { apply elem_of_dom. rewrite Heq. apply elem_of_singleton. auto. }
        assert ( (memory_to_lmemory m vinit) !! (l_assert_flag, vinit) = Some (word_to_lword x vinit)) as Hlook_log.
        { rewrite memory_to_lmemory_lookup.
          by rewrite Hlook; cbn.
        }
        iDestruct (big_sepM_lookup _ _ (l_assert_flag,vinit) with "Hm") as "Hflag"; eauto.
        apply HOK in Hlook as ->.
        iFrame.
      - iIntros "HH". iExists {[ l_assert_flag := WInt 0%Z ]}.
        rewrite /memory_to_lmemory map_fmap_singleton kmap_singleton.
        rewrite big_sepM_singleton. iFrame.
        rewrite dom_singleton_L /minv_dom /=. iSplit;auto.
        rewrite /OK_invariant. iPureIntro. intros w Hw. simplify_map_eq. done.
    }

    pose proof ( verifier_size ) as Hverifier_size.
    replace verifier_end with (verifier_start ^+ trusted_memory_readout_main_len)%a by solve_addr.

    (* 6 - Apply the full_run spec *)
    iApply (wp_wand _ _ _
              (λ v0 : val, (⌜v0 = HaltedV⌝ →
                            ∃ r : LReg, full_map r ∧ registers_mapsto r
                                        ∗ na_own logrel_nais ⊤) ∨ ⌜v0 = FailedV⌝)%I
             with "[-]")
    ; last (by iIntros (v) "H").
    iApply (trusted_memory_readout_full_run_spec with
             "[$Hadv $Hsystem_inv $Hinv_link $Hassert $Hprog_inv $Hflag_inv ] [ $HPC $Hown $Hr_adv $Hrmap]"); auto.
    + solve_ndisj.
    + solve_ndisj.
    + solve_ndisj.
    + solve_ndisj.
    + solve_ndisj.
    + subst P; rewrite /ts_verifier_prog /=.
      solve_addr.
    + rewrite /SubBounds.
      split; first solve_addr.
      split; last solve_addr.
      subst P; rewrite /ts_verifier_prog /=.
      rewrite /trusted_memory_readout_main_len.
      solve_addr.
    + pose proof link_table_size.
      cbn; solve_addr.
    + pose proof link_table_size.
      cbn.
      apply le_addr_withinBounds; solve_addr.
    + rewrite /register_to_lregister.
      by rewrite dom_fmap_L.
  Qed.

End ts_adequacy.


(** END-TO-END THEOREM *)
Theorem ts_enclaves_adequacy `{memory_layout}
    (m m': Mem) (reg reg': Reg) (etbl etbl' : ETable) (ecur ecur' : ENum)
    (es: list cap_lang.expr):
  is_initial_memory ts_verifier_prog adv_prog AssertLib link_tbl m →
  is_complete_memory m →
  is_initial_registers ts_verifier_prog adv_prog AssertLib link_tbl reg r_t0 →
  is_complete_registers reg m →
  is_initial_etable etbl ecur →
  Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := etbl ; enumcur := ecur |})
    (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
  (∀ w, m' !! l_assert_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? ? ? ? Hints.
  set (Σ' := #[one_shotΣ]).
  pose proof (template_adequacy Σ' ts_verifier_prog adv_prog AssertLib link_tbl) as Hadequacy.
  eapply Hadequacy;eauto.
  - eapply adequacy_flag_inv_is_initial_memory; eauto.
  - intros Σ ? ? ? ? ? ?.
    iIntros "(?&?&?&?&?&?&?&?&?&?&?)".
    iApply ts_correct; eauto; last iFrame.
Qed.
