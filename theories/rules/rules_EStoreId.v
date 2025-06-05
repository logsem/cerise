From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac gmap agree local_updates.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.
  Implicit Types etable : ETable.


  Inductive EStoreId_spec (lregs lregs' : LReg) (rs rd : RegName) tidx (I : EIdentity) (ecn : ENum) : cap_lang.val -> Prop :=
  | EStoreId_spec_success otype :
    lregs !! rs = Some (LInt otype) ->
    incrementLPC ((<[rd := LInt I]> lregs)) = Some lregs' →
    has_seal otype tidx → (* we associate a given table index with the provided otype *)
    0 <= tidx < ecn ->
    EStoreId_spec lregs lregs' rs rd tidx I ecn NextIV
  |EStoreId_spec_failure_incr_pc:
    incrementLPC lregs = None →
    lregs = lregs' →
    EStoreId_spec lregs lregs' rs rd tidx I ecn FailedV
  |EStoreId_spec_failure_invalid_otype lw:
    get_otype_from_wint (lword_get_word lw) = None →
    lregs = lregs' →
    EStoreId_spec lregs lregs' rs rd tidx I ecn FailedV
  (* |EStoreId_spec_failure_tidx_invalid_for_otype lw ot: *)
  (*   get_otype_from_wint (lword_get_word lw) = Some ot → (* necessary? *) *)
  (*   tid_of_otype ot = None → *)
  (*   lregs = lregs' → *)
    (* EStoreId_spec lregs lregs' rs rd tidx I ecn FailedV *)
  |EStoreId_spec_failure_tidx_missing_in_etable lw ot (etbl : ETable):
    get_otype_from_wint (lword_get_word lw) = Some ot → (* necessary? *)
    tid_of_otype ot = tidx → (* necessary? *)
    etbl !! tidx = None →
    lregs = lregs' →
    EStoreId_spec lregs lregs' rs rd tidx I ecn FailedV.

  (* Creates a fragmental "all" resource for the enclave e at index i in the etable *)
  Lemma enclave_all_alloc etable i e :
    etable !! i = Some e →
    enclaves_all etable
    ⊢ |==> enclaves_all etable ∗ enclave_all i e.
  Proof.
    iIntros (Hexists) "Hall".
    iDestruct (own_update with "Hall") as "Hall".
    { apply auth_update_alloc,
           (gmap_local_update
               _ _
               (to_agree <$> etable)
               (to_agree <$> {[i := e]})).
      intro i'.
      rewrite !lookup_fmap lookup_empty.
      destruct (decide (i = i')); subst.
      2: by rewrite lookup_singleton_ne.
      rewrite Hexists; cbn.
      rewrite lookup_singleton. cbn.
      rewrite -{3}(ucmra_unit_left_id (A := optionUR (agreeR EIdentity)) (Some (to_agree e))).
      apply core_id_local_update.
      apply _.
      easy. }

    rewrite map_fmap_singleton.
    by iDestruct "Hall" as ">[Hall Hfrag]"; iFrame.
    Qed.

  Ltac wp2_remember := iApply wp_opt2_bind; iApply wp_opt2_eqn_both.

  (* TODO @Denis *)
  (* The EStoreId instruction fetches the machine's stored hash for a given OType.
     It is used by the client of an enclave to verify that a value signed by a given OType originates from code with a known hash `I`. *)
  (* Logically, the crux of this contract is that the post-condition contains a duplicable resource `enclave_all`,
     which states that an enclave has existed at some point in the past at some index `tidx` in the enclave table, and that this index corresponds to some hash/EIdentity `I` *)
  (* Essentially it gives us a partial view on the enclave table, since we now know that at a particular index, at some point, there was an enclave with a particular identity. *)
  (* In a later step of the verification, an invariant will allow us to trade this resource for the specific predicate that always holds for results signed by enclaves with that hash... *)
  (* This enables "learning" some information about the signed, yet unknown result: we will be able to establish that at least the above predicate will hold for it... *)
  (* NOTE @June what if we already have the resource `enclave_cur(tidx, I)` ? *)
  (* @Denis: that is the case when an enclave initializes and immediately attests itself. *)
  (* Then we need a separate rule, because the rule below is not general enough to derive the former *)
  (* For the time being, this rule is at least enough to prove the FTLR. *)
  Lemma wp_estoreid E pc_p pc_b pc_e pc_a pc_v lw rd rs lregs (with_ec : bool) (ecn : ENum) :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EStoreId rd rs) ⊆ dom lregs →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        (if with_ec then EC⤇ ecn else True)
    }}}
      Instr Executable @ E
    {{{ lregs' tidx I retv, RET retv;
        ⌜ EStoreId_spec lregs lregs' rs rd tidx I ecn retv⌝ ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        (if with_ec then EC⤇ ecn else True) ∗
        if decide (retv = NextIV) then (enclave_all tidx I) (*!*) else emp }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HPC φ) "(>Hrmap & Hpca & HEC) Hφ".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hrmap $Hpca HEC Hφ]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hrmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) _".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply (wp_wp2
              (φ1 :=
                 lwσ  ← lregs !! rs;
                 lσa  ← get_otype_from_wint (lword_get_word lwσ); (* easier than def. a logically equiv fn *)
                 let tid := tid_of_otype lσa in
                 eid  ← (etable σ1) !! tid;
                 lregs' ← incrementLPC (<[rd := LWInt eid]> lregs);
                 Some lregs'
              )).
    iModIntro.
    iDestruct "Hσ1" as "(%lr & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hrmap") as "%Hlrsub".
    iCombine "Hlr Hlm Hrmap" as "Hσ".
    iDestruct (transiently_intro with "Hσ") as "Hσ".

    wp2_remember.

    iApply wp_opt2_mono2.
    iSplitR "". 2: iApply wp2_reg_lookup5; eauto; set_solver.

    iSplit; first now iIntros.
    iIntros (lwr wr) "-> %Hlwr %Hwr".

    assert (lr !! rs = Some lwr) as Hlrs by eapply (lookup_weaken _ _ _ _ Hlwr Hlrsub).

    wp2_remember.

    iApply wp_opt2_mono2.
    iSplitR "". 2: now iApply (wp2_diag_univ (Φf := True%I) (Φs := fun _ _ => True)%I).
    iSplit.
    { (* abort case: the Wont passed in rs is not a valid otype *)
      iIntros "_ %Hlw %Hlw2".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a HEC".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs Hpc_a HEC]"). iFrame. iPureIntro. now constructor 3 with lwr.
    }

    iIntros (otype otype2) "_ %Hlotype %Hotype".
    rewrite Hotype in Hlotype; inversion Hlotype; subst.

    (* rs contains an LWInt... *)
    destruct lwr. 2-3: cbn in Hotype; inversion Hotype.
    cbn in Hotype; subst.

    wp2_remember.
    iApply wp_opt2_mono2.

    (* iSplitR "". *)
    (* 2: now iApply (wp2_diag_univ (Φf := True%I) (Φs := fun _ _ => True)%I). *)
    (* iSplit. *)
    (* { (* abort case: the passed otype is not a valid table index *) *)
    (*   iIntros "_ %Hlw %Hlw2". *)
    (*   iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)". *)
    (*   iSplitR "Hφ Hregs Hpc_a HEC". *)
    (*   - iExists lr, lm, vmap, _, _, _; now iFrame. *)
    (*   - iApply ("Hφ" with "[$Hregs Hpc_a HEC]"). iFrame. iPureIntro. now constructor 4 with (LWInt z) otype. *)
    (* } *)

    (* iIntros (ltidx tidx) "_ %Hltidx %Htidx". *)
    (* rewrite Htidx in Hltidx; inversion Hltidx; subst. *)
    (* wp2_remember. *)
    (* iApply wp_opt2_mono2. *)
    set ( tidx := tid_of_otype otype).

    iSplitR "".
    2: now iApply (wp2_diag_univ (Φf := True%I) (Φs := fun _ _ => True)%I).
    iSplit.
    { (* abort case: the enclave table does not have an entry for the passed index *)
      iIntros "_ %Hlw %Hlw2".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      Print enclaves_all.
      iSplitR "Hφ Hregs Hpc_a HEC".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs Hpc_a HEC]"). iFrame. iPureIntro. constructor 4 with (LWInt z) otype (etable σ1); eauto. }

    iIntros (lhash hash) "_ %Hlhash %Hhash".
    rewrite Hhash in Hlhash; inversion Hlhash; subst.
    rewrite updatePC_incrementPC.
    wp2_remember.
    iApply wp_opt2_mono2.

    iSplitR "".
    2: {
      iApply wp2_opt_incrementPC.
      ++ eapply dom_insert_subseteq, elem_of_dom_2, HPC.
      ++ admit.
    }

    iSplit.
    { (* abort case: pc increment failed *)
      iIntros "_ %Hlw %Hlw2".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a HEC".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply "Hφ". iSplit. iPureIntro. econstructor 2.
        1-2: admit. iFrame. }

    iIntros (lregs' regs') "HRregs' %Hlregs' %Hregs'".
    iApply wp2_val.

    (* need a fragment for `etable !! ltidx = Some lhash` *)
    iDestruct (enclave_all_alloc with "Hall_tb") as ">[Hall_tb Hall_frag]".
    by apply lookup_union_Some_l.

    iDestruct (transiently_commit with "Hσ") as "Hpost".
    iMod "Hpost".
    iModIntro.

    iSplitL "". cbn. admit.
    (* iSplitR "Hφ Hpc_a HEC". cbn. iFrame. *)

    cbn.
    iApply "Hφ".
    iFrame.
    iSplit. iPureIntro. econstructor 1; eauto.
     + unfold has_seal. rewrite Hotype; auto.
     + (* by Hdomtbcompl ... *) admit.
     + admit.

 Admitted.

  Lemma wp_estoreid_success_unknown_ec E pc_p pc_b pc_e pc_a pc_a' pc_v lw rd rs otype any ecn :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
        ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ rs ↦ᵣ LWInt otype ∗
        ▷ rd ↦ᵣ any ∗
        ▷ EC⤇ ecn
    }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (pc_a, pc_v) ↦ₐ lw ∗
        rs ↦ᵣ LWInt otype ∗
        EC⤇ ecn ∗
        ((⌜ retv = NextIV ⌝ ∗
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
          ∃ (I : EIdentity), ∃ (tid : TIndex),
            rd ↦ᵣ (LWInt I) ∗
            (enclave_all tid I) ∗
            ⌜ has_seal otype tid ⌝ ∗
            ⌜ 0 <= tid < ecn ⌝
         )
           ∨
           (⌜ retv = FailedV ⌝ ∗
            PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
            rd ↦ᵣ any)
         ) }}}.
    Proof.
    iIntros (Hinstr Hvpc Hpca φ) "(>HPC & >Hpc_a & >Hrs & >Hrd & >HEC) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrs Hrd") as "[Hrmap (%&%&%)]".

    (* iDestruct (big_opM_delete with "H"). *)
    iApply ( wp_estoreid _ _ _ _ _ _ _ _ _ _ true with "[$Hrmap $HEC $Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }


    iNext. iIntros (lregs' tidx I retv) "(#Hspec & Hrmap & HPCa & HEC & Henclave)".
    iDestruct "Hspec" as %Hspec.

    admit.
    (* need to add the new constructors *)

  (*   destruct Hspec eqn:? *)
  (*   ; [ erewrite decide_True | erewrite decide_False | erewrite decide_False | erewrite decide_False ]; rewrite // ; *)
  (*     simplify_eq; cycle 1; cbn; iApply "Hφ"; iFrame. *)
  (*   - rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[HPC Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrs Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrd _]". *)
  (*     iFrame. *)
  (*     iRight; iFrame. *)
  (*     done. *)
  (*   - rewrite lookup_insert_ne in e ; last done. *)
  (*     rewrite lookup_insert in e; simplify_eq. *)
  (*     apply incrementLPC_Some_inv in e0 as (?&?&?&?&?&?&?&?&?); simplify_map_eq. *)
  (*     rewrite (insert_commute _ rd PC) // insert_insert. *)
  (*     rewrite (insert_commute _ rd rs) // insert_insert. *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[HPC Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrs Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrd _]". *)

  (*     iFrame. iLeft; iFrame. *)
  (*     iSplit ; first done. *)
  (*     iExists I, tidx; iFrame. *)
  (*     done. *)
  (* Qed. *)
  Admitted.

  Lemma wp_estoreid_success_unknown E pc_p pc_b pc_e pc_a pc_a' pc_v lw rd rs otype any :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
        ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ rs ↦ᵣ LWInt otype ∗
        ▷ rd ↦ᵣ any
    }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (pc_a, pc_v) ↦ₐ lw ∗
        rs ↦ᵣ LWInt otype ∗
        ((⌜ retv = NextIV ⌝ ∗
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
          ∃ (I : EIdentity), ∃ (tid : TIndex),
            rd ↦ᵣ (LWInt I) ∗
            (enclave_all tid I) ∗
            ⌜ has_seal otype tid ⌝
         )
           ∨
           (⌜ retv = FailedV ⌝ ∗
            PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
            rd ↦ᵣ any)
         ) }}}.
    Proof.
    iIntros (Hinstr Hvpc Hpca φ) "(>HPC & >Hpc_a & >Hrs & >Hrd) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrs Hrd") as "[Hrmap (%&%&%)]".

    (* iDestruct (big_opM_delete with "H"). *)
    iApply ( wp_estoreid _ _ _ _ _ _ _ _ _ _ false 0 with "[$Hrmap$Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }


    iNext. iIntros (lregs' tidx I retv) "(#Hspec & Hrmap & HPCa & HEC & Henclave)".
    iDestruct "Hspec" as %Hspec.

  (*   destruct Hspec eqn:? *)
  (*   ; [ erewrite decide_True | erewrite decide_False ]; rewrite // ; *)
  (*     simplify_eq; cycle 1; cbn; iApply "Hφ"; iFrame. *)
  (*   - rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[HPC Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrs Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrd _]". *)
  (*     iFrame. *)
  (*     iRight; iFrame. *)
  (*     done. *)
  (*   - rewrite lookup_insert_ne in e ; last done. *)
  (*     rewrite lookup_insert in e; simplify_eq. *)
  (*     apply incrementLPC_Some_inv in e0 as (?&?&?&?&?&?&?&?&?); simplify_map_eq. *)
  (*     rewrite (insert_commute _ rd PC) // insert_insert. *)
  (*     rewrite (insert_commute _ rd rs) // insert_insert. *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[HPC Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrs Hrmap]". *)
  (*     rewrite big_sepM_insert; last by simplify_map_eq. *)
  (*     iDestruct "Hrmap" as "[Hrd _]". *)

  (*     iFrame. iLeft; iFrame. *)
  (*     iSplit ; first done. *)
  (*     iExists I, tidx; iFrame. *)
  (*     done. *)
  (* Qed. *)
    Admitted.


End cap_lang_rules.
