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

  Inductive EStoreId_spec_fail (lregs : LReg) rd tidx I : cap_lang.val -> Prop :=
  |EStoreId_spec_failure_incr_pc:
    incrementLPC (<[rd:=LInt I]> lregs) = None →
    EStoreId_spec_fail lregs  rd tidx I FailedV
  |EStoreId_spec_failure_invalid_otype lw:
    get_otype_from_wint (lword_get_word lw) = None →
    EStoreId_spec_fail lregs rd tidx I FailedV
  |EStoreId_spec_failure_tidx_missing_in_etable lw ot (etbl : ETable):
    get_otype_from_wint (lword_get_word lw) = Some ot → (* necessary? *)
    tid_of_otype ot = tidx → (* necessary? *)
    etbl !! tidx = None →
    EStoreId_spec_fail lregs rd tidx I FailedV.

  Inductive EStoreId_spec (lregs lregs' : LReg) (rs rd : RegName) tidx (I : EIdentity) : cap_lang.val -> Prop :=
  | EStoreId_spec_success otype :
    lregs !! rs = Some (LInt otype) ->
    incrementLPC ((<[rd := LInt I]> lregs)) = Some lregs' →
    has_seal otype tidx → (* we associate a given table index with the provided otype *)
    (* 0 <= tidx < ecn -> *) (* can be derived from the state interp *)
    EStoreId_spec lregs lregs' rs rd tidx I NextIV
  | EStoreId_fail :
    lregs = lregs' ->
    EStoreId_spec_fail lregs rd tidx I FailedV →
    EStoreId_spec lregs lregs' rs rd tidx I FailedV.

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

  (* The EStoreId instruction fetches the machine's stored hash for a given OType.
     It is used by the client of an enclave to verify that a value signed by a given OType originates from code with a known hash `I`. *)
  (* Logically, the crux of this contract is that the post-condition contains a duplicable fragmental resource `enclave_all`,
     which states that an enclave has existed at some point in the past at some index `tidx` in the enclave table, and that this index corresponds to some hash/EIdentity `I` *)
  (* Essentially it gives us a partial view on the enclave table, since we now know that at a particular index, at some point, there was an enclave with a particular identity. *)
  (* In a later step of the verification, an invariant will allow us to trade this resource for the specific predicate that always holds for results signed by enclaves with that hash... *)
  (* This enables "learning" some information about the signed, yet unknown result: we will be able to establish that at least the above predicate will hold for it... *)
  (* NOTE @June what if we already have the resource `enclave_cur(tidx, I)` ? *)
  (* @Denis: that is the case when an enclave initializes and immediately attests itself. *)
  (* Then we need a separate rule, because the rule below is not general enough to derive the former *)
  (* For the time being, this rule is at least enough to prove the FTLR. *)
  Lemma wp_estoreid E pc_p pc_b pc_e pc_a pc_v lw rd rs lregs :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EStoreId rd rs) ⊆ dom lregs →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw
        (* (if with_ec then EC⤇ ecn else True) *) (* Domi says: ownership of the EC resource is unrelated to EStoreId *)
    }}}
      Instr Executable @ E
    {{{ lregs' tidx I retv, RET retv;
        ⌜ EStoreId_spec lregs lregs' rs rd tidx I retv⌝ ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        (* (if with_ec then EC⤇ ecn else True) ∗ *)
        (⌜(retv = NextIV)⌝ -∗ (enclave_all tidx I)) (*!*)}}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HPC φ) "(>Hrmap & Hpca) Hφ".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hrmap $Hpca Hφ]").
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
    iApply wp2_diag_univ.
    iSplit.
    { (* abort case: the WInt passed in rs is not a valid otype *)
      iIntros "%Hlw %Hlw2".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs $Hpc_a]"). iSplit. iPureIntro.
        apply EStoreId_fail; auto. now constructor 2 with (lw := lwr). iIntros "%H //". }

    iIntros (otype) "%Hlotype %Hotype".
    rewrite Hotype in Hlotype; inversion Hlotype; subst.

    (* rs contains an LWInt... *)
    destruct lwr. 2-3: cbn in Hotype; inversion Hotype.
    cbn in Hotype; subst.

    wp2_remember.
    iApply wp2_diag_univ.

    iSplit.
    { (* abort case: the enclave table does not have an entry for the passed index *)
      iIntros "%Hlw _".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs $Hpc_a]"). iSplit. iPureIntro.
        apply EStoreId_fail; auto. constructor 3 with (LWInt z) otype (etable σ1); eauto.
        iIntros "%H //". }

    iIntros (lhash) "%Hhash _".
    rewrite updatePC_incrementPC.
    wp2_remember.
    iApply wp_opt2_mono2.

    iSplitR "Hσ".
    2: {
      iApply transiently_wp_opt2.
      iMod "Hσ" as "(Hσr & Hσm & Hregs)".
      iModIntro.
      iApply wp_opt2_mod.
      iMod (gen_heap_update_inSepM _ _ rd (LInt lhash) with "Hσr Hregs") as "(Hσr & Hregs)".
      { rewrite -elem_of_dom. set_solver. }
      iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
      iApply (wp_opt2_frame with "Hσm").
      iModIntro.
      iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
      eapply dom_insert_subseteq, elem_of_dom_2, HPC.
      eapply (state_phys_log_corresponds_update_reg (lw := LInt lhash) eq_refl); cbn; eauto. }

    iSplit.
    { (* abort case: pc increment failed *)
      iIntros "Htr %HincLPC %Hancock".
      iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs)".
      iSplitR "Hφ Hregs Hpc_a".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hpc_a]").
      iSplit.
      -- iPureIntro.
         apply EStoreId_fail; auto. constructor 1.
         apply HincLPC.
      -- iIntros "%H //".
    }

    iIntros (lregs' regs') "Htr %Hlregs' %Hregs'".
    iApply wp2_val.

    (* need a fragment for `etable !! ltidx = Some lhash` *)
    iDestruct (enclave_all_alloc with "Hall_tb") as ">[Hall_tb Hall_frag]".
    by apply lookup_union_Some_l.

    iDestruct (transiently_commit with "Htr") as ">(Hlm & [%lr' (Hlr & %Hcorr & Hlregs')])".
    iModIntro.

    iSplitR "Hφ Hall_frag Hpc_a Hlregs'".
    cbn.

    (* Todo: should be able to frame I think? *)

    unfold state_interp_logical.
    destruct Hcorr as ((? & ?) & ? & ? & ?).
    iExists lr', lm, vmap, _, _, _.
    iFrame. cbn. repeat iSplit; auto.
    cbn.
    iApply "Hφ".
    iFrame. iSplit.
    iPureIntro. apply EStoreId_spec_success with (otype := z); auto.
    unfold has_seal; rewrite Hotype; auto.
    easy.

    Unshelve.
    (* @Denis says: TODO...
       We have shelved goals which arise from failure cases where the postcondition Hφ (which quantifies over
       a TIndex and an EIdentity) was applied, without a witness for either the table index or the identity
       (e.g. there was no valid table index).
       I am simply picking an arbitrary value in these cases, but this feels unsatisfactory.
       I think the right solution moves the existentially quantified tidx and I in the postcondition of the WP
       into the right places, and removes the tidx and I parameters of the spec, instead requiring them only
       for the relevant constructors. TBD... *)
    all: constructor 1.

  Qed.

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
    iApply ( wp_estoreid _ _ _ _ _ _ _ _ _ _ with "[$Hrmap$Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }


    iNext. iIntros (lregs' tidx I retv) "(#Hspec & Hrmap & HPCa & Henclave)".
    iDestruct "Hspec" as %Hspec.
    iApply "Hφ".
    destruct Hspec eqn:?; rewrite //
    ; simplify_eq; cycle 1; cbn; iFrame.
    - rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".
      iFrame.
      iRight; iFrame.
      done.
    - rewrite lookup_insert_ne in e ; last done.
      rewrite lookup_insert in e; simplify_eq.
      apply incrementLPC_Some_inv in e0 as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite (insert_commute _ rd PC) // insert_insert.
      rewrite (insert_commute _ rd rs) // insert_insert.
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".

      iFrame. iLeft; iFrame.
      iSplit ; first done.
      iExists I, tidx; iFrame.
      iSpecialize ("Henclave" with "[]"); first done.
      by iFrame.
    Qed.


  (* TODO unless we can find a way to derive `0 <= tidx < ecn` another way, keep it here *)
  Lemma wp_estoreid_with_ec E pc_p pc_b pc_e pc_a pc_v lw rd rs ecn lregs :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EStoreId rd rs) ⊆ dom lregs →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        EC⤇ ecn
    }}}
      Instr Executable @ E
    {{{ lregs' tidx I retv, RET retv;
        ⌜ EStoreId_spec lregs lregs' rs rd tidx I retv⌝ ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        EC⤇ ecn ∗
        (⌜(retv = NextIV)⌝ -∗ (enclave_all tidx I) ∗ ⌜ 0 <= tidx < ecn ⌝ ) (*!*)}}}.
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
    iApply wp2_diag_univ.
    iSplit.
    { (* abort case: the WInt passed in rs is not a valid otype *)
      iIntros "%Hlw %Hlw2".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a HEC".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs $Hpc_a $HEC]"). iSplit. iPureIntro.
        apply EStoreId_fail; auto. now constructor 2 with (lw := lwr). iIntros "%H //". }

    iIntros (otype) "%Hlotype %Hotype".
    rewrite Hotype in Hlotype; inversion Hlotype; subst.

    (* rs contains an LWInt... *)
    destruct lwr. 2-3: cbn in Hotype; inversion Hotype.
    cbn in Hotype; subst.

    wp2_remember.
    iApply wp2_diag_univ.

    iSplit.
    { (* abort case: the enclave table does not have an entry for the passed index *)
      iIntros "%Hlw _".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a HEC".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs $Hpc_a $HEC]"). iSplit. iPureIntro.
        apply EStoreId_fail; auto. constructor 3 with (LWInt z) otype (etable σ1); eauto.
        iIntros "%H //". }

    iIntros (lhash) "%Hhash _".
    rewrite updatePC_incrementPC.
    wp2_remember.
    iApply wp_opt2_mono2.

    iSplitR "Hσ".
    2: {
      iApply transiently_wp_opt2.
      iMod "Hσ" as "(Hσr & Hσm & Hregs)".
      iModIntro.
      iApply wp_opt2_mod.
      iMod (gen_heap_update_inSepM _ _ rd (LInt lhash) with "Hσr Hregs") as "(Hσr & Hregs)".
      { rewrite -elem_of_dom. set_solver. }
      iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
      iApply (wp_opt2_frame with "Hσm").
      iModIntro.
      iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
      eapply dom_insert_subseteq, elem_of_dom_2, HPC.
      eapply (state_phys_log_corresponds_update_reg (lw := LInt lhash) eq_refl); cbn; eauto. }

    iSplit.
    { (* abort case: pc increment failed *)
      iIntros "Htr %HincLPC %Hancock".
      iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs)".
      iSplitR "Hφ Hregs Hpc_a HEC".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hpc_a $HEC]").
      iSplit.
      -- iPureIntro.
         apply EStoreId_fail; auto. constructor 1.
         apply HincLPC.
      -- iIntros "%H //".
    }

    iIntros (lregs' regs') "Htr %Hlregs' %Hregs'".
    iApply wp2_val.

    (* need a fragment for `etable !! ltidx = Some lhash` *)
    iDestruct (enclave_all_alloc with "Hall_tb") as ">[Hall_tb Hall_frag]".
    by apply lookup_union_Some_l.

    iCombine "Hecauth HEC" as "Henumcur".
    iDestruct (own_valid with "Henumcur") as "%Hvalid_ec".
    apply excl_auth.excl_auth_agree_L in Hvalid_ec.
    rewrite -Hvalid_ec.
    iAssert (⌜(tid_of_otype otype) ∈ dom (etable σ1 ∪ prev_tb)⌝%I) as "%Hin".
    {
      iCombine "Hall_tb" "Hall_frag" as "Hall".
      iDestruct (own_valid with "Hall") as "%Hvalid_all".
      apply auth_both_valid_discrete in Hvalid_all as [Hlt_all Hvalid_all].
      apply gmap.dom_included in Hlt_all.
      by rewrite dom_singleton dom_fmap singleton_subseteq_l in Hlt_all.
    }
    rewrite Hdomtbcompl in Hin.
    rewrite list_to_set_seq in Hin.
    rewrite elem_of_set_seq /= in Hin.
    iDestruct "Henumcur" as "[Hecauth HEC]".

    iDestruct (transiently_commit with "Htr") as ">(Hlm & [%lr' (Hlr & %Hcorr & Hlregs')])".
    iModIntro.

    iSplitR "Hφ Hall_frag Hpc_a Hlregs' HEC".
    cbn.

    (* Todo: should be able to frame I think? *)

    unfold state_interp_logical.
    destruct Hcorr as ((? & ?) & ? & ? & ?).
    iExists lr', lm, vmap, _, _, _.
    iFrame. cbn. repeat iSplit; auto.
    cbn.
    iApply "Hφ".
    iFrame. iSplit.
    iPureIntro. apply EStoreId_spec_success with (otype := z); auto.
    unfold has_seal; rewrite Hotype; auto.
    easy.

    Unshelve.
    all: constructor 1.
  Qed.


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
    iApply ( wp_estoreid_with_ec _ _ _ _ _ _ _ _ _ _ with "[$Hrmap $Hpc_a $HEC]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }


    iNext. iIntros (lregs' tidx I retv) "(#Hspec & Hrmap & HPCa & HEC & Henclave)".
    iDestruct "Hspec" as %Hspec.


    destruct Hspec eqn:?; rewrite //
    ; simplify_eq; cycle 1; cbn; iApply "Hφ"; iFrame.
    - rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".
      iFrame.
      iRight; iFrame.
      done.
    - rewrite lookup_insert_ne in e ; last done.
      rewrite lookup_insert in e; simplify_eq.
      apply incrementLPC_Some_inv in e0 as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite (insert_commute _ rd PC) // insert_insert.
      rewrite (insert_commute _ rd rs) // insert_insert.
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".
      iFrame. iLeft; iFrame.
      iSplit ; first done.
      iExists I, tidx; iFrame.
      iSpecialize ("Henclave" with "[]"); first done.
      iDestruct "Henclave" as "[$ $]".
      done.
  Qed.

End cap_lang_rules.
