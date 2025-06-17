From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac excl gmap.
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

  Lemma enclave_cur_compat {tidx eid cur_tb} :
    enclave_cur tidx eid -∗ enclaves_cur cur_tb -∗ ⌜ cur_tb !! tidx = Some eid ⌝.
  Proof.
    iIntros "Hcur Hcur_tb".
    iDestruct (own_valid_2 with "Hcur_tb Hcur") as "%Hvalid".
    iPureIntro.
    apply auth_both_valid_discrete in Hvalid.
    destruct Hvalid as (Hincl & _).
    apply singleton_included_l in Hincl.
    destruct Hincl as (I' & HeqI' & HII').
    rewrite lookup_fmap in HeqI'.
    destruct I';
      last by (destruct (cur_tb !! tidx); apply leibniz_equiv in HeqI'; inversion HeqI').
    rewrite Excl_included in HII'.
    apply leibniz_equiv in HII'; subst.
    apply leibniz_equiv in HeqI'.
    destruct (cur_tb !! tidx);
      now inversion HeqI'.
  Qed.


  Lemma enclave_update_deinit {cur_tb prev_tb tidx I} :
    cur_tb ##ₘ prev_tb ->
    enclaves_cur cur_tb -∗ enclaves_prev prev_tb -∗ enclave_cur tidx I ==∗ enclave_prev tidx ∗ enclaves_cur (delete tidx cur_tb) ∗ enclaves_prev (insert tidx I prev_tb).
  Proof.
    iIntros (Hdisj) "Hcur_tb Hprev_tb Hcur".
    iPoseProof (enclave_cur_compat with "Hcur Hcur_tb") as "%Hcurtbtidx".
    iCombine "Hcur_tb Hcur" as "Hcurm".
    iMod (own_update with "Hcurm") as "Hcurm".
    { eapply (auth_update_dealloc _ _ (excl.Excl <$> (delete tidx cur_tb))).
      rewrite fmap_delete.
      now apply (@delete_singleton_local_update TIndex _ _ (excl EIdentity) (Excl <$> cur_tb)).
    }
    iMod (own_update with "Hprev_tb") as "(Hprev_tb & Hprev)".
    { eapply (auth_update_alloc _ (to_agree <$> (insert tidx I prev_tb)) {[ tidx := to_agree I]} ).
      rewrite fmap_insert -insert_empty.
      eapply alloc_singleton_local_update; last done.
      rewrite lookup_fmap.
      enough (prev_tb !! tidx = None) as H by now rewrite H.
      now apply (map_disjoint_Some_l _ _ _ _ Hdisj Hcurtbtidx).
    }
    iModIntro.
    iSplitL "Hprev".
    - now iExists I.
    - now iFrame.
      (* + now rewrite union_delete_insert. *)
      (* + eapply map_disjoint_dom_2. *)
      (*   set_solver. *)
      (* + now eapply union_delete_insert. *)
  Qed.

  Lemma get_sealing_cap_lword {lwr permitSeal permitUnseal σb σe σa} :
    get_sealing_cap (lword_get_word lwr) = Some (permitSeal, permitUnseal, σb, σe, σa) ->
    lwr = LSealRange (permitSeal, permitUnseal) σb σe σa.
  Proof.
    destruct lwr as [|[ |(? & ?) ? ? ? ]| ]; now inversion 1.
  Qed.


  Inductive EDeInit_fail lregs : Prop :=
  | EDeInit_fail_no_valid_PC :
    incrementLPC lregs = None →
    EDeInit_fail lregs
  | EDeInit_fail_no_seal_unseal_pair :
    (*... → *)
    EDeInit_fail lregs.

  Inductive EDeInit_spec (lregs lregs' : LReg) r (tidx : TIndex) (eid : EIdentity) is_cur : cap_lang.val → Prop :=
  | EDeInit_success b e a:
    (b+2)%ot = Some e →
    lregs !! r = Some (LSealRange (true,true) b e a) →
    incrementLPC lregs = Some lregs' →
    is_cur = true →
    EDeInit_spec lregs lregs' r tidx eid is_cur NextIV
  | EDeInit_failure :
    EDeInit_fail lregs →
    lregs = lregs' →
    EDeInit_spec lregs lregs' r tidx eid is_cur FailedV.

  (* SealRange <-> Word *)
  Definition is_seal_range (w : option LWord) : bool :=
    match w with
    | Some (LSealRange (true,true) b e a) =>
        match (b+2)%ot with
        | Some b2 => (e =? b2)%ot
        | None => false
        end
    |  _ => false
    end.
  Ltac wp2_remember := iApply wp_opt2_bind; iApply wp_opt2_eqn_both.

  Definition word_allows_deinit_or_true (lw : LWord) tidx :=
    forall permitSeal permitUnseal σb σe σa, lw = LWSealable (LSSealRange (permitSeal, permitUnseal) σb σe σa) ->
                                (bool_decide ((permitSeal, permitUnseal) = (true, true)) && (σe =? (σb ^+ 2)%f)%Z) ->
                                tidx = tid_of_otype σb.

  (* TODO @Denis *)
  Lemma wp_edeinit E pc_p pc_b pc_e pc_a pc_v lw lwσ r lregs tidx eid (is_cur : bool) :
    decodeInstrWL lw = EDeInit r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! r = Some lwσ ->
    word_allows_deinit_or_true lwσ tidx ->
      (* EC register does not decrement (i.e. it acts as a bump allocator) *)

      {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
            (pc_a, pc_v) ↦ₐ lw ∗
            (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
            (* if is_cur *)
            (* then enclave_cur tidx eid *)
            (* else enclave_prev tidx *)
          enclave_cur tidx eid
    }}}
      Instr Executable @ E
    {{{ lregs' retv, RET retv;
        ⌜ EDeInit_spec lregs lregs' r tidx eid is_cur retv⌝ ∗
        match retv with
        | NextIV => enclave_prev tidx
        | _ => enclave_cur tidx eid
        end ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hr Hallow φ) "(>Hrmap & Hpca & Hofrag) Hφ".

    pose proof (elem_of_dom_2 _ _ _ Hr) as Dregsr.
    assert (regs_of (EDeInit r) ⊆ dom lregs) as Dregs by set_solver.
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hrmap $Hpca Hφ Hofrag]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hrmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) _".

    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.

    iModIntro.


    iDestruct "Hσ1" as "(%lr & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)".

    iApply (wp_wp2
              (φ1 :=
                 lwr ← lregs !! r; (* σ should be a seal/unseal pair *)
                 '(p,σb,σe,_) ← get_sealing_cap (lword_get_word lwr);
                 if decide ((bool_decide (p = (true,true))) && (σe =? σb^+2)%ot) then
                   let tidx := tid_of_otype σb in
                   let cur_tb' := delete tidx cur_tb in
                   lregs' ← incrementLPC lregs;
                   Some lregs'
                 else None
              )).

    iDestruct (gen_heap_valid_inclSepM with "Hlr Hrmap") as "%Hlrsub".
    wp2_remember.
    iApply wp_opt2_mono2.
    iSplitR "".
    2: iApply (wp2_reg_lookup5 Dregsr Hlrsub Hcorr0).
    iSplit.
    { now iIntros (f).}
    iIntros (lwr wr -> Hlwr Hwr).
    assert (lwσ = lwr) as ->.
    {rewrite Hr in Hlwr. now inversion Hlwr.}
    clear Hr.

    iDestruct (enclave_cur_compat with "Hofrag Hcur_tb") as "%Hcurtbtidx".

    iCombine "Hlr Hlm Hrmap Hall_tb Hcur_tb Hprev_tb Hecauth Hofrag Hpc_a" as "Hσ".
    iDestruct (transiently_intro with "Hσ") as "Hσ".

    wp2_remember.
    iApply wp2_diag_univ.
    iSplit.
    { iIntros "%Hlwrgc _".
      iDestruct (transiently_abort with "Hσ") as "(Hlr & Hlm & Hregs & Hall_tb & Hcur_tb & Hprev_tb & Hecauth & Hofrag & Hpc_a)".
      iSplitR "Hφ Hofrag Hregs Hpc_a".
      { iExists _, _, vmap, _, _, _ ; now iFrame. }
      iApply "Hφ"; iFrame.
      iPureIntro; constructor; last done.
      now apply EDeInit_fail_no_seal_unseal_pair.
    }
    iIntros (seal Hlwrgc _). destruct seal as ((([permitSeal permitUnseal] & σb) & σe) & σa).
    eapply get_sealing_cap_lword in Hlwrgc; subst.

    (* annoying. *)
    destruct (bool_decide ((permitSeal, permitUnseal) = (true, true)) && (σe =? (σb ^+ 2)%f)%Z) eqn:Hdec.
    - destruct (andb_prop _ _ Hdec) as (Hseals%bool_decide_eq_true_1 & Hbounds%Z.eqb_eq%finz_to_z_eq).
      inversion Hseals; subst; clear Hseals.
      rewrite (decide_True_pi (P := Is_true true) I).
      rewrite updatePC_incrementPC.
      destruct σ1; cbn.
      wp2_remember.
      iApply wp_opt2_mono2.
      iSplitL "Hφ".
      2: {
        iApply transiently_wp_opt2.
        iMod "Hσ" as "(Hσr & Hσm & Hregs & Hall_tb & Hcur_tb & Hprev_tb & Hecauth & Hofrag & Hpc_a)".
        iMod (enclave_update_deinit Htbdisj with "Hcur_tb Hprev_tb Hofrag") as "(Hofrag & Hcur_tb & Hprev_tb)".
        iModIntro.
        iApply (wp_opt2_frame with "Hσm").
        iApply (wp_opt2_frame with "Hpc_a").
        iApply (wp_opt2_frame with "Hall_tb").
        iApply (wp_opt2_frame with "Hcur_tb").
        iApply (wp_opt2_frame with "Hprev_tb").
        iApply (wp_opt2_frame with "Hecauth").
        iApply (wp_opt2_frame with "Hofrag").
        iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
        now eapply elem_of_dom.
      }
      iSplit.
      { iIntros "Hσ %HincLPCf %HincPCf".
        iDestruct (transiently_abort with "Hσ") as "(Hr & Hm & Hregs & Hall_tb & Hcur_tb & Hprev_tb & Hecauth & Hofrag & Hpc_a)".
        iSplitL "Hr Hm Hecauth Hall_tb Hcur_tb Hprev_tb".
        { iExists _, _, _, _, _, _; iFrame.
          iPureIntro.
          cbn in *.
          intuition eauto.
        }
        iApply "Hφ"; iFrame.
        iPureIntro.
        constructor 2; eauto.
        now eapply EDeInit_fail_no_valid_PC.
      }
      iIntros (lregs' regs) "Hσ %HincLPC %HincPC".
      iApply wp2_val.
      iMod (transiently_commit with "Hσ") as "(Hm & Hpc_a & Hall_tb & Hur_tb & Hprev_tb & Hecauth & Hprev & %lregs2 & Hlregs2 & %Hcorr & Hregs)".
      iModIntro.
      iSplitR "Hφ Hregs Hpc_a Hprev".
      + unfold update_regs; cbn.
        iExists _, _, _, _, _, _; iFrame; cbn.
        cbn in *.
        iPureIntro; intuition eauto.
        * f_equiv.
          eapply (Hallow _ _ _ _ _ eq_refl).
          now eapply Is_true_true_2.
        * set_solver.
        * now rewrite union_delete_insert.
        * apply map_disjoint_dom_2.
          set_solver.
        * now rewrite union_delete_insert.
      + iApply "Hφ"; iFrame.
        iPureIntro.
        econstructor 1; try done.
        admit.
        admit.
    - erewrite !(decide_False (H := Is_true_dec false)); eauto.
      iModIntro.
      iDestruct (transiently_abort with "Hσ") as "(Hr & Hm & Hregs & Hall_tb & Hcur_tb & Hprev_tb & Hecn & Hcur & Hpc_a)".
      iSplitR "Hφ Hcur Hregs Hpc_a".
      + iExists _, _, _, _, _, _; iFrame.
        iPureIntro; intuition eauto.
      + iApply ("Hφ" with "[ Hcur $Hregs $Hpc_a]"); iFrame.
        iPureIntro.
        constructor 2; last done.
        apply EDeInit_fail_no_seal_unseal_pair.
  Admitted.

End cap_lang_rules.
