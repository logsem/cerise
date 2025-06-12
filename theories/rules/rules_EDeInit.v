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

  Lemma enclave_update_deinit tidx I σ :
    state_interp_logical σ
    ⊢ enclave_cur tidx I ==∗ enclave_prev tidx.
  Proof.
    unfold enclave_cur, enclave_prev.
    iIntros "Hσ Hcur".
    iExists I.
    unfold state_interp_logical.
    iDestruct "Hσ" as "(%_ & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & _ & _ & %Hetable & Hcur_tb & Hprev_tb & _ & _ & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & _)".
    Search "update" "dealloc".
    unfold enclaves_cur.
    (* remove tidx from enclaves_cur *)
    iCombine "Hcur_tb Hcur" as "Hcurm".
    iDestruct (own_update with "Hcurm") as "Hcurm".
    rewrite (@auth_update_dealloc (gmapUR TIndex (excl EIdentity)) _ {[tidx := excl.Excl I]} (excl.Excl <$> (delete tidx cur_tb))).
    Search gmap (_ ~~> _).
    admit.
    Search gmap (_ ~l~> _).
    Search fmap delete.
    rewrite fmap_delete.
    Check Excl <$> cur_tb.
    apply (@delete_singleton_local_update TIndex _ _ (excl EIdentity) (Excl <$> cur_tb)).
    apply _.
    Search (● _ ⋅ ◯ _).

    (* create a fragment for tidx in enclaves_prev *)
    iDestruct (own_update with "Hprev_tb") as "Hprev".
    apply auth_update_alloc.
    apply (gmap_local_update
               _ _
               (to_agree <$> prev_tb)
               (to_agree <$> {[tidx := I]})).
    cbn.
    (* ... *)
    1: admit.
    iMod "Hcurm".
    iMod "Hprev".
    iModIntro.
    iDestruct "Hprev" as "(Hprev_tb & Hprev_frag)".
    by rewrite map_fmap_singleton.
  Admitted.



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

  (* TODO @Denis *)
  Lemma wp_edeinit E pc_p pc_b pc_e pc_a pc_v lw r lregs tidx eid (is_cur : bool) :
    decodeInstrWL lw = EDeInit r →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EDeInit r) ⊆ dom lregs →
    (* EC register does not decrement (i.e. it acts as a bump allocator) *)

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
          (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
          if is_cur
          then enclave_cur tidx eid
          else enclave_prev tidx
    }}}
      Instr Executable @ E
    {{{ lregs' retv, RET retv;
        ⌜ EDeInit_spec lregs lregs' r tidx eid is_cur retv⌝ ∗
        enclave_prev tidx ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hrmap & Hpca & Hofrag) Hφ".

    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hrmap $Hpca Hφ Hofrag]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hrmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) _".

    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.

    iApply (wp_wp2
              (φ1 :=
                 lwr ← (reg σ1) !! r; (* σ should be a seal/unseal pair *)
                 '(p,σb,σe,_) ← get_sealing_cap lwr;
                 if decide ((bool_decide (p = (true,true))) && (σe =? σb^+2)%ot) then
                   let tidx := tid_of_otype σb in
                   eid  ← (etable σ1) !! tidx;
                   (* etable' ← remove_from_etable σ1 tidx; *)
                   _
                 (*   incrementLPC lregs *)
                 (* else None *)
                 else None
              )).
    iModIntro.

    destruct is_cur.

    iDestruct (enclave_update_deinit tidx eid with "Hσ1 Hofrag") as "Hprev".
    (* missing the state interp here, need to return it since we are mod. the auth parts too... *)
    admit.
    iDestruct "Hσ1" as "(%lr & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hrmap") as "%Hlrsub".
    iCombine "Hlr Hlm Hrmap" as "Hσ".
    iDestruct (transiently_intro with "Hσ") as "Hσ".


    iApply wp_opt2_bind.
    iApply wp2_diag_univ.
    iSplit.
    { iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)".
      iSplitR "Hφ Hregs Hpc_a Hofrag".
      - iExists lr, lm, vmap, _, _, _; now iFrame.
      - iApply ("Hφ" with "[$Hregs $Hpc_a Hofrag]"). iSplit. iPureIntro.
        apply EDeInit_failure; auto. constructor 2.
        iFrame. }

    iIntros (lwr).
    iApply wp_opt2_bind.
    iApply wp2_diag_univ.
    iSplit.
    { admit. }
    iIntros (seal). destruct seal as ((([permitSeal permitUnseal] & σb) & σe) & σa).

    (* annoying. *)
    destruct (bool_decide ((permitSeal, permitUnseal) = (true, true)) && (σe =? (σb ^+ 2)%f)%Z).
    1: {
      destruct (decide true). 2: by exfalso. (* hmmm *)

      wp2_remember.
      iApply wp_opt2_mono2.
      iSplitR "".

      2: admit.
      (* ... *)

      iSplit.
      1: admit.

      (* have to remove the index in the table... *)
      iIntros (leid lhash) "_ Hlookup %Hrem".
      (* rewrite updatePC_incrementPC. *)
      (* wp2_remember. *)

      admit.
    }
    { destruct (decide false); try by exfalso.
      Search (wp_opt2 ?X ?X).
      iApply wp2_diag_univ.
      admit.
    }

  Admitted.
    (*   (* have to remove the index in the table... *) *)
    (*   rewrite updatePC_incrementPC. *)
    (*   wp2_remember. *)

    (*   iApply wp_opt2_mono2. *)

    (*   iSplitR "Hσ". *)
    (*   2: { *)
    (*     (* iMod "Hσ" as "(Hσr & Hσm & Hregs)". *) *)

    (*     iApply wp_opt2_bind. *)
    (*     unfold remove_from_etable. *)
    (*     destruct σ1. *)
    (*     cbn. *)
    (*     Search (wp_opt2 _ (incrementPC _)). *)

    (*     iApply wp2_diag_univ. *)
    (*     iApply wp2_opt_incrementPC. with "[Hσr Hregs]"); eauto. *)
    (*     eapply dom_insert_subseteq, elem_of_dom_2, HPC. *)
    (*     eapply (state_phys_log_corresponds_update_reg (lw := LInt lhash) eq_refl); cbn; eauto. } *)
    (*   Search incrementPC. *)
    (*   admit. } *)

    (* { (* σe ≠ σb + 2 *) *)
    (*   cbn. *)
    (*   Search (if _ then _ else _). *)
    (*   erewrite decide_False. *)
    (*   2: easy. *)
    (*   iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)". *)
    (*   iApply wp2_diag_univ. *)
    (*   iSplit. *)
    (*   iSplitR "Hφ Hregs Hpc_a Hofrag". *)
    (*   - iExists lr, lm, vmap, _, _, _; now iFrame. *)
    (*   - iApply ("Hφ" with "[$Hregs $Hpc_a Hofrag]"). iSplit. iPureIntro. *)
    (*     apply EDeInit_failure; auto. constructor 2. *)
    (*     destruct is_cur; iFrame. admit. *)
    (*   - admit. } *)

    (* { (* permitSeal and/or permitUnseal were not set *) *)
    (*   cbn. *)
    (*   erewrite decide_False. *)
    (*   2: easy. *)
    (*   iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs)". *)
    (*   iSplitR "Hφ Hregs Hpc_a Hofrag". *)
    (*   - iExists lr, lm, vmap, _, _, _; now iFrame. *)
    (*   - iApply ("Hφ" with "[$Hregs $Hpc_a Hofrag]"). iSplit. iPureIntro. *)
    (*     apply EDeInit_failure; auto. constructor 2. *)
    (*     destruct is_cur; iFrame. admit. } *)






   (*  iIntros (Hinstr Hvpc φ) "[Hpc Hpca] Hφ". *)
   (*  apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc. *)
   (*  iApply wp_lift_atomic_head_step_no_fork; auto. *)
   (*  iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
   (*  iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv. *)
   (*  iDestruct (@gen_heap_valid with "Hr Hpc") as %?. *)
   (*  iDestruct (@gen_heap_valid with "Hm Hpca") as %?. *)
   (*  iModIntro. *)
   (*  iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
   (*  iIntros (e2 σ2 efs Hstep). *)
   (*  apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)). *)
   (*  iNext; iIntros "_". *)
   (*  iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)
   (*  2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v))) *)
   (*  ; eapply state_corresponds_reg_get_word ; eauto. *)
   (*  2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
   (*  cbn in Hstep; simplify_eq. *)
   (*  iModIntro. *)
   (*  iSplitR "Hφ Hpc Hpca"; last (iApply "Hφ" ; iFrame). *)
   (*  iExists lr, lm, vmap. *)
   (*  iFrame; auto. *)
   (* Qed. *)

End cap_lang_rules.
