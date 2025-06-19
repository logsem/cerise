From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
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

  Inductive EInit_fail (lregs : LReg) (lmem : LMem) (r_code r_data : RegName) (tidx : TIndex) (ot : OType) : Prop :=
  (* the code register is PC *)
  | EInit_fail_rcode_is_pc :
    r_code = PC ->
    EInit_fail lregs lmem r_code r_data tidx ot
  (* the code register doesn't contain a capability *)
  | EInit_fail_ccap_not_a_cap lw :
    lregs !! r_code = Some lw ->
    is_log_cap lw = false →
    EInit_fail lregs lmem r_code r_data tidx ot
  (* the code capability is not RX *)
  | EInit_fail_ccap_no_rx p b e a v :
    lregs !! r_code = Some (LCap p b e a v) ->
    p ≠ RX ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the code capability does not contain enough space for the data capability *)
  | EInit_fail_ccap_small p b e a v :
    lregs !! r_code = Some (LCap p b e a v) ->
    ¬ (b < e)%a ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the hashing fails *)
  | EInit_fail_hash_fail p b e a v :
    lregs !! r_code = Some (LCap p b e a v) ->
    (b < e)%a ->
    (hash_lmemory_range lmem (b ^+ 1)%a e v) = None ->
    EInit_fail lregs lmem  r_code r_data tidx ot

  (* the data register doesn't contain a capability *)
  | EInit_fail_dcap_not_a_cap lw :
    lregs !! r_data = Some lw ->
    is_log_cap lw = false →
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the data capability is not RW *)
  | EInit_fail_dcap_no_rw p b e a v :
    lregs !! r_data = Some (LCap p b e a v)->
    p ≠ RW ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the data capability does not contain enough space for the data capability *)
  | EInit_fail_dcap_small p b e a v :
    lregs !! r_data = Some (LCap p b e a v) ->
    ¬ (b < e)%a ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* One of the sweeps fail... *)
  | EInit_fail_ccap_dcap_not_unique p b e a v p' b' e' a' v' :
    (* TODO: probably missing assumptions *)
    lregs !! r_code = Some (LCap p b e a v) ->
    lregs !! r_data = Some (LCap p' b' e' a' v')->
    EInit_fail lregs lmem r_code r_data tidx ot
  (* Casting to bounded Z fails (max enum exceeded?) *)
  | EInit_fail_enum_bound_exceeded {zB} z :
    @finz.of_z zB z = None →
    EInit_fail lregs lmem r_code r_data tidx ot
  (* the PCC overflows *)
  | EInit_fail_pc_overflow
     b_code e_code a_code v_code
     b_data e_data a_data v_data :
    lregs !! r_code = Some (LCap RX b_code e_code a_code v_code) ->
    lregs !! r_data = Some (LCap RW b_data e_data a_data v_data) ->
    incrementLPC (
        <[ r_data := LWInt 0 ]>
          (<[ r_code := next_version_lword (LCap E b_code e_code (b_code ^+ 1)%a v_code)]>
             lregs)) = None →
    EInit_fail lregs lmem  r_code r_data tidx ot

  | EInit_fail_otype_overflow :
    tid_of_otype ot = tidx ->
    Z.even ot = true ->
    (ot + 2)%ot = None →

    EInit_fail lregs lmem  r_code r_data tidx ot.

    (* | EInit_fail_ccap_not_unique : *)
    (*   EInit_fail lregs lmem ot *)
    (* | EInit_fail_dcap_not_unique : *)
    (*   EInit_fail lregs lmem ot *)
    (* | EInit_fail_dcap_not_a_cap : *)
    (*   EInit_fail lregs lmem ot *)
    (* | EInit_fail_dcap_no_rw : *)
    (*   EInit_fail lregs lmem ot. *)

  Definition EInit_spec_success (lregs lregs' : LReg) (lmem lmem' : LMem) (tidx tidx_incr : TIndex)
    (ot : OType) (r_code r_data : RegName) (retv : val) : iProp Σ :=
    ∃ glmem lmem'' (code_b code_e code_a : Addr) (code_v : Version) (data_b data_e data_a : Addr)
      (data_v : Version) eid hash_instrs,
    ⌜r_code ≠ PC⌝ ∗
    ⌜(tidx+1)%nat = tidx_incr⌝ ∗
    ⌜tid_of_otype ot = tidx⌝ ∗
    ⌜Z.even ot = true⌝ ∗
    ⌜ (hash_lmemory_range lmem (code_b ^+ 1)%a code_e code_v) = Some hash_instrs
    ∧ hash_concat (hash code_b) hash_instrs = eid⌝ ∗ (* eid = hash(code_b || mem[b+1::e]) *)
    ⌜(ot + 2)%ot = Some (ot ^+ 2)%ot ⌝ ∗ (* there are still otypes left in the pool *)
    ⌜lregs !! r_code = Some (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* rcode contains a valid code capability *)
    ⌜lregs !! r_data = Some (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* rdata contains a valid data capability *)
    ⌜ (code_b < code_e)%a ⌝ ∗ (* the code capability contains at least one address *)
    ⌜ (data_b < data_e)%a ⌝ ∗ (* the data capability contains at least one address *)
    ⌜ is_valid_updated_lmemory glmem lmem (finz.seq_between code_b code_e) code_v lmem'' ⌝ ∗ (* all memory in the code capability is "current" w.r.t. revocation *)
    ⌜ is_valid_updated_lmemory glmem lmem (finz.seq_between data_b data_e) data_v lmem'' ⌝ ∗ (* all memory in the data capability is "current" w.r.t. revocation *)
    ⌜ lmem' =
    <[ ( data_b, (data_v+1)%nat ) := (LSealRange (true,true) ot (ot ^+ 2)%ot ot ) ]>
      (<[ (code_b, (code_v+1)%nat ) := (LCap RW data_b data_e data_a (data_v + 1)%nat) ]> lmem'') ⌝ ∗
    ⌜unique_in_registersL lregs (Some r_code) (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* the code capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜unique_in_registersL lregs (Some r_data) (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* the data capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜ map_Forall (fun la lw => (laddr_get_addr la) ∈ (finz.seq_between (code_b ^+ 1)%a code_e) -> is_zL lw) lmem ⌝ ∗
    ⌜ (finz.seq_between code_b code_e) ## reserved_addresses ⌝ ∗
    ⌜ (finz.seq_between data_b data_e) ## reserved_addresses ⌝ ∗
    ⌜incrementLPC (
        <[ r_data := LWInt 0 ]>
          (<[ r_code := next_version_lword (LCap E code_b code_e (code_b ^+ 1)%a code_v)]>
             lregs)) = Some lregs' ⌝ ∗ (* the pc will be incremented and rs will point to a "current" sentry capability *)
    ⌜ retv = NextIV ⌝ ∗
      enclave_cur tidx eid (* non-dup token asserting ownership over the enclave at etable index `tidx` *)
      ∗ enclave_all tidx eid (* dup token asserting ownership over the enclave at etable index `tidx` *)

  .

  Definition EInit_spec_failure
    (lregs : LReg) (lmem : LMem) (r_code r_data : RegName) (tidx : TIndex) (ot : OType) : iProp Σ :=
    ⌜ EInit_fail lregs lmem r_code r_data tidx ot ⌝.

  Definition allows_einit_memory (lregs : LReg) (lmem : LMem) (r : RegName) :=
    ∀ p b e a v,
    lregs !! r = Some (LCap p b e a v)
    -> readAllowed p = true
       (* lmem must include at least those addresses in the r_code cap *)
    -> Forall (fun a => is_Some (lmem !! (a, v))) (finz.seq_between b e).

  Definition allows_einit (lregs : LReg) (r : RegName) :=
    ∀ p b e a v,
    lregs !! r = Some (LCap p b e a v)
    -> readAllowed p = true
    -> (finz.seq_between b e) ## reserved_addresses.

  Definition lmeasure (m : LMem) (b e: Addr) v : option Z :=
    hash_instr ← hash_lmemory_range m (b^+1)%a e v;
    Some (hash_concat (hash b) hash_instr).

  Lemma lmeasure_weaken {lmem lmt} {b e v} :
    lmem ⊆ lmt →
    Forall (fun a => is_Some (lmem !! (a, v))) (finz.seq_between b e) →
    hash_lmemory_range lmem b e v = hash_lmemory_range lmt b e v.
  Admitted.

  Definition exec_optL_EInit {A}
    (lregs : LReg) (lmem : LMem)
    (r1 r2 :  RegName) (code_sweep data_sweep : bool)
    (m : Mem) (ec : ENum) {zB : Z}
    (kont : LReg → option A) : option A.
    refine (
    if decide (negb (bool_decide (r1 = PC))) then
      ccap          ← lregs !! r1;
      '(p, b, e, _, v) ← lword_get_cap ccap;
      if decide (p = RX) then
        if decide (b < e)%a then
          dcap          ← lregs !! r2;
          '(p', b', e', _) ← get_wcap (lword_get_word dcap);
          if decide (p' = RW) then
            if decide (b' < e')%a then
              if decide (code_sweep && data_sweep && (ensures_no_cap m (b ^+ 1)%a e)) then
                s_b ← @finz.of_z zB (2 * Z.of_nat ec)%Z ;
                s_e ← @finz.of_z zB (2 * Z.of_nat ec + 2)%Z ;
                eid ← lmeasure lmem b e v;
                newPC ← incrementLPC (<[r2 := LInt 0]> (<[r1 := (LCap machine_base.E b e (b ^+ 1)%a (v+1))]> lregs));
                kont newPC (* missing stuff from below.. *)
                     (* (update_reg *)
                     (*    (update_reg *)
                     (*       (update_enumcur *)
                     (*          (update_etable *)
                     (*             (update_mem (update_mem σ f2 (WSealRange (true, true) s_b s_e s_b)) f (WCap p0 f2 f3 f4)) *)
                     (*             (enumcur σ) eid) (enumcur σ + 1)) r_code (WCap machine_base.E f f0 (f ^+ 1)%a)) r_data *)
                     (*    (WInt 0)) *)

                     (* φ  |>> update_mem b' seals    (* store seals at base address of enclave's data section *) *)
                     (*    |>> update_mem b dcap      (* store dcap at base address of enclave's code section *) *)
                     (*    |>> update_etable (enumcur φ) eid (* create a new index in the ETable *) *)
                     (*    |>> update_enumcur ((enumcur φ)+1)  (* increment EC := EC + 1 *) *)
                     (*    |>> update_reg r1 (WCap E b e (b^+1)%a) (* Position cursor at address b+1: entry point always at base address *) *)
                     (*    |>> update_reg r2 (WInt 0) (* Erase the supplied dcap from r2 *) *)
                     (*    |>> updatePC *)

              else None
            else None
          else None
        else None
      else None
    else None).
    Defined.

  Lemma wp_einit E pc_p pc_b pc_e pc_a pc_v lw lregs lmem tidx r_code r_data :
    decodeInstrWL lw = EInit r_code r_data →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EInit r_code r_data) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allows_einit lregs r_code →
    allows_einit lregs r_data →
    allows_einit_memory lregs lmem r_code →
    {{{
          (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
          (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          EC⤇ tidx
    }}}
      Instr Executable @ E
    {{{ lregs' lmem' retv tidx' ot, RET retv;
        ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        EC⤇ tidx' ∗

        ( EInit_spec_success lregs lregs' lmem lmem' tidx tidx' ot r_code r_data retv
         ∨ (
           EInit_spec_failure lregs lmem r_code r_data tidx ot
           ∗ ⌜ lmem' = lmem ⌝
           ∗ ⌜ tidx' = tidx ⌝
           ∗ ⌜ retv = FailedV ⌝
           )
        )
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HrcodeAllowEInit HrdataAllowEInit HallowsMemory φ) "(>Hregs & >Hmem & HECv) Hφ".
    (*  extract the pc  *)
    rewrite (big_sepM_delete _ lmem). 2: apply Hmem_pc. iDestruct "Hmem" as "[Hpc_a Hmem]".
    (* iApply wp_lift_atomic_head_step_no_fork; auto. *)
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hregs $Hpc_a Hmem Hφ HECv]").
    iModIntro.

    iIntros (σ) "(Hσ & Hregs & Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) _".
    iCombine "Hpc_a Hmem" as "Hmem".
    rewrite -(big_sepM_delete (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y) _ _ _ Hmem_pc).

    set (code_sweep := (sweep_reg (mem σ) (reg σ) r_code)).
    set (data_sweep := (sweep_reg (mem σ) (reg σ) r_data)).


    iApply (wp_wp2 (φ1 := exec_optL_EInit lregs lmem r_code r_data code_sweep data_sweep (mem σ) (enumcur σ) _) (φ2 := _)).
    iModIntro.

    unfold exec_optL_EInit.

    (* split on whether code cap register is PC... *)
    destruct (decide (negb (bool_decide (r_code = PC)))) eqn:Hpc_eq; cbn in *; simplify_eq; rewrite Hpc_eq; clear Hpc_eq.
    all: revgoals.
    { (* case where they are equal: crash the machine *)
      unfold wp_opt2.
      unfold exec_optL_EInit.
      iModIntro.
      iFrame.
      iApply "Hφ". iFrame.
      iRight.
      iSplit. iPureIntro. constructor 1.
      - by apply negb_prop_classical, bool_decide_unpack in n.
      - easy. }

    (* regular path: PC does not equal r_code *)
    (* intro transient modality *)

    iDestruct (state_interp_transient_intro_nodfracs (lr := lregs) (lm := lmem) with "[$Hregs $Hσ $Hmem]") as "Hσ".

    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ HECv]"); first by set_solver.
    iIntros (lccap) "Hσ %Hlccap %Hccap".

    iApply wp_opt2_bind.

    unfold lword_get_cap.
    destruct lccap eqn:Hccap_shape; cbn.

    (* why can't I use multi-goal selectors with curly braces? *)
    1: {
      iModIntro.
      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_not_a_cap.
    }
    2: {
      iModIntro.
      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_not_a_cap.
    }

    destruct sb eqn:Hsb_shape; cbn.
    2: {
      iModIntro.
      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_not_a_cap.
    }

    iModIntro.
    destruct (decide (p = RX)).

    2: { (* we do not have RX permissions for ccap. *)
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_no_rx. }

    destruct (decide (f < f0)%a).
    2: { (* ccap is too small to store dcap at address b *)
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_small. }

    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ HECv]"); first by set_solver.
    iIntros (ldcap) "Hσ %Hldcap %Hdcap".

    unfold get_wcap.
    destruct ldcap eqn:Hdcap_shape; cbn.
    1: {
      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_dcap_not_a_cap.
    }

    (* is DCAP a cap? *)
    destruct sb0 eqn:Hsb0_shape; cbn.

    2: {

      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      Search "EInit_fail_dcap".
      by eapply EInit_fail_dcap_not_a_cap.
    }

    2: {

      iIntros.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      Search "EInit_fail_dcap".
      by eapply EInit_fail_dcap_not_a_cap.
    }

    (* DCAP is now definitely a cap *)


    (* Does DCAP have the right perms? *)
    destruct (decide (p0 = RW)).

    2: {
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_dcap_no_rw. }

    destruct (decide (f2 < f3)%a).
    2: { (* dcap is too small to store seals at address b' *)
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_dcap_small. }

    destruct code_sweep eqn:Hcode_sweep; cbn.

    2: {
      (* code sweep was not successful. *)
      unfold code_sweep in Hcode_sweep.
      rewrite Hcode_sweep.
      repeat rewrite andb_false_l.
      erewrite !(decide_False (H := Is_true_dec false)); eauto.
      iModIntro.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_dcap_not_unique. }

    destruct data_sweep eqn:Hdata_sweep; cbn.

    2: {
      (* data sweep was not successful. *)
      unfold data_sweep in Hdata_sweep.
      unfold code_sweep in Hcode_sweep.
      rewrite Hcode_sweep Hdata_sweep.
      rewrite andb_true_l.
      repeat rewrite andb_false_l.
      erewrite !(decide_False (H := Is_true_dec false)); eauto.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
      iApply "Hφ". iFrame.
      iRight. iModIntro. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_dcap_not_unique. }

    (* Both CCAP and DCAP sweeps have succeeded, now to ensure no caps exist in CAP.. *)

      unfold data_sweep, code_sweep in *.
      rewrite Hcode_sweep Hdata_sweep !andb_true_l.

      destruct (decide (ensures_no_cap (mem σ) (f ^+ 1)%a f0)).

      2: {
        (* no caps sweep was not successful. *)
        unfold data_sweep in Hdata_sweep.
        unfold code_sweep in Hcode_sweep.
        destruct (decide false). (* why doesn't this reduce ??? *)
        { cbn in i0. by exfalso. }
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
        iApply "Hφ". iFrame.
        iRight. iModIntro. iSplit; try easy. iPureIntro.
        by eapply EInit_fail_ccap_dcap_not_unique. }

      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_diag_univ.
      iSplit.
      1: {
        iIntros.
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
        iApply "Hφ". iFrame.
        iRight. iSplit; try easy. iPureIntro.
        by eapply EInit_fail_enum_bound_exceeded. }

      iIntros (s_b) "%Hs_b _".

      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_diag_univ.
      iSplit.
      1: {
        iIntros.
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
        iApply "Hφ". iFrame.
        iRight. iSplit; try easy. iPureIntro.
        by eapply EInit_fail_enum_bound_exceeded. }

      iIntros (s_e) "%Hs_e _".

      subst.

      (* measure the enclave footprint *)

      iApply wp_opt2_bind.
      iApply wp_opt2_eqn_both.
      iDestruct (state_interp_transient_corr with "Hσ") as "%".
      destruct H as (lrt & lmt & vm & Hlrt & Hlmt & Hcorr).
      assert (lmem ⊆ lmt). admit.
      unfold measure at 1, lmeasure at 1.

      erewrite lmeasure_weaken.
      2,3: eauto; try eapply HallowsMemory; admit.

      erewrite (lmeasure_measure _ (mem σ)).
      2: {
        eapply (is_cur_lword_lea vm RX RX f (f ^+ 1)%a f0 f0 _ _ _ (LCap RX f f0 _ _)).
        rewrite Is_true_true.
        apply isWithin_of_le.
        solve_addr.
        all: try easy.

        eapply lreg_corresponds_read_iscur.
        by destruct Hcorr.
        by eapply lookup_weaken in Hlccap. }

      2: eauto.
      iApply wp2_diag_univ.
      iSplit.

      1: {
        iIntros "%Hhash _".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". rewrite big_sepM_fmap. cbn.
        iApply "Hφ". iFrame.
      iRight. iSplit; try easy. iPureIntro.
      eapply EInit_fail_hash_fail.
      - apply Hlccap.
      - apply l.
      - unfold lmeasure in Hhash.
        destruct (hash_lmemory_range lmem (f ^+ 1)%a f0 v).
        discriminate Hhash. exact eq_refl.
      }

      iIntros (eid) "%Hlhash %Hhash".
      rewrite updatePC_incrementPC.
      cbn.
      iApply wp2_opt_incrementPC; eauto.

  Admitted.

End cap_lang_rules.
