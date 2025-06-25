From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From iris.algebra.lib Require Import excl_auth.
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
  | EInit_fail_enum_bound_exceeded :
    @finz.of_z _ (2 * tidx) = (None : option OType) →
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

  Definition ensures_is_zL lmem b e v : Prop :=
    map_Forall (fun la lw => (laddr_get_addr la) ∈ (finz.seq_between b e) ∧ (laddr_get_version la) = v
                          -> is_zL lw) lmem.

  Lemma ensures_is_z_corresponds {phr phm lr lm vmap} {r} {p} {b e a} {v} :
    state_phys_log_corresponds phr phm lr lm vmap →
    is_cur_word (LCap p b e a v) vmap ->
    ensures_is_z phm b e →
    ensures_is_zL lm b e v.
  Proof.
    intros Hcorr Hr Hensure_z.
    rewrite /ensures_is_zL.
    rewrite /ensures_is_z in Hensure_z.
    apply bool_decide_unpack in Hensure_z.
    destruct Hcorr as [ Hreg (? & ? & ?) ].
    rewrite /is_cur_word in Hr.
    rewrite /mem_vmap_root in H0.
    rewrite /mem_current_version in H.
    rewrite map_Forall_lookup in H.
    rewrite map_Forall_lookup.
    intros [a' v'] lw Hla [Hla_in ?]; cbn in *; simplify_eq.
    specialize (Hr a' Hla_in).
    rewrite map_Forall_lookup in H0; eauto.
    eapply H0 in Hr.
    destruct Hr as (?&?&?&?); cbn in *.
    rewrite map_Forall_lookup in Hensure_z; eauto.
    rewrite H2 in Hla; simplify_eq.
    apply Hensure_z in H3; eauto.
    destruct lw ; eauto.
  Qed.

  Lemma ensures_is_z_mono {lm lm'} {b e} {v}  :
    lm ⊆ lm' →
    ensures_is_zL lm' b e v -> ensures_is_zL lm b e v.
  Proof.
    intros Hsub Hensure_is_zL.
    rewrite /ensures_is_zL in Hensure_is_zL |- *.
    rewrite map_Forall_lookup.
    intros [a v'] lw Hla [Hin ?] ; cbn in *; simplify_eq.
    eapply lookup_weaken in Hla; eauto.
  Qed.

  Definition EInit_spec_success (lregs lregs' : LReg) (lmem1 lmem4 : LMem) (tidx tidx_incr : TIndex)
    (ot : OType) (r_code r_data : RegName) (retv : val) : iProp Σ :=
    ∃ glmem lmem2 lmem3 (code_b code_e code_a : Addr) (code_v : Version) (data_b data_e data_a : Addr)
      (data_v : Version) eid hash_instrs,
    ⌜r_code ≠ PC⌝ ∗
    ⌜(tidx+1)%nat = tidx_incr⌝ ∗
    ⌜tid_of_otype ot = tidx⌝ ∗
    ⌜Z.even ot = true⌝ ∗
    ⌜ (hash_lmemory_range lmem1 (code_b ^+ 1)%a code_e code_v) = Some hash_instrs
    ∧ hash_concat (hash code_b) hash_instrs = eid⌝ ∗ (* eid = hash(code_b || mem[b+1::e]) *)
    ⌜(ot + 2)%ot = Some (ot ^+ 2)%ot ⌝ ∗ (* there are still otypes left in the pool *)
    ⌜lregs !! r_code = Some (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* rcode contains a valid code capability *)
    ⌜lregs !! r_data = Some (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* rdata contains a valid data capability *)
    ⌜ (code_b < code_e)%a ⌝ ∗ (* the code capability contains at least one address *)
    ⌜ (data_b < data_e)%a ⌝ ∗ (* the data capability contains at least one address *)
    ⌜ is_valid_updated_lmemory glmem lmem1 (finz.seq_between data_b data_e) data_v lmem2 ⌝ ∗ (* all memory in the data capability is "current" w.r.t. revocation *)
    ⌜ is_valid_updated_lmemory (update_version_region glmem (finz.seq_between data_b data_e) data_v glmem) lmem2 (finz.seq_between code_b code_e) code_v lmem3 ⌝ ∗ (* all memory in the code capability is "current" w.r.t. revocation *)
    ⌜ lmem4 =
    <[ ( data_b, (data_v+1)%nat ) := (LSealRange (true,true) ot (ot ^+ 2)%ot ot ) ]>
      (<[ (code_b, (code_v+1)%nat ) := (LCap RW data_b data_e data_a (data_v + 1)%nat) ]> lmem3) ⌝ ∗
    ⌜unique_in_registersL lregs (Some r_code) (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* the code capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜unique_in_registersL lregs (Some r_data) (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* the data capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜ ensures_is_zL lmem1 (code_b ^+ 1)%a code_e code_v ⌝ ∗
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

  Definition allows_einit_memory (lregs : LReg) (lmem : LMem) (pc_a : Addr) (r : RegName) :=
    ∀ b e a v,
    lregs !! r = Some (LCap RX b e a v)
    -> pc_a ∉ finz.seq_between b e
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


  Lemma lmeasure_weaken_aux (lmem lmt: LMem) (la : list Addr) (v : Version) :
    lmem ⊆ lmt →
    Forall (fun a => is_Some (lmem !! (a, v))) la →
    lmemory_get_instrs lmem la v = lmemory_get_instrs lmt la v.
  Proof.
    intros Hincl Hall.
    induction la ; first done.
    rewrite Forall_cons in Hall. destruct Hall as [ [w Ha] Hall].
    apply IHla in Hall.
    assert (lmt !! (a, v) = Some w) as Ha' by (eapply lookup_weaken in Ha ; eauto).
    cbn.
    rewrite -/(lmemory_get_instrs lmem la v) -/(lmemory_get_instrs lmt la v).
    by rewrite Ha Ha' Hall.
  Qed.

  Lemma lmeasure_weaken {lmem lmt} {b e v} :
    lmem ⊆ lmt →
    Forall (fun a => is_Some (lmem !! (a, v))) (finz.seq_between b e) →
    hash_lmemory_range lmem b e v = hash_lmemory_range lmt b e v.
  Proof.
    intros Hincl Hall.
    rewrite /hash_lmemory_range.
    erewrite lmeasure_weaken_aux; eauto.
  Qed.

  Lemma sweep_implies_no_pc {σ p pc_b pc_e pc_a r a v} b e :
    reg σ !! PC = Some (WCap p pc_b pc_e pc_a)
    → reg σ !! r = Some (WCap RX b e a)
    → sweep_reg (mem σ) (reg σ) r = true
    → r ≠ PC
    -> pc_a ∈ finz.seq_between pc_b pc_e
    → pc_a ∉ finz.seq_between b e.
  Proof.
    intros Hpc Hr Hsweep Hinbouds pcHrpc.
    unfold sweep_reg, sweep_memory_reg, sweep_registers_reg in Hsweep.
    rewrite Hr in Hsweep.
    rewrite andb_true_iff in Hsweep.
    destruct Hsweep as [_ Hsweep].
    unfold unique_in_registers in *.
    rewrite bool_decide_eq_true in Hsweep.
    rewrite map_Forall_lookup in Hsweep.
    eapply Hsweep in Hpc.
    destruct (decide (PC = r)); eauto.
    apply overlap_word_disjoint in Hpc.
    intro Hpca.
    eapply elem_of_disjoint; eauto.
  Qed.

  Lemma update_version_region_insert (a : Addr) (la : list Addr) (v v' : Version) (lw : LWord) (glmem llmem : LMem ) :
    a ∉ la ->
    (<[(a, v):= lw]> (update_version_region glmem la v' llmem)) =
    (update_version_region (<[(a, v):= lw]> glmem) la v' (<[(a, v):= lw]> llmem)).
  Proof.
    revert a v v' lw glmem llmem.
    induction la; intros a' v v' lw glmem llmem Ha'; first set_solver.
    cbn.
    rewrite -/(update_version_region glmem la v' llmem).
    rewrite -/(update_version_region (<[(a', v):=lw]> glmem) la v' (<[(a', v):=lw]> llmem)).
    rewrite /update_version_addr.
    rewrite lookup_insert_ne; last (intro; simplify_eq; set_solver).
    destruct ( glmem !! (a, v') ) eqn:Ha_glmem; rewrite Ha_glmem.
    - rewrite insert_commute; last (intro; simplify_eq; set_solver).
      rewrite IHla; set_solver.
    - rewrite IHla; set_solver.
  Qed.

  Definition exec_optL_EInit {A}
    (lregs : LReg) (lmem : LMem)
    (r1 r2 :  RegName) (code_sweep data_sweep : bool)
    (m : Mem) (ec : ENum) {zB : Z}
    (kont : LReg → option A) : option A.
    refine (
    if negb (bool_decide (r1 = PC)) then
      ccap          ← lregs !! r1;
      '(p, b, e, _, v) ← lword_get_cap ccap;
      if decide (p = RX) then
        if decide (b < e)%a then
          dcap          ← lregs !! r2;
          '(p', b', e', _ , _) ← lword_get_cap dcap;
          if decide (p' = RW) then
            if decide (b' < e')%a then
              if decide (code_sweep && data_sweep && (ensures_is_z m (b ^+ 1)%a e)) then
                s_b ← @finz.of_z zB (2 * Z.of_nat ec)%Z ;
                s_e ← @finz.of_z zB (2 * Z.of_nat ec + 2)%Z ;
                eid ← lmeasure lmem b e v;
                lregs' ← incrementLPC (<[r2 := LInt 0]> (<[r1 := (LCap machine_base.E b e (b ^+ 1)%a (v+1))]> lregs));
                kont lregs' (* missing stuff from below.. *)
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
    allows_einit_memory lregs lmem pc_a r_code →
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
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hregs $Hpc_a Hmem Hφ HECv]").
    iModIntro.

    iIntros (σ) "(Hσ & Hregs & Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) _".
    iCombine "Hpc_a Hmem" as "Hmem".
    rewrite -(big_sepM_delete (fun x y => mapsto x (DfracOwn 1) y) _ _ _ Hmem_pc).

    set (code_sweep := (sweep_reg (mem σ) (reg σ) r_code)).
    set (data_sweep := (sweep_reg (mem σ) (reg σ) r_data)).


    iApply (wp_wp2 (φ1 := exec_optL_EInit lregs lmem r_code r_data code_sweep data_sweep (mem σ) (enumcur σ) _)).
    iModIntro.

    unfold exec_optL_EInit.

    (* split on whether code cap register is PC... *)
    destruct (negb (bool_decide (r_code = PC))) eqn:Hpc_eqb; cbn in *; simplify_eq; rewrite Hpc_eqb.
    all: revgoals.
    { (* case where they are equal: crash the machine *)
      iModIntro.
      iFrame "Hσ".
      iApply "Hφ". iFrame.
      iRight.
      iSplit; last easy.
      iPureIntro.
      constructor 1.
      now apply negb_false_iff, Is_true_true, bool_decide_unpack in Hpc_eqb.
    }
    assert ( r_code ≠ PC ) as Hpc_neq_code by (intro; simplify_eq).

    (* regular path: PC does not equal r_code *)
    (* intro transient modality *)

    iDestruct "Hσ" as "(%lr & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)".

    iAssert (⌜enumcur σ = tidx⌝)%I as "%HEC".
    { iDestruct (own_valid_2 with "Hecauth HECv") as "%HEC_valid".
      by apply excl_auth.excl_auth_agree_L in HEC_valid. }

    (* derive frag ⊆ auth *)
    iDestruct (gen_heap_valid_inclSepM with "Hlm Hmem") as "%Hlmsub".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hregs") as "%Hlrsub".
    iCombine "Hlr Hlm Hregs Hmem Hcur_tb Hall_tb Hecauth HECv" as "Hσ".

    iDestruct (transiently_intro with "Hσ") as "Hσ".

    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply wp_opt2_mono2.
    iSplitR "".
    2: { iApply wp2_reg_lookup5; eauto. set_solver. }
    iSplit; first now iIntros "%Htr".

    iIntros (lccap ccap) "-> %Hlccap %Hccap".

    iApply wp_opt2_bind. iApply wp_opt2_eqn_both.

    iApply wp2_word_get_cap; iSplit; iIntros.

    (* why can't I use multi-goal selectors with curly braces? *)
    (* domi: I think that might be an Ltac2 feature...*)
    1: {
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      { iExists lr, lm, vmap, _, _, _; now iFrame. }
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      eapply EInit_fail_ccap_not_a_cap; first done.
      apply is_log_cap_is_cap_false_iff.
      destruct (lword_get_word lccap) as [ | [ | ] | ]; (easy || now discriminate).
    }
    destruct lccap as [ | [ | ] | ]; cbn in *; inversion H; subst f f0 f1 p0 v0; clear H H0.

    destruct (decide (p = RX)).

    2: { (* we do not have RX permissions for ccap. *)
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_no_rx.
    }
    subst p.

    destruct (decide (b < e)%a).
    2: { (* ccap is too small to store dcap at address b *)
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_small.
    }

    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply wp_opt2_mono2.
    iSplitR "".
    2: { iApply wp2_reg_lookup5; eauto. set_solver. }
    iSplit; first now iIntros "%Htr".

    iIntros (ldcap dcap) "-> %Hldcap %Hdcap".

    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply wp2_word_get_cap.
    iSplit; iIntros.
    { iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      eapply EInit_fail_dcap_not_a_cap; first done.
      apply is_log_cap_is_cap_false_iff.
      destruct (lword_get_word ldcap) as [ | [ | ] | ]; (easy || now discriminate).
    }
    (* DCAP is now definitely a cap *)
    destruct ldcap as [ | [ | ] | ]; cbn in *; inversion H; subst p0 f f0 f1 v1; clear H H0.



    (* Does DCAP have the right perms? *)
    destruct (decide (p = RW)).

    2: {
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_dcap_no_rw. }
    subst p.

    destruct (decide (b0 < e0)%a).
    2: { (* dcap is too small to store seals at address b' *)
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_dcap_small. }

    destruct code_sweep eqn:Hcode_sweep; cbn.

    2: {
      (* code sweep was not successful. *)
      unfold code_sweep in Hcode_sweep.
      rewrite Hcode_sweep.
      repeat rewrite andb_false_l.
      erewrite !(decide_False (H := Is_true_dec false)); eauto.
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
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
      iModIntro.
      iIntros.
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
      iSplitR "Hφ Hregs Hmem HECv".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
      iRight. iSplit; try easy. iPureIntro.
      by eapply EInit_fail_ccap_dcap_not_unique. }

    (* Both CCAP and DCAP sweeps have succeeded, now to ensure no caps exist in CAP.. *)


      unfold data_sweep, code_sweep in *.
      rewrite Hcode_sweep Hdata_sweep !andb_true_l.

      assert (r_code ≠ r_data) as Hneq_rcode_data by (intro ; simplify_map_eq).

      assert (Hcode_data_disjoint :
               (finz.seq_between b e) ## (finz.seq_between b0 e0)).
      { clear -Hneq_rcode_data Hccap Hdcap Hcode_sweep.
        unfold sweep_reg, sweep_memory_reg, sweep_registers_reg in Hcode_sweep.
        rewrite Hccap in Hcode_sweep.
        rewrite andb_true_iff in Hcode_sweep.
        destruct Hcode_sweep as [_ Hcode_sweep].
        unfold unique_in_registers in *.
        rewrite bool_decide_eq_true in Hcode_sweep.
        rewrite map_Forall_lookup in Hcode_sweep.
        eapply Hcode_sweep in Hdcap.
        destruct (decide (r_data = r_code)); eauto.
        simplify_eq.
        apply overlap_word_disjoint in Hdcap.
        done. }

      destruct (decide (ensures_is_z (mem σ) (b ^+ 1)%a e)).

      2: {
        (* no caps sweep was not successful. *)
        unfold data_sweep in Hdata_sweep.
        unfold code_sweep in Hcode_sweep.
        destruct (decide false). (* why doesn't this reduce ??? *)
        { cbn in i. by exfalso. }
        iModIntro.
        iIntros.
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        iSplitR "Hφ Hregs Hmem HECv".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
        iRight. iSplit; try easy. iPureIntro.
        by eapply EInit_fail_ccap_dcap_not_unique. }

      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_diag_univ.
      iSplit.
      1: {
        iIntros.
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        iSplitR "Hφ Hregs Hmem HECv".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
        iRight. iSplit; try easy. iPureIntro.
        eapply EInit_fail_enum_bound_exceeded.
        now rewrite -HEC.
      }

      iIntros (s_b) "%Hs_b _".
      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_diag_univ.
      iSplit.
      1: {
        iIntros.
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        iSplitR "Hφ Hregs Hmem HECv".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
        iRight. iSplit; try easy. iPureIntro.
        eapply (EInit_fail_otype_overflow _ _ _ _ _ s_b).
        + rewrite -HEC /tid_of_otype.
          clear -Hs_b.
          destruct (Z.even s_b) eqn:HZeven; cycle 1.
          { by apply finz_even_mul2 in Hs_b; rewrite Hs_b in HZeven. }
          replace (Z.to_nat s_b) with (2 * Z.to_nat (enumcur σ)) by solve_finz.
          apply finz_of_z_is_Some_spec in Hs_b.
          rewrite Nat.mul_comm Nat.div_mul; lia.
        + by eapply finz_even_mul2.
        + apply finz_of_z_is_Some_spec in Hs_b.
          rewrite -Hs_b in H.
          by eapply finz_of_z_add_None.
      }

      iIntros (s_e) "%Hs_e _".

      (* measure the enclave footprint *)

      iApply wp_opt2_bind.
      iApply wp_opt2_eqn_both.
      unfold measure at 1, lmeasure at 1.
      assert (Hpc_notin_code : pc_a ∉ (finz.seq_between b e)).
      {   eapply sweep_implies_no_pc; eauto.
          eapply isCorrectPC_le_addr in Hcorrpc.
          rewrite elem_of_finz_seq_between; solve_addr. }

      erewrite lmeasure_weaken; eauto.
      2: {
        eapply incl_Forall; cycle 1.
        eapply HallowsMemory; eauto.
        rewrite /incl.
        intros a' HIna'.
        rewrite -!elem_of_list_In !elem_of_finz_seq_between in HIna' |- *.
        solve_addr.
      }

      erewrite (lmeasure_measure _ (mem σ)); eauto.
      2: {
        eapply (is_cur_lword_lea vmap RX RX b (b ^+ 1)%a e e _ _ _ (LCap RX b e _ _)).
        rewrite Is_true_true.
        apply isWithin_of_le.
        solve_addr.
        all: try easy.

        eapply lreg_corresponds_read_iscur.
        by destruct Hcorr0.
        by eapply lookup_weaken in Hlccap. }

      iApply wp2_diag_univ.
      iSplit.

      (* Need the gen_heap_interp for the incrementPC call below, use frame rule *)

      1: {
        iIntros (Hhash Hlhash).
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        iSplitR "Hφ Hregs Hmem HECv".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
        iRight. iSplit; try easy. iPureIntro.
        eapply EInit_fail_hash_fail; eauto.
        unfold lmeasure in Hhash.
        by destruct (hash_lmemory_range lmem (b ^+ 1)%a e v).
      }

      iIntros (eid) "%Hlmeasure %Hmeasure".
      rewrite updatePC_incrementPC.

      iApply wp_opt2_bind; iApply wp_opt2_eqn_both.

      iApply wp_opt2_mono2.
      iSplitL "Hφ Hprev_tb".
      2: {
        iApply transiently_wp_opt2.
        iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        rewrite map_full_own.
        iMod (update_state_interp_next_version (src := r_data) with "[$Hσr $Hσm $Hregs $Hmem]") as
          "(%Hvm & Hσr & Hσm & %Hcorr' & Hregs & Hmem)"; cycle 1; eauto.
        rewrite -map_full_own.
        iMod (gen_heap_update_inSepM _ _ (b0,v0+1) (LSealRange (true, true) s_b s_e s_b) with
               "Hσm Hmem") as "(Hσm & Hmem)"; eauto.
        {
          destruct Hvm as (_&_&_&Hall).
          rewrite Forall_forall in Hall.
          apply Hall; eauto.
          apply elem_of_finz_seq_between; solve_addr.
        }
        rewrite map_full_own.
        eapply (state_phys_log_corresponds_update_mem (la := (b0, v0+1))
          (lw := LSealRange (true, true) s_b s_e s_b)) in Hcorr'; cycle 1.
        { (* TODO turn into lemma *)
          rewrite finz_seq_between_cons ; eauto.
          cbn.
          rewrite /is_cur_addr; cbn.
          rewrite /update_version_addr_vmap.
          by simplify_map_eq.
        }
        { by cbn. }
        cbn in Hcorr'.
        set (mem' := (<[b0:=WSealRange (true, true) s_b s_e s_b]> (mem σ))).
        iMod (update_state_interp_next_version (src := r_code) (σm := mem') with "[$Hσr $Hσm $Hregs $Hmem]") as
          "(%Hvm' & Hσr & Hσm & %Hcorr'' & Hregs & Hmem)"; eauto.
        { (* TODO turn into lemma *)
          subst mem'.
          rewrite /sweep_reg in Hcode_sweep |- *.
          apply andb_true_intro.

          apply andb_true_iff in Hcode_sweep as [Hsweep ?]; split ; eauto.
          rewrite /sweep_memory_reg in Hsweep |- *.
          rewrite !Hccap  in Hsweep |- *.
          rewrite bool_decide_eq_true_2; first done.
          apply bool_decide_eq_true_1 in Hsweep.
          cbn in *.
          rewrite /unique_in_memory in Hsweep |- *.
          apply map_Forall_insert_2; auto.
        }
        { by simplify_map_eq. }
        { by simplify_eq. }
        rewrite -map_full_own.
        iMod (gen_heap_update_inSepM _ _ (b,v+1) (LCap RW b0 e0 a0 (v0+1)) with "Hσm Hmem") as "(Hσm & Hmem)"; eauto.
        {
          destruct Hvm' as (_&_&_&Hall).
          rewrite Forall_forall in Hall.
          apply Hall; eauto.
          apply elem_of_finz_seq_between; solve_addr.
        }
        eapply (state_phys_log_corresponds_update_mem (la := (b, v+1))
          (lw := LCap RW b0 e0 a0 (v0 + 1))) in Hcorr''; cycle 1.
        { (* TODO turn into lemma *)
          rewrite finz_seq_between_cons ; eauto.
          cbn.
          rewrite /is_cur_addr; cbn.
          rewrite /update_version_addr_vmap.
          by simplify_map_eq.
        }
        { change ( LCap RW b0 e0 a0 (v0 + 1)) with ( next_version_lword ( LCap RW b0 e0 a0 v0)).
          assert (
              is_cur_word (next_version_lword (LCap RW b0 e0 a0 v0)) (update_version_region_vmap (finz.seq_between b0 e0) v0 vmap)
            ) as ?.
          { destruct Hcorr0 as [? _]; eauto.
            eapply update_version_word_region_update_lword; eauto.
            eapply lreg_corresponds_read_iscur; eauto.
            eapply lookup_weaken ; eauto.
          }
          eapply (update_version_notin_is_cur_word _ _ _ _ _ _ _ _ (LCap RX b e a v))
          ; eauto.
          clear -Hcode_sweep Hccap Hdcap Hneq_rcode_data.
          eapply sweep_reg_spec in Hcode_sweep; eauto.
          cbn in Hcode_sweep.
          rewrite /unique_in_machine_reg in Hcode_sweep.
          apply Hcode_sweep in Hccap as [Hunique _].
          rewrite /unique_in_registers in Hunique.
          eapply map_Forall_lookup_1 in Hunique; last eapply Hdcap.
          rewrite decide_False in Hunique; auto.
        }


        (* mod update for <[(enumcur σ) := eid]> etable in CUR_TB *)
        iMod (own_update with "Hcur_tb") as "(Hcur_tb & Hcur_frag)".
        eapply (auth_update_alloc (Excl <$> cur_tb) (Excl <$> (<[tidx := eid]> cur_tb)) (Excl <$> {[ tidx := eid ]})).
        rewrite fmap_insert.
        rewrite map_fmap_singleton.
        apply gmap.alloc_singleton_local_update.
        { clear -HEC Hdomtbcompl.
          rewrite lookup_fmap.
          apply fmap_None.
          rewrite HEC in Hdomtbcompl.
          rewrite dom_union_L in Hdomtbcompl.
          rewrite -not_elem_of_dom.
          assert (tidx ∉ dom cur_tb ∪ dom prev_tb); last set_solver.
          rewrite Hdomtbcompl.
          apply not_elem_of_list_to_set.
          intro Htidx.
          apply elem_of_seq in Htidx; lia.
        }
        { done. }

        (* mod update for <[(enumcur σ) := eid]> etable in ALL_TB *)
        iMod (own_update with "Hall_tb") as "(Hall_tb & Hall_frag)".
        eapply (auth_update_alloc (to_agree <$> all_tb) (to_agree <$> (<[tidx := eid]> all_tb)) (to_agree <$> {[ tidx := eid ]})).
        rewrite fmap_insert.
        rewrite map_fmap_singleton.
        apply gmap.alloc_singleton_local_update.
        { clear -HEC Htbcompl Hdomtbcompl.
          rewrite lookup_fmap.
          apply fmap_None.
          rewrite HEC in Hdomtbcompl.
          rewrite dom_union_L in Hdomtbcompl.
          rewrite -not_elem_of_dom.
          rewrite -Htbcompl.
          assert (tidx ∉ dom cur_tb ∪ dom prev_tb); last set_solver.
          rewrite Hdomtbcompl.
          apply not_elem_of_list_to_set.
          intro Htidx.
          apply elem_of_seq in Htidx; lia.
        }
        { done. }
        cbn.
        iCombine "Hecauth HECv" as "HEC".
        iMod (own_update with "HEC") as "(Hecauth & HECv)".
        apply (excl_auth_update _ _ (enumcur σ + 1)).

        iMod (gen_heap_update_inSepM _ _ r_code (LCap machine_base.E b e (b ^+ 1)%a (v+1)) with
               "Hσr Hregs") as "(Hσr & Hregs)"; eauto.
        { by simplify_map_eq. }
        iMod (gen_heap_update_inSepM _ _ r_data (LInt 0) with "Hσr Hregs") as "(Hσr & Hregs)"; eauto.
        { rewrite lookup_insert_ne; eauto.
          rewrite lookup_insert_ne; eauto.
          by simplify_map_eq.
        }
        iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".


        iApply (wp_opt2_frame with "Hσm").
        iApply (wp_opt2_frame with "Hmem").
        iApply (wp_opt2_frame with "Hcur_tb").
        iApply (wp_opt2_frame with "Hcur_frag").
        iApply (wp_opt2_frame with "Hall_tb").
        iApply (wp_opt2_frame with "Hall_frag").
        iApply (wp_opt2_frame with "Hecauth").
        iApply (wp_opt2_frame with "HECv").
        iAssert (⌜ _ ⌝)%I as "Hcorr''"; first (iPureIntro ; eapply Hcorr'').
        iApply (wp_opt2_frame with "Hcorr''").
        iModIntro.
        (* iDestruct "Hcorr''" as "%Hcorr''". *)

        iApply (wp2_opt_incrementPC2 with "[Hσr Hregs]"); cycle -1.
        {
          iFrame.
          rewrite !insert_insert.
          iEval (rewrite insert_commute; eauto) in "Hregs".
          rewrite !insert_insert.
          iEval (rewrite insert_commute; eauto) in "Hregs".
          iFrame.
        }
        { apply elem_of_dom. by repeat (rewrite lookup_insert_is_Some'; right). }
        {
          rewrite insert_insert.
          rewrite insert_commute; auto.
          rewrite insert_insert.
          rewrite insert_commute; auto.
          by do 2 (apply insert_mono).
        }
        {
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 0)); eauto. constructor. (* ints are always current... *)
          eapply (state_phys_log_corresponds_update_reg
                    (lw := LCap machine_base.E b e (b ^+ 1)%a (v+1))); eauto.
          cbn.
          intros a' Ha'.
          rewrite /update_version_addr_vmap.
          apply update_version_region_vmap_lookup; auto.
          apply finz_seq_between_NoDup.
        }
      }

      iSplit.
      iIntros "Hσ %Hincrement".
      { (* PC increment failed *)
        iIntros.
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem & Hcur_tb & Hall_tb & Hecauth & HECv)".
        iSplitR "Hφ Hregs Hmem HECv".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem $HECv]").
        iRight. iSplit; try easy. iPureIntro.
        eapply  EInit_fail_pc_overflow; eauto. }

      (* incr succeeds *)
      iIntros (lregs' regs') "Hσ %Hlincrement %Hincrement".
      iApply wp2_val.
      iMod (transiently_commit with "Hσ") as "(Hσm & Hmem & Hcur_tb & Hcur_frag & Hall_tb & Hall_frag & Hecauth & HECv & %Hcorr'' & [%lr' (Hσr' & %Hcorr' & Hregs')])".
      iModIntro.
      iSplitR " Hφ Hregs' Hmem HECv Hcur_frag Hall_frag".
      { subst.
        incrementPC_inv; simplify_map_eq.
        iExists _, _, _, _, _, _; iFrame; cbn; iPureIntro.
        split; first done.
        split.
        {
          rewrite dom_insert_L disjoint_union_l; split ; auto.
          rewrite disjoint_singleton_l.
          assert (enumcur σ ∉ dom prev_tb ∪ dom (etable σ)) as H'; last set_solver+H'.
          rewrite union_comm_L -dom_union_L Hdomtbcompl.
          rewrite not_elem_of_list_to_set.
          rewrite elem_of_seq; solve_finz+.
        }
        split.
        {
         rewrite dom_union_L dom_insert_L -union_assoc_L -dom_union_L Hdomtbcompl.
          replace ( enumcur σ + 1) with (S (enumcur σ)) by lia.
          rewrite seq_S; simpl.
          rewrite list_to_set_app_L.
          set_solver+.
        }
        split.
        { rewrite map_disjoint_insert_l; split; last done.
          rewrite -not_elem_of_dom.
          assert (enumcur σ ∉ dom prev_tb ∪ dom (etable σ)) as H'; last set_solver+H'.
          rewrite union_comm_L -dom_union_L Hdomtbcompl.
          rewrite not_elem_of_list_to_set.
          rewrite elem_of_seq; solve_finz+.
        }
        split.
        { rewrite !insert_union_singleton_l.
          by rewrite map_union_assoc.
        }
        eapply Hcorr'.
      }

      { iApply ("Hφ" with "[$Hregs' $Hmem $HECv Hcur_frag Hall_frag]"). iLeft.
        unfold EInit_spec_success.
        apply bind_Some in Hlmeasure as (lhash&Hlmeasure&Hlhash_range); simplify_eq.
        apply bind_Some in Hmeasure as (hash&Hmeasure&Hhash_range); simplify_eq.
        set (lmem2 :=
                  (update_version_region lm (finz.seq_between b0 e0) v0 lmem)).
        set (lmem3 :=
               (update_version_region
                  (update_version_region lm (finz.seq_between b0 e0) v0 lm)
                  (finz.seq_between b e) v
                  (update_version_region lm (finz.seq_between b0 e0) v0 lmem))).
        iExists lm, lmem2, lmem3, b, e, a, v, b0, e0, a0, v0, _, _.
        rewrite !map_fmap_singleton; iFrame.
        iPureIntro.
        intuition eauto.
        { assert (tid_of_otype s_b = enumcur σ); last done.
          clear - Hs_b Hs_e.
          rewrite /tid_of_otype.
          destruct (Z.even s_b) eqn:HZeven; cycle 1.
          { by apply finz_even_mul2 in Hs_b; rewrite Hs_b in HZeven. }
          replace (Z.to_nat s_b) with (2 * Z.to_nat (enumcur σ)) by solve_finz.
          apply finz_of_z_is_Some_spec in Hs_b.
          rewrite Nat.mul_comm Nat.div_mul; lia. }
        { by eapply finz_even_mul2. }
        { solve_addr. }
        { apply is_valid_updated_lmemory_update_version_region; eauto.
          - apply finz_seq_between_NoDup.
          - eapply state_corresponds_last_version_lword_region; eauto; cycle 1.
            ++ eapply lookup_weaken in Hldcap. apply Hldcap. apply Hlrsub.
            ++ done.
          - eapply state_corresponds_access_lword_region; eauto; cycle 1.
            ++ eapply lookup_weaken in Hldcap. apply Hldcap. apply Hlrsub.
            ++ done. }
        {(* eauto using is_valid_updated_lmemory_update_version_region, lookup_weaken, finz_seq_between_NoDup, state_corresponds_last_version_lword_region, state_corresponds_access_lword_region. *)
          apply is_valid_updated_lmemory_update_version_region; eauto using update_version_region_mono, finz_seq_between_NoDup.
          - (* data and code don't overlap, moreover old version was cur in lm *)
            assert (Hnovupdate : Forall (λ a : Addr,  lm !! (a, v + 1) = None)
    (finz.seq_between b e)).
            { eapply (state_corresponds_last_version_lword_region); cycle 2.
              + eapply lookup_weaken in Hlccap; eauto.
              + eauto.
              + done. }
            rewrite Forall_forall in Hnovupdate.
            rewrite Forall_forall.
            intros a' Ha'in.
            rewrite update_version_region_notin_preserves_lmem.
            by apply Hnovupdate.
            by set_solver.

          - rewrite Forall_forall.
            intros a' Hain.
            rewrite update_version_region_notin_preserves_lmem.
            2: by set_solver.
            clear Hcorr'' Hcorr' Hcorr0 Hincrement Hlincrement.
            apply HallowsMemory in Hlccap; eauto.
            specialize (Hlccap Hpc_notin_code).
            rewrite Forall_forall in Hlccap.
            apply Hlccap in Hain.
            eapply lookup_weaken_is_Some; eauto. }

        { subst lmem2.
          assert (b0 ∉ finz.seq_between b e).
          {
          clear -Hcode_sweep Hdcap Hccap Hneq_rcode_data l l0.
          eapply sweep_reg_spec in Hcode_sweep; eauto.
          cbn in Hcode_sweep.
          rewrite /unique_in_machine_reg in Hcode_sweep.
          apply Hcode_sweep in Hccap as [Hunique _].
          rewrite /unique_in_registers in Hunique.
          eapply map_Forall_lookup_1 in Hunique; last eapply Hdcap.
          rewrite decide_False in Hunique; auto.
          cbn in Hunique.
          intro; simplify_eq.
          apply Hunique.
          rewrite elem_of_finz_seq_between in H.
          destruct (b <? b0)%a eqn:Hb0 ; try solve_addr.
          }
          rewrite -update_version_region_insert; auto.
          replace s_e with (s_b ^+ 2)%f by solve_finz.
          rewrite insert_commute; first done.
          intro ; simplify_eq
          ; rewrite elem_of_finz_seq_between in H
          ; solve_finz.
        }
        {  apply andb_prop in Hcode_sweep.
           eapply unique_in_registersL_mono; eauto.
           destruct Hcode_sweep.
           eapply sweep_registers_reg_spec in H0; eauto.
           cbn in H0.
           eapply state_corresponds_unique_in_registers; eauto.
           eapply lookup_weaken; eauto. }
        {  apply andb_prop in Hdata_sweep.
           eapply unique_in_registersL_mono; eauto.
           destruct Hdata_sweep.
           eapply sweep_registers_reg_spec in H0; eauto.
           cbn in H0.
           eapply state_corresponds_unique_in_registers; eauto.
           eapply lookup_weaken; eauto. }
        {  eapply ensures_is_z_mono; try eauto.
          eapply ensures_is_z_corresponds; eauto.
          destruct Hcorr0 as [Hcorr0 _].
          assert (lr !! r_code = Some (LCap RX b e a v) )
            as Hlccap' by (eapply lookup_weaken ; eauto).
          eapply lreg_corresponds_read_iscur in Hlccap'; eauto.
          eapply is_cur_lword_lea; eauto; try done.
          rewrite Is_true_true.
          eapply isWithin_of_le;solve_addr.
        }
      }
      Unshelve.
      all : try exact 0%ot.
      all : try exact 0%a.
      all : try exact 0.
      all : try exact ∅.
      try exact r_data.
      try exact O.

  Qed.

End cap_lang_rules.
