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
  (* Etable is now unbounded *)
  (* | EInit_fail_etable_full *)

  (* the code register doesn't contain a capability *)
  | EInit_fail_ccap_not_a_cap lw :
    lregs !! r_code = Some lw ->
    is_log_cap lw = false →
    EInit_fail lregs lmem r_code r_data tidx ot
  (* the code capanility is not RX *)
  | EInit_fail_ccap_no_rx p b e a v :
    lregs !! r_code = Some (LCap p b e a v) ->
    p ≠ RX ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the code capanility does not contain enough space for the data_capability *)
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
  | EInit_fail_dcap_no_rx p b e a v :
    lregs !! r_data = Some (LCap p b e a v)->
    p ≠ RW ->
    EInit_fail lregs lmem  r_code r_data tidx ot
  (* the data capanility does not contain enough space for the data_capability *)
  | EInit_fail_dcap_small p b e a v :
    lregs !! r_data = Some (LCap p b e a v) ->
    ¬ (b < e)%a ->
    EInit_fail lregs lmem  r_code r_data tidx ot

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
    tid_of_otype ot = Some tidx ->
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
    ⌜(tidx+1)%nat = tidx_incr⌝ ∗
    ⌜tid_of_otype ot = Some tidx⌝ ∗
    ⌜Z.even ot = true⌝ ∗
    ⌜ (hash_lmemory_range lmem (code_b ^+ 1)%a code_e code_v) = Some hash_instrs
    ∧ hash_concat (hash code_b) hash_instrs = eid⌝ ∗ (* eid = hash(code_b || mem[b+1::e]) *)
    ⌜(ot + 2)%ot = Some (ot ^+ 2)%ot ⌝ ∗ (* there are still otypes left in the pool *)
    ⌜lregs !! r_code = Some (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* rcode contains a valid code capability *)
    ⌜lregs !! r_data = Some (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* rdata contains a valid data capability *)
    ⌜ (code_b < code_e)%a ⌝ ∗ (* the code capability contains at least one address *)
    ⌜ (data_b < data_e)%a ⌝ ∗ (* the data capability contains at least one address *)
    ⌜is_valid_updated_lmemory glmem lmem (finz.seq_between code_b code_e) code_v lmem'' ⌝ ∗ (* all memory in the code capability is "current" w.r.t. revocation *)
    ⌜is_valid_updated_lmemory glmem lmem (finz.seq_between data_b data_e) data_v lmem'' ⌝ ∗ (* all memory in the data capability is "current" w.r.t. revocation *)
    ⌜ lmem' =
    <[ ( data_b, (data_v+1)%nat ) := (LSealRange (true,true) ot (ot ^+ 2)%ot ot ) ]>
      (<[ (code_b, (code_v+1)%nat ) := (LCap RW data_b data_e data_a (data_v + 1)%nat) ]> lmem'') ⌝ ∗
    ⌜unique_in_registersL lregs (Some r_code) (LCap RX code_b code_e code_a code_v) ⌝ ∗ (* the code capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜unique_in_registersL lregs (Some r_data) (LCap RW data_b data_e data_a data_v) ⌝ ∗ (* the data capability is unique across all registers (except where it is stored: in `r_code`) *)
    ⌜ map_Forall (fun la lw => (laddr_get_addr la) ∈ (finz.seq_between (code_b ^+ 1)%a code_e) -> is_zL lw) lmem⌝ ∗
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

  Definition allows_einit (lregs : LReg) (r : RegName) :=
    ∀ p b e a v,
    lregs !! r = Some (LCap p b e a v)
    -> readAllowed p = true
    -> (finz.seq_between b e) ## reserved_addresses.

  (*     lmem = lmem' → *)
  (*     (* ... *) *)

  Lemma wp_einit E pc_p pc_b pc_e pc_a pc_v lw lregs lmem tidx r_code r_data :
    decodeInstrWL lw = EInit r_code r_data →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EInit r_code r_data) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allows_einit lregs r_code →
    allows_einit lregs r_data →
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
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HrcodeAllowEInit HrdataAllowEInit φ) "(>Hregs & >Hmem & HECv) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
                         "(Hr & Hm
                          & -> & Htbl_cur & Htbl_prev & Htbl_all
                          & HEC
                          & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
                          & %HLinv)"
    ; cbn in *.

    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as %Hregs.
    (* have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs. *)
    (* specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
    (* odestruct (Hri rs) as [lsrcv [Hlsrc' Hlsrc] ]; first by set_solver+. *)

    (* Derive necessary memory *)
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem.
    (* iDestruct (gen_mem_valid_inSepM lmem lm with "Hm Hmem") as %Hma; eauto. *)

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    iNext; iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    (* 2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)
    cbn in Hstep; simplify_eq.
    iModIntro.
    iSplitR "Hφ HECv". (* not yet sure what is needed *)
    iExists lr, lm, vmap.
    iExists etable, tbl_prev, (etable ∪ tbl_prev).
    iFrame; auto.


    all: admit.
   (* Qed. *)
  Admitted.

End cap_lang_rules.
