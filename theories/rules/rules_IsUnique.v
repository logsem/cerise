From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.
From cap_machine.proofmode Require Export region register_tactics.

Section cap_lang_rules.
  Context `{HmemG : memG Σ, HregG : regG Σ}.
  Context `{Hparam : MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  (* Implicit Types lmem : LMem. *)

  Definition is_sealed (lw : LWord) :=
    match lw with
    | LCap E _ _ _ _ | LSealedCap _ _ _ _ _ _ => true
    | _ => false
    end.

  Definition is_log_cap_or_scap (lw : LWord) : bool :=
    match lw with
    | LCap _ _ _ _ _ | LWSealed _ (LSCap _ _ _ _ _)  => true
    | _ => false
    end.

  Inductive IsUnique_fail (lregs : LReg) (lmem : LMem) (dst src : RegName): Prop :=
  | IsUnique_fail_cap (lwsrc: LWord) :
    lregs !! src = Some lwsrc ->
    is_log_cap_or_scap lwsrc = false →
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_upd (lwsrc: LWord) p b e a v:
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword lwsrc ]> lregs)) = None ->
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_nupd (lwsrc: LWord) (z : Z):
    lregs !! src = Some lwsrc ->
    incrementLPC (<[ dst := LInt z ]> lregs) = None ->
    IsUnique_fail lregs lmem dst src.

  Inductive IsUnique_spec
    (lregs: LReg) (lmem : LMem) (dst src : RegName)
    (lregs': LReg) (lmem' : LMem) : cap_lang.val → Prop :=

  | IsUnique_success_true_cap (p : Perm) (b e a : Addr) (v : Version) :
    lregs !! src = Some (LCap p b e a v) ->
    p ≠ E ->
    (* we update the region of memory with the new version *)
    is_valid_updated_lmemory lmem (finz.seq_between b e) v lmem' ->
    (* specific instance of unique_in_registers *)
    unique_in_registersL lregs src (LCap p b e a v) ->
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword (LCap p b e a v) ]> lregs)) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_true_is_sealed (lwsrc : LWord) :
    lregs !! src = Some lwsrc ->
    is_sealed lwsrc ->
    (* specific instance of unique_in_registers *)
    unique_in_registersL lregs src lwsrc ->
    lmem' = lmem ->
    incrementLPC (<[ dst := LInt 1 ]> lregs) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_false (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    lmem' = lmem ->
    incrementLPC (<[ dst := LInt 0 ]> lregs) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_failure :
    lregs = lregs' ->
    lmem = lmem' ->
    IsUnique_fail lregs lmem dst src ->
    IsUnique_spec lregs lmem dst src lregs' lmem' FailedV
  .

  (** NOTE Proof strategy:

    We only care when the sweep is true.
    1. From the operational 'sweep phm phr src = true',
       the specification states that there's no overlap in the *physical* machine,
       'unique_in_machine phm phr src wsrc'

    2. In combination with the 'phys_log_correspondance',
       we get an equivalent for the *logical machine*,
       'unique_in_machineL lm lr src lwsrc'.

    2a. We define 'unique_in_machineL' by looking only at
        the last version of each laddress.
        'phys_log_correspondance' states that,
        the physical memory corresponds
        to the logical view for the current view of each address.
        It also states that,
        the current view of a logical address
        is actually the max version in the lmemory.

    2b. Thanks to 2a,
        under the 'phys_log_correspondance' hypothesis,
        we know that the current view of the lmemory
        corresponds to the laddresses with the max version number.
        We can then reason equivalently with
        the 2 interpretation of
        "the current view" (easier to reason about)
        VS "last version number" (requires to know the current view map)

    3. From 'unique_in_machineL lmem lregs src lwsrc',
       we know that we can safely update the lmemory region in lmem
       corresponding to 'lwsrc'.

    4. Because the lmem had been updated,
       we can also update the heap resources;
       for the memory and the registers.

    5. It is finally possible to re-establish
       'phys_log_correspondance
        phr phm (updated lregs) (updated lmem) (updated vmap)',
        which, one might notice, the version number changes.
   *)

  (** NOTE What should be captured:

    --- ownership over the whole region  ---
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v)
        ∗ dst        ↦ᵣ _
        ∗ (b, v)     ↦ₐ lwb
        ∗ (b+1, v)   ↦ₐ lwb'
    }}}
    ->
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v+1)
        ∗ dst        ↦ᵣ LInt 1
        ∗ (b, v)     ↦ₐ lwb
        ∗ (b+1, v)   ↦ₐ lwb'

        ∗ (b, v+1)   ↦ₐ lwb
        ∗ (b+1, v+1) ↦ₐ lwb'
    }}}

    --- ownership over part of the region  ---
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (E,b,b+2,_,v)
        ∗ dst        ↦ᵣ _
    }}}
    ->
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (E,b,b+2,_,v)
        ∗ dst        ↦ᵣ LInt 1
    }}}

   *)

  Definition exec_optL_IsUnique
    (lregs : LReg) (lmem : LMem)
    (dst : RegName) (src : RegName)
    (bsweep : bool) : option LReg :=
    lwsrc        ← lregs !! src ;
    _            ← match (is_lcap lwsrc) with | true => Some () | false => None end;
    lregs' ← incrementLPC
      (if bsweep
       then
         (if is_sealed lwsrc
          then (<[dst:=LWInt 1%Z]> lregs)
          else (<[dst:=LWInt 1%Z]> (<[ src := next_version_lword lwsrc ]> lregs)))
       else (<[dst:=LWInt 0%Z]> lregs)
      )
    ; Some lregs'.

  (* TODO move stdpp_extra *)
  Lemma snd_fmap_pair_inv {K V1 V2} `{Countable K} (m : gmap K V1) (v2 : V2) :
    (snd <$> ((λ v : V1, (v2, v)) <$> m)) = m.
  Proof.
    induction m using map_ind.
    - by rewrite !fmap_empty.
    - by rewrite !fmap_insert /= IHm.
  Qed.

  (* TODO generalise and move *)
  Lemma fmap_forall_inv (lmt : LMemF) :
    map_Forall (λ (_ : LAddr) (a : dfrac * LWord), a.1 = DfracOwn 1) lmt ->
    exists lm, lmt = ((λ y : LWord, (DfracOwn 1, y)) <$> lm).
  Proof.
    induction lmt using map_ind; intro Hall.
    - exists ∅. by rewrite fmap_empty.
    - assert (x.1 = DfracOwn 1) as Hx
                                     by (apply map_Forall_insert_1_1 in Hall; auto).
      apply map_Forall_insert_1_2 in Hall; auto.
      apply IHlmt in Hall.
      destruct Hall as (lm' & Hall).
      exists (<[i := (snd x)]> lm').
      rewrite fmap_insert /=.
      by destruct x ; cbn in * ; subst.
  Qed.

  (* TODO move *)
  Lemma wp2_word_is_lcap {Ep} {w Φf Φs} :
         Φf ∧ (Φs () ())
      ⊢ wp_opt2 Ep (if is_lcap w then Some () else None) (word_is_cap_or_scap (lword_get_word w)) Φf Φs.
  Proof.
    iIntros "HΦ".
    destruct w as [ | [ | ] | [] [ | ] ]; cbn.
    all: try now rewrite bi.and_elim_l.
    all: try now rewrite bi.and_elim_r.
  Qed.

  Lemma state_interp_transient_unique_in_lregs
    {σ σt lreg lrt lmem lmt src lwsrc}:
    sweep (mem σ) (reg σ) src = true ->
    lreg !! src = Some lwsrc ->
    state_interp_transient σ σt lreg lrt lmem lmt ⊢
    ⌜ unique_in_registersL lreg src lwsrc ⌝.
  Proof.
    iIntros (Hsweep Hsrc) "(Hσ & Hregs & Hmem & _ & Hcommit)".
    iDestruct "Hσ" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregs_incl".
    iPureIntro.
    eapply unique_in_registersL_mono; first done.
    eapply lookup_weaken in Hsrc; eauto.
    eapply state_corresponds_unique_in_registers; eauto.
    eapply sweep_registers_spec ; cbn.
    2: eapply state_corresponds_reg_get_word; eauto.
    clear -Hsweep.
    apply Is_true_true in Hsweep.
    apply Is_true_true.
    rewrite /sweep in Hsweep.
    by destruct_and? Hsweep.
  Qed.

  (* TODO generalise to not just LMem + find better name + move iris_extra *)
  Lemma map_full_own (lm : LMem) :
    ([∗ map] k↦y ∈ lm, k ↦ₐ y)%I
    ⊣⊢ ([∗ map] la↦dw ∈ ((λ y : LWord, (DfracOwn 1, y)) <$> lm), la ↦ₐ{dw.1} dw.2).
  Proof.
    induction lm using map_ind.
    - rewrite fmap_empty.
      by iSplit; iIntros "Hmem".
    - rewrite fmap_insert.
      iSplit; iIntros "Hmem".
      + iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"; first done.
        iDestruct (IHlm with "Hmem") as "Hmem".
        iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
        by rewrite lookup_fmap fmap_None.
        by cbn.
      +
        iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"
        ; first (by rewrite lookup_fmap fmap_None).
        iDestruct (IHlm with "Hmem") as "Hmem".
        cbn.
        by iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
  Qed.

  (* TODO lemma à la update_state_interp_from_mem_mod,
       i.e. that updates the actual state *)
  Lemma update_state_interp_next_version
    {σ Ep lregs lmem (* lmem' *) (* vmap *) src lwsrc p b e a v} :

    sweep (mem σ) (reg σ) src = true ->
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->

    state_interp_logical σ
    ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
    ∗ ([∗ map] la↦dw ∈ ((λ y : LWord, (DfracOwn 1, y)) <$> lmem), la ↦ₐ{dw.1} dw.2)
    ⊢ |={Ep}=>
          ∃ lmem',
    ⌜ is_valid_updated_lmemory lmem (finz.seq_between b e) v lmem'⌝ ∗
          state_interp_logical σ
          ∗ ([∗ map] k↦y ∈ (<[src:=next_version_lword lwsrc]> lregs), k ↦ᵣ y)
          ∗ ([∗ map] la↦dw ∈ ((λ y : LWord, (DfracOwn 1, y)) <$> lmem'), la ↦ₐ{dw.1} dw.2).
  Proof.
    iIntros (Hsweep Hlsrc Hlcap_wsrc) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iDestruct (map_full_own with "Hmem") as "Hmem".
    iPoseProof (gen_heap_valid_inclSepM with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ src (next_version_lword lwsrc)) with "Hr Hregs") as
      "[Hr Hregs]"; eauto.
    iFrame.
    destruct
      (update_cur_version_region lmem lm vmap ((finz.seq_between b e)))
      as ((lmem' & lm') & vmap') eqn:Hupd_lmem.
    iMod ((gen_heap_lmem_version_update lmem lm lmem' _ vmap _ (finz.seq_between b e) v)
           with "Hm Hmem") as "[Hm Hmem]"; eauto.
    by apply finz_seq_between_NoDup.
    admit. (* easy (?) *)
    admit. (* easy (?) *)
    iModIntro; iExists lmem'.
    iSplit; first (iPureIntro; eapply update_cur_version_region_valid; eauto).
    by apply finz_seq_between_NoDup.
    admit. (* easy (?) *)
    admit. (* easy (?) *)
    admit. (* easy (?) *)
    iSplitR "Hmem".
    rewrite /state_interp_logical.
    iExists (<[src:=next_version_lword lwsrc]> lr),lm',vmap'.
    iFrame.
    iPureIntro.
    {
      (* TODO extract as a lemma ? *)
      assert (lr !! src = Some lwsrc) as Hsrc' by (eapply lookup_weaken; eauto).
      eapply sweep_true_specL in Hsweep; eauto.
      split.
      + rewrite (_: (reg σ) = (<[src:=(lword_get_word (next_version_lword lwsrc))]> (reg σ))).
        * eapply update_cur_version_region_lreg_corresponds_src; eauto.
          eapply update_cur_version_region_lcap_update_lword; eauto.
          admit. (* easy (?) *)
          eapply lreg_corresponds_read_iscur; eauto.
          by destruct HLinv.
        * rewrite lword_get_word_next_version.
          rewrite insert_id; first done.
          eapply state_corresponds_reg_get_word; eauto.
      + eapply update_cur_version_region_lmem_corresponds; eauto.
    }
    by iDestruct (map_full_own with "Hmem") as "Hmem".
  Admitted.



  Lemma update_state_interp_transient_next_version {σ σt lreg lregt lmem lmemt src lwsrc p b e a v}:
    sweep (mem σt) (reg σt) src = true ->
    lregt !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    state_interp_transient σ σt lreg lregt
      ((λ y : LWord, (DfracOwn 1, y)) <$> lmem)
      ((λ y : LWord, (DfracOwn 1, y)) <$> lmemt) ⊢
    ∃ (lmemt' : LMem),
      ⌜ is_valid_updated_lmemory lmemt (finz.seq_between b e) v lmemt'⌝ ∗
      state_interp_transient
        σ σt (* the physical state does not change *)
        lreg (<[ src := next_version_lword lwsrc ]> lregt) (* the version of the word is updated *)
        ((λ y : LWord, (DfracOwn 1, y)) <$> lmem) ((λ y : LWord, (DfracOwn 1, y)) <$> lmemt'). (* the version of the memory region is updated *)
  Proof.
    iIntros (Hsweep Hsrc Hcap_lwsrc) "(Hσ & Hregs & Hmem & %Hcor & Hcommit)".
    cbn in *.
    destruct Hcor as (lrt & lmt & vmap & Hlregt_incl & Hlmemt_incl & HLinv).
    rewrite snd_fmap_pair_inv in Hlmemt_incl.
    assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).
    assert (lrt !! src = Some lwsrc) as Hsrc' by (eapply lookup_weaken in Hsrc ; eauto).
    opose proof
      (state_corresponds_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ HLinv _ Hsrc')
      as HcurMap ; first (by cbn).
    opose proof
      (state_corresponds_last_version_lword_region _ _ _ _ _ _ _ _ _ _ _ _  HLinv _ Hsrc')
      as HmemMap_maxv; first (by cbn).
    opose proof
      (state_corresponds_access_lword_region _ _ _ _ _ _ _ _ _ _ _ _ HLinv _ Hsrc')
      as HmemMap; first (by cbn).
    destruct
      (update_cur_version_region lmemt lmt vmap ((finz.seq_between b e)))
      as ((lmemt' & lmt') & vmap') eqn:Hupd_lmemt.
    iExists lmemt'.
    iSplit; first (iPureIntro; eapply update_cur_version_region_valid; eauto).
    iFrame "Hσ Hregs Hmem".
    eapply sweep_true_specL in Hsweep; eauto.

    iSplit.
    - iPureIntro; cbn.
      exists (<[src:=next_version_lword lwsrc]> lrt).
      exists (snd <$> ((λ y : LWord, (DfracOwn 1, y)) <$> lmt')).
      exists vmap'.
      split; [|split]; auto.
      { by apply insert_mono. }
      { rewrite !snd_fmap_pair_inv.
        eapply update_cur_version_region_preserves_lmem_incl; eauto. }
      {
        (* TODO extract as a lemma ? *)
        split.
        + rewrite (_: (reg σt) = (<[src:=(lword_get_word (next_version_lword lwsrc))]> (reg σt))).
          * eapply update_cur_version_region_lreg_corresponds_src; eauto.
            eapply update_cur_version_region_lcap_update_lword; eauto.
            eapply lreg_corresponds_read_iscur; eauto.
            by destruct HLinv.
          * rewrite lword_get_word_next_version.
            rewrite insert_id; first done.
            eapply state_corresponds_reg_get_word; eauto.
        + eapply update_cur_version_region_lmem_corresponds; eauto.
          by rewrite snd_fmap_pair_inv.
      }
    - iIntros (Ep) "H".
      iMod ("Hcommit" with "H") as "(Hσ & Hregs & Hmem)".
      iDestruct (update_state_interp_next_version with "[$Hσ $Hregs $Hmem]") as "H"; eauto.
      iMod "H".
      iDestruct "H" as (lmemt0) "(%Hvalid & Hσ & Hreg & Hmem)"; iFrame.
      (* TODO well, it is problematic because the
         lmemt0 that I get from the update of the commit
         might not be the same as the one obtained before. *)
      (* eapply lookup_weaken ; eauto. *)
      admit.
  Admitted.

  (* TODO the proof uses wp_opt,
     but requires some early destructs,
     which therefore require some proof duplication
   *)
  Lemma wp_isunique Ep
    pc_p pc_b pc_e pc_a pc_v
    (dst src : RegName) lw lmem lregs :
    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsUnique dst src) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ IsUnique_spec lregs lmem dst src lregs' lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc φ) "(>Hmem & >Hregs) Hφ".
    (*  extract the pc  *)
    rewrite (big_sepM_delete). 2: apply Hmem_pc. iDestruct "Hmem" as "[Hpc_a Hmem]".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hregs $Hpc_a Hmem Hφ]").
    iModIntro.
    iIntros (σ) "(Hσ & Hregs & Hpca)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    destruct (sweep (mem σ) (reg σ) src) eqn:Hsweep
    ; cbn ; rewrite Hsweep
    ; unshelve iApply (wp_wp2 (φ1 := exec_optL_IsUnique lregs lmem dst src _) (φ2 := _))
    ; [exact true|exact false| |].
    all: iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    - iMod (state_interp_transient_intro_nodfracs (lm := lmem) with "[$Hregs $Hσ Hmem Hpca]") as "Hσ".
      { iCombine "Hpca Hmem" as "Hmem".
        rewrite -(big_sepM_insert (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y)).
        rewrite insert_delete. iFrame. auto. by rewrite lookup_delete. }
      iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver.
      iIntros (srcv) "Hσ %Hlsrcv %Hsrcv".

      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_word_is_lcap. iSplit.

      { (* failure case: r1v contains something, but it is not a capability. *)
        iIntros "%Hcsrcv %Hgcsrcv".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
        rewrite big_sepM_fmap.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        constructor 4; try easy.
        eapply IsUnique_fail_cap; first eassumption.
        rewrite /is_log_cap_or_scap.
        destruct srcv; auto.
        destruct sb; cbn in *; done.
        destruct l; cbn in *; done.
      }

      iIntros "%Heqlwsrcv %Heqgwsrcv".
      rewrite updatePC_incrementPC; cbn.


      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      destruct (is_lcap srcv) eqn:Hsrcv_lcap ; last done; clear Heqlwsrcv.
      destruct (get_is_lcap_inv srcv Hsrcv_lcap) as (p & b & e & a & v & Hget_lsrcv).
      iDestruct (state_interp_transient_unique_in_lregs with "Hσ") as "%Hunique_in_lreg"; eauto.
      destruct (is_sealed srcv) eqn:His_sealed.
      + (* case is sealed: the version is not updated *)
        rewrite (update_state_interp_transient_int (dst := dst) (z := 1%Z))
        ; last by set_solver.
        iApply (wp2_opt_incrementPC with "[$Hσ Hφ]").
        { rewrite elem_of_dom.
          destruct (decide (PC = dst)); try by simplify_map_eq.
        }
        iSplit.
        { (* failure case: incrementing the pc failed *)
          iIntros (ec lregs') "Hσ %Hlincr %Hincr".
          iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
          rewrite big_sepM_fmap.
          iApply ("Hφ" with "[$Hregs $Hmem]").
          iPureIntro.
          constructor 4; auto.
          destruct srcv as [ | [|] | ? [|] ]
          ; cbn in *
          ; try done
          ; by econstructor 3.
        }

        (* pc incr success *)
        iIntros (lregs' regs') "Hσ %Hlincr %Hincr".
        iApply wp2_val. cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
        rewrite big_sepM_fmap; cbn.
        iApply ("Hφ" with "[$Hmem $Hregs]").
        iPureIntro.
        destruct srcv as [ | [|] | ? [|] ] ; cbn in *
        ; auto
        ; try done
        ; inversion Hget_lsrcv; subst.
        all: eapply IsUnique_success_true_is_sealed; eauto.
      + iDestruct (update_state_interp_transient_next_version
                     (b := b) (e := e) with "Hσ")
          as (lmt') "(%Hvalid_lmt' & Hσ)"; eauto.
        rewrite (update_state_interp_transient_int (dst := dst) (z := 1%Z))
        ; last by set_solver.
        iApply (wp2_opt_incrementPC with "[$Hσ Hφ]").
        { rewrite elem_of_dom.
          destruct (decide (PC = dst)); try by simplify_map_eq.
          destruct (decide (PC = src)); by simplify_map_eq.
        }
        iSplit.
        { (* failure case: incrementing the pc failed *)
          iIntros (ec lregs') "Hσ %Hlincr %Hincr".
          iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
          rewrite big_sepM_fmap.
          iApply ("Hφ" with "[$Hregs $Hmem]").
          iPureIntro.
          constructor 4; auto.
          destruct srcv as [ | [|] | ? [|] ]
          ; cbn in *
          ; try done
          ; by econstructor 2.
        }

        (* pc incr success *)
        iIntros (lregs' regs') "Hσ %Hlincr %Hincr".
        iApply wp2_val. cbn.
        iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
        rewrite big_sepM_fmap; cbn.
        iApply ("Hφ" with "[$Hmem $Hregs]").
        iPureIntro.
        destruct srcv as [ | [|] | ? [|] ] ; cbn in *
        ; auto
        ; try done
        ; inversion Hget_lsrcv; subst.
        eapply IsUnique_success_true_cap; eauto.
        { by intro ; subst. }
    - iMod (state_interp_transient_intro_nodfracs (lm := lmem) with "[$Hregs $Hσ Hmem Hpca]") as "Hσ".
      { iCombine "Hpca Hmem" as "Hmem".
        rewrite -(big_sepM_insert (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y)).
        rewrite insert_delete. iFrame. auto. by rewrite lookup_delete. }
      iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver.
      iIntros (srcv) "Hσ %Hlsrcv %Hsrcv".

      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      iApply wp2_word_is_lcap. iSplit.

      { (* failure case: r1v contains something, but it is not a capability. *)
        iIntros "%Hcsrcv %Hgcsrcv".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
        rewrite big_sepM_fmap.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        constructor 4; try easy.
        eapply IsUnique_fail_cap; first eassumption.
        rewrite /is_log_cap_or_scap.
        destruct srcv; auto.
        destruct sb; cbn in *; done.
        destruct l; cbn in *; done.
      }

      iIntros "%Heqlwdstv %Heqgwdstv".
      rewrite updatePC_incrementPC; cbn.
      iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
      rewrite (update_state_interp_transient_int (dst := dst) (z := 0%Z))
      ; last by set_solver.
      iApply (wp2_opt_incrementPC with "[$Hσ Hφ]").
      { rewrite elem_of_dom.
        destruct (decide (PC = dst)) ; subst; now simplify_map_eq.
      }
      iSplit.
      { (* failure case: incrementing the pc failed *)
        iIntros (ec lregs') "Hσ %Hlincr %Hincr".
        iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
        rewrite big_sepM_fmap.
        iApply ("Hφ" with "[$Hregs $Hmem]").
        iPureIntro.
        constructor 4; auto. econstructor 3; eauto. }

      (* pc incr success *)
      iIntros (lregs' regs') "Hσ %Hlincr %Hincr".
      iApply wp2_val. cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap; cbn.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      destruct srcv as [ | [|] | ? [|] ] ; cbn in *
      ; auto
      ; try done
      ; eapply IsUnique_success_false; eauto.
  Admitted.

  (* Lemma update_state_interp_transient_next_version {σ σt lr lrt} {lm lmt : LMemF} la lw lw' : *)
  (*   (forall cur_map, is_cur_regs lrt cur_map -> is_cur_word lw cur_map) -> *)
  (*   (forall cur_map, is_cur_regs lrt cur_map -> is_cur_addr la cur_map) -> *)
  (*   lmt !! la = Some (DfracOwn 1, lw') -> *)
  (*   state_interp_transient σ σt lr lrt lm lmt ⊢ *)
  (*   state_interp_transient σ (update_mem σt (laddr_get_addr la) (lword_get_word lw)) *)
  (*                         lr lrt (* registers remain unchanged *) *)
  (*                         lm (<[ la := (DfracOwn 1, lw)]> lmt). *)

    (* unfold read_reg_inr in *. rewrite Hlr1v in Hreadreg. *)
    (* inversion Heqlwr1v; inversion Hreadreg; subst. *)




  (*   apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc. *)
  (*   iApply wp_lift_atomic_head_step_no_fork; auto. *)
  (*   iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
  (*   iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv. *)

  (*   (* Derive necessary register values in r *) *)
  (*   iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)
  (*   have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs. *)
  (*   specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
  (*   odestruct (Hri dst) as [ldstv [Hldst' Hldst] ]; first by set_solver+. *)
  (*   odestruct (Hri src) as [lsrcv [Hlsrc' Hlsrc] ]; first by set_solver+. *)

  (*   (* Derive necessary memory *) *)
  (*   iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem. *)
  (*   iDestruct (gen_mem_valid_inSepM lmem lm with "Hm Hmem") as %Hma; eauto. *)

  (*   iModIntro. *)
  (*   iSplitR. *)
  (*   by iPureIntro; apply normal_always_head_reducible. *)
  (*   iNext. iIntros (e2 σ2 efs Hpstep). *)
  (*   apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
  (*   iIntros "_". *)
  (*   iSplitR; auto; eapply step_exec_inv in Hstep; eauto. *)
  (*   2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v))) *)
  (*   ; eapply state_corresponds_reg_get_word ; eauto. *)
  (*   2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto. *)

  (*   set (srcv := lword_get_word lsrcv). *)
  (*   assert ( reg !! src = Some srcv ) as Hsrc *)
  (*       by (eapply state_corresponds_reg_get_word ; eauto). *)
  (*   rewrite /exec /= Hsrc /= in Hstep. *)

  (*   (* src contains a capability *) *)
  (*   destruct (is_lcap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *. *)
  (*   { (* Fail : not a capability *) *)
  (*     destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv. *)
  (*     all: simplify_map_eq. *)
  (*     all: (iSplitR "Hφ Hmap Hmem" *)
  (*           ; [ iExists lr, lm, vmap; iFrame; auto *)
  (*             | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_cap *)
  (*          ]). *)
  (*   } *)
  (*   destruct (get_is_lcap_inv lsrcv Hlsrcv) as (p & b & e & a & v & Hget_lsrcv). *)

  (*   set (lregs' := (<[ dst := LInt (if (sweep mem reg src) then 1 else 0) ]> *)
  (*                     (if (andb (sweep mem reg src) (negb (is_sealed lsrcv)) ) *)
  (*                      then (<[ src := next_version_lword lsrcv]> lregs) *)
  (*                      else lregs))). *)
  (*   set (lr' := (<[ dst := LInt (if (sweep mem reg src) then 1 else 0) ]> *)
  (*                  (if (andb (sweep mem reg src) (negb (is_sealed lsrcv)) ) *)
  (*                   then (<[ src := next_version_lword lsrcv]> lr) *)
  (*                   else lr))). *)
  (*   assert (lreg_strip lregs' ⊆ lreg_strip lr') as Hlregs'_in_lr'. *)
  (*   { subst lregs' lr'. *)
  (*     apply map_fmap_mono, insert_mono. *)
  (*     destruct (sweep mem reg src); destruct (is_sealed lsrcv); cbn; auto. *)
  (*     apply insert_mono; auto. *)
  (*   } *)

  (*   assert ( (lreg_strip lr') = *)
  (*              (<[ dst := WInt (if (sweep mem reg src) then 1 else 0) ]> reg)) *)
  (*     as Hstrip_lr'. *)
  (*   { subst lr'. *)
  (*     destruct HLinv as [ [Hstrips Hcurreg] _]. *)
  (*     destruct (sweep mem reg src); destruct (is_sealed lsrcv); cbn; auto. *)
  (*     all: rewrite -Hstrips /lreg_strip !fmap_insert -/(lreg_strip lr) //=. *)
  (*     rewrite lword_get_word_next_version insert_lcap_lreg_strip; cycle 1 ; eauto. *)
  (*   } *)

  (*   destruct (incrementLPC lregs') as  [?|] eqn:Hlregs' *)
  (*   ; pose proof Hlregs' as H'lregs' *)
  (*   ; cycle 1. *)
  (*   { *)
  (*     apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'. *)
  (*     eapply updatePC_fail_incl with *)
  (*       (regs' := lreg_strip lr') (m':=mem) *)
  (*       (etbl':=etable) (ecur':=enumcur) in Hlregs' *)
  (*     ; auto *)
  (*     ; cycle 1. *)
  (*     { *)
  (*       rewrite /lreg_strip lookup_fmap. *)
  (*       subst lregs' lr'. *)
  (*       apply fmap_is_Some. *)
  (*       destruct (decide (dst = PC)); simplify_map_eq ; auto. *)
  (*       destruct (sweep mem reg src) ; simplify_map_eq ; auto. *)
  (*       destruct (is_sealed lsrcv) ; simplify_map_eq ; auto. *)
  (*       destruct (decide (src = PC)) ; simplify_map_eq ; auto. *)
  (*     } *)
  (*     rewrite Hstrip_lr' in Hlregs'. *)
  (*     match goal with *)
  (*     | Hstep : *)
  (*       match ?x with _ => _ end = (_,_) |- _ => *)
  (*         replace x with (None : option Conf) in Hstep *)
  (*           by (destruct_lword lsrcv ; eauto) *)
  (*     end *)
  (*     ; simplify_eq. *)
  (*     subst lr'. *)

  (*     iSplitR "Hφ Hmap Hmem" *)
  (*     ; [ iExists lr, lm, vmap; iFrame; auto *)
  (*       | iApply "Hφ" ; iFrame]. *)
  (*     destruct (sweep mem reg src) *)
  (*     ; destruct (is_sealed lsrcv) *)
  (*     ; subst lregs' *)
  (*     ; cbn in * *)
  (*     ; try (by iFailCore IsUnique_fail_invalid_PC_nupd) *)
  (*     ; try (by iFailCore IsUnique_fail_invalid_PC_upd). *)
  (*   } *)

  (*   (* PC has been incremented correctly *) *)
  (*   rewrite /update_reg /= in Hstep. *)
  (*   eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs' *)
  (*       as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->) *)
  (*   ; simplify_map_eq. *)
  (*   assert (dst <> PC) as Hdst by (subst lregs' ; intro ; simplify_map_eq). *)
  (*   eapply updatePC_success_incl with *)
  (*     (regs' := lreg_strip lr') (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC *)
  (*   ; auto. *)
  (*   rewrite Hstrip_lr' in HuPC. *)
  (*   rewrite HuPC in Hstep; clear HuPC. *)
  (*   match goal with *)
  (*   | Hstep : match ?x with _ => _ end = (_,_) |- _ => *)
  (*       match goal with *)
  (*       | Hstep' : context f [ Some (?a,?b) ] |- _ => *)
  (*           replace x with (Some (a,b)) in Hstep *)
  (*             by (destruct_lword lsrcv ; cbn in * ; try congruence) *)
  (*       end *)
  (*   end *)
  (*   ; subst lregs' lr' ; simplify_eq ; simplify_map_eq. *)

  (*   (* Start the different cases now *) *)
  (*   (* sweep success or sweep fail *) *)
  (*   destruct (sweep mem reg src) as [|] eqn:Hsweep; cycle 1. *)
  (*   { (* sweep is false *) *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto *)
  (*     ; first by simplify_map_eq. *)

  (*     iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*     ; [| iApply "Hφ" ; iFrame; iPureIntro; eapply IsUnique_success_false ; eauto]. *)

  (*     iExists _, lm, vmap; iFrame; auto *)
  (*     ; iPureIntro; econstructor; eauto *)
  (*     ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ] *)
  (*     ; cbn in * *)
  (*     ; last (split;eauto) *)
  (*     . *)
  (*     assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap ) as Hcur_PC. *)
  (*     { eapply lookup_weaken in HPC'' ; eauto. *)
  (*       eapply is_cur_lword_lea with (a' := a_pc1) ; cycle 1 ; eauto. *)
  (*     } *)
  (*     eapply lreg_corresponds_insert_respects; eauto. *)
  (*     eapply lreg_corresponds_insert_respects; done. *)
  (*   } *)

  (*   (* sweep is true *) *)
  (*   eapply sweep_true_specL in Hsweep; eauto. *)

  (*   destruct ( is_sealed lsrcv ) eqn:His_sealed; cbn in *; simplify_eq. *)
  (*   { *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
  (*       as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
  (*       as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)

  (*     iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*     ; [| iApply "Hφ" ; iFrame; iPureIntro ; eapply IsUnique_success_true_is_sealed; eauto] *)
  (*     ; last (by destruct Hsweep as [ ? _ ]; eauto ; eapply unique_in_registersL_mono). *)

  (*     iExists _, lm, vmap; iFrame; auto *)
  (*     ; iPureIntro; econstructor; eauto *)
  (*     ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ] *)
  (*     ; cbn in * *)
  (*     ; last (split;eauto). *)

  (*     assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap ) as Hcur_PC. *)
  (*     { eapply lookup_weaken in HPC'' ; eauto. *)
  (*       eapply is_cur_lword_lea with (a' := a_pc1) ; cycle 1 ; eauto. *)
  (*     } *)
  (*     eapply lreg_corresponds_insert_respects; eauto. *)
  (*     eapply lreg_corresponds_insert_respects; done. *)
  (*   } *)


  (*   (* case is_not_sealed *) *)
  (*   destruct_lword lsrcv ; cbn in His_sealed, Hget_lsrcv ; simplify_eq. *)
  (*   assert (p ≠ E) as Hp0_neq_E by (by intro ; simplify_eq; cbn in His_sealed) *)
  (*   ; clear His_sealed. *)
  (*   set (lsrcv := LCap p b e a v). *)
  (*   (* update version number of memory points-to *) *)
  (*   assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup). *)
  (*   opose proof *)
  (*     (state_corresponds_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ HLinv _ Hlsrc) *)
  (*     as HcurMap; first (by cbn). *)
  (*   opose proof *)
  (*     (state_corresponds_last_version_lword_region _ _ _ _ _ _ _ _ _ _ _ _  HLinv _ Hlsrc) *)
  (*     as HmemMap_maxv; first (by cbn). *)
  (*   opose proof *)
  (*     (state_corresponds_access_lword_region _ _ _ _ _ _ _ _ _ _ _ _ HLinv _ Hlsrc) *)
  (*     as HmemMap; first (by cbn). *)
  (*   destruct (update_cur_version_word_region lmem lm vmap (LCap p b e a v)) *)
  (*     as [ [lmem' lm'] vmap'] eqn:Hupd *)
  (*   ; rewrite /update_cur_version_word_region /= in Hupd. *)
  (*   iMod ((gen_heap_lmem_version_update lmem lm lmem' lm' ) with "Hm Hmem") *)
  (*     as "[Hm Hmem]"; eauto. *)
  (*   (* we destruct the cases when the registers are equals *) *)
  (*   destruct (decide (src = PC)); simplify_map_eq ; cycle 1. *)
  (*   - (* src <> PC *) *)
  (*     destruct (decide (src = dst)) ; simplify_map_eq ; cycle 1. *)
  (*     + (* src <> dst *) *)
  (*       iMod ((gen_heap_update_inSepM _ _ src (next_version_lword lsrcv)) with "Hr Hmap") *)
  (*         as "[Hr Hmap]"; eauto. *)
  (*       iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
  (*         as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)
  (*       iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
  (*         as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)


  (*       iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*       ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto] *)
  (*       ; [| eapply update_cur_version_region_valid; eauto *)
  (*         | by destruct Hsweep as [ Hunique_reg _ ]; eauto ; eapply unique_in_registersL_mono *)
  (*         ]. *)

  (*       iExists _, lm', vmap'; iFrame; auto *)
  (*       ; iPureIntro; econstructor; eauto ; cbn in * *)
  (*       ; last (eapply update_cur_version_region_lmem_corresponds ; eauto) *)
  (*       ; destruct HLinv as [Hreg_inv Hmem_inv] *)
  (*       ; last done. *)
  (*       assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap' ). *)
  (*       { eapply lookup_weaken in HPC'' ; eauto. *)
  (*         eapply lreg_corresponds_insert_respects_updated_vmap *)
  (*           with (r := PC) (lw := (LCap p1 b1 e1 a1 v1)) ; eauto; done. *)
  (*       } *)
  (*       eapply lreg_corresponds_insert_respects ; last done. *)
  (*       eapply lreg_corresponds_insert_respects ; last done. *)
  (*       replace reg with (<[ src := lword_get_word (next_version_lword lsrcv) ]> reg) *)
  (*         by (rewrite insert_id //= lword_get_word_next_version //=). *)
  (*       eapply update_cur_version_region_lreg_corresponds_src with *)
  (*         (phm := mem); eauto; try done. *)
  (*       rewrite -/(next_version_lword (LCap _ _ _ _ v)). *)
  (*       eapply update_cur_version_region_lcap_update_lword ; eauto. *)
  (*       eapply lreg_corresponds_read_iscur; eauto. *)

  (*     + (* src = dst *) *)
  (*       iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
  (*         as "[Hr Hmap]"; eauto. *)
  (*       iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
  (*         as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)
  (*       iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*       ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto] *)
  (*       ; cycle 1. *)
  (*       { eapply update_cur_version_region_valid; eauto. } *)
  (*       { by destruct Hsweep as [ Hunique_reg _ ]; eauto ; eapply unique_in_registersL_mono. } *)
  (*       { by rewrite insert_insert in H'lregs' |- *. } *)
  (*       iExists _, lm', vmap'; iFrame; auto *)
  (*       ; iPureIntro; econstructor; eauto *)
  (*       ; cbn in * *)
  (*       ; last (eapply update_cur_version_region_lmem_corresponds ; eauto) *)
  (*       ; destruct HLinv as [Hreg_inv Hmem_inv] *)
  (*       ; last done. *)
  (*       assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap' ). *)
  (*       { eapply lookup_weaken in HPC'' ; eauto. *)
  (*         eapply lreg_corresponds_insert_respects_updated_vmap *)
  (*           with (r := PC) (lw := (LCap p1 b1 e1 a1 v1)) ; eauto; last done. *)
  (*       } *)
  (*       eapply lreg_corresponds_insert_respects ; last done. *)
  (*       eapply update_cur_version_region_lreg_corresponds_src *)
  (*         with (phm := mem) ; eauto; done. *)

  (*   - (* src = PC *) *)
  (*     rewrite (insert_commute _ dst PC) //= insert_insert insert_commute //= in H'lregs'. *)
  (*     (* we update the registers with their new value *) *)
  (*     destruct (decide (dst = PC)) ; simplify_map_eq. *)
  (*     (* dst ≠ PC *) *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto *)
  (*     ; first by simplify_map_eq. *)
  (*     iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*     ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto] *)
  (*     ; [| eapply update_cur_version_region_valid; eauto *)
  (*       | by destruct Hsweep as [ Hunique_reg _ ]; eauto ; eapply unique_in_registersL_mono *)
  (*       ]. *)
  (*     iExists _, lm', vmap'; iFrame; auto *)
  (*     ; iPureIntro; econstructor; eauto ; cbn in * *)
  (*     ; last (eapply update_cur_version_region_lmem_corresponds *)
  (*           with (src := PC) ; eauto ; done) *)
  (*     ; destruct HLinv as [Hreg_inv Hmem_inv]. *)
  (*     eapply update_cur_version_region_lreg_corresponds_src with *)
  (*       (phm := mem) (lwsrc := (LCap p1 b1 e1 a1 pc_v) ); eauto; cycle 1. *)
  (*     rewrite -/((next_version_lword (LCap p1 b1 e1 a_pc1 pc_v))). *)
  (*     eapply update_cur_version_region_lcap_update_lword ; eauto. *)
  (*     eapply is_cur_lword_lea with (lw := (LCap p1 b1 e1 a1 pc_v)); eauto. *)
  (*     eapply lreg_corresponds_read_iscur; eauto. *)
  (*     by rewrite lookup_insert_ne // lookup_insert_ne //. *)
  (*     eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
  (*     split; eauto. *)
  (*     eapply lreg_corresponds_insert_respects; eauto; done. *)
  (* Qed. *)

  (* Because I don't know the whole content of the memory (only a local view), *)
  (*    any sucessful IsUnique wp-rule can have 2 outcomes: *)
  (*    either the sweep success or the sweep fails. *)

  (*   Importantly, we cannot derive any sweep success rule, because we would need *)
  (*   the entire footprint of the registers/memory. *)
  (*  *)
  Hint Resolve finz_seq_between_NoDup NoDup_logical_region : core.
  Lemma wp_isunique_success
    (Ep : coPset)
    (pc_p : Perm) (pc_b pc_e pc_a pc_a' : Addr) (pc_v : Version)
    (lw : LWord)
    (p : Perm) (b e a : Addr) (v : Version)
    (lwdst : LWord) (lws : list LWord)
    (dst src : RegName) :

    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    pc_a ∉ finz.seq_between b e -> (* TODO is that necessary ? Or can I derive it ? *)
    (pc_a + 1)%a = Some pc_a' →
    length lws = length (finz.seq_between b e) ->
    p ≠ E ->

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ dst ↦ᵣ lwdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ lws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ dst ↦ᵣ LInt 1
        ∗ src ↦ᵣ LCap p b e a (v+1)
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]]
        ∗ [[ b , e ]] ↦ₐ{ (v+1) } [[ lws ]] )
           ∨
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ dst ↦ᵣ LInt 0
          ∗ src ↦ᵣ LCap p b e a v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]] )
        }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca_notin Hpca Hlen_lws Hp φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a & >Hmap) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hrmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_cons (λ _ la lw, la ↦ₐ lw)%I (pc_a, pc_v) lw with "[Hpc_a Hmap]")
      as "Hmmap"; iFrame.
    iDestruct (big_sepL2_to_big_sepM  with "Hmmap") as "Hmmap".
    { apply NoDup_cons ; split; [| apply NoDup_logical_region].
      intro Hcontra.
      apply elem_of_list_fmap in Hcontra.
      destruct Hcontra as (? & ? & ?) ; simplify_eq.
    }
    iApply (wp_isunique with "[$Hrmap Hmmap]"); eauto ; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    rewrite -/(logical_range_map b e lws v).
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as
      [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
      | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
      | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC
      | ? ? Hfail]
    ; cycle 1.
    - (* Success is_sealed : contradiction *)
      destruct p ; simplify_map_eq.

    - (* Success false *)
      iApply "Hφ"; iRight.
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.
      iDestruct (big_sepM_insert with "Hmmap") as "[Hpc_a Hmmap]"
      ; first (eapply logical_region_notin; eauto).
      iFrame.
      iApply (big_sepM_to_big_sepL2 with "Hmmap").
      eapply NoDup_logical_region.
      by rewrite map_length.

    - (* Fail : contradiction *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto; solve_addr.

    - (* Success true *)
      iApply "Hφ"; iLeft.

      (* Registers *)
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca
          by (eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq).

      assert ( logical_range_map b0 e0 lws v0 ⊆ mem' )
        as Hmem'_be.
      {
        eapply is_valid_updated_lmemory_lmem_incl; eauto.
        eapply is_valid_updated_lmemory_insert; eauto.
        eapply logical_range_notin; eauto.
        eapply Forall_forall; intros a Ha.
        eapply logical_range_version_neq; eauto; lia.
      }
      assert
        (logical_range_map b0 e0 lws (v0 + 1) ⊆ mem')
        as Hmem'_be_next.
      { clear -Hupd Hpca_notin Hlen_lws.
        (* TODO extract as a lemma *)
        eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
        assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be]
            by (eapply logical_range_map_some_inv; eauto) ; simplify_eq.
        destruct Hupd.
        eapply lookup_weaken; last eauto.
        rewrite update_version_region_preserves_lmem_next; eauto.
        all: rewrite lookup_insert_ne //=; last (intro ; set_solver).
        erewrite logical_range_map_lookup_versions; eauto.
        eapply logical_range_version_neq; eauto; lia.
      }

      rewrite -(insert_id mem' (pc_a, pc_v) lw); auto.
      iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame.
      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be
      ; last (by eapply logical_region_notin; eauto).
      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be).
      iSplitL "Hrange".
      { iApply big_sepM_to_big_sepL2; last iFrame; eauto; by rewrite map_length. }
      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next
      ; last (eapply logical_region_notin ; eauto).
      eapply delete_subseteq_list_r
        with (m3 := list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws))
        in Hmem'_be_next
      ; eauto
      ; last by eapply update_logical_memory_region_disjoint.
      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be_next); iClear "Hmmap".
      iApply big_sepM_to_big_sepL2; last iFrame; eauto; by rewrite map_length.

  Qed.


  Lemma wp_isunique_success'
    (Ep : coPset)
    (pc_p : Perm) (pc_b pc_e pc_a pc_a' : Addr) (pc_v : Version)
    (lw : LWord)
    (p : Perm) (b e a : Addr) (v : Version)
    (lwdst : LWord)
    (dst src : RegName) :

    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    pc_a ∉ finz.seq_between b e -> (* TODO is that necessary ? Or can I derive it ? *)
    (pc_a + 1)%a = Some pc_a' →
    p ≠ E ->

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ dst ↦ᵣ lwdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ dst ↦ᵣ LInt 1
        ∗ src ↦ᵣ LCap p b e a (v+1)
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ (∃ lws , [[ b , e ]] ↦ₐ{ (v+1) } [[ lws ]] ))
           ∨
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ dst ↦ᵣ LInt 0
          ∗ src ↦ᵣ LCap p b e a v
          ∗ (pc_a, pc_v) ↦ₐ lw )
        }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca_notin Hpca Hp φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hrmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmmap".
    iApply (wp_isunique with "[$Hrmap Hmmap]"); eauto ; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as
      [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
      | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
      | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hmem' Hincr_PC
      | ? ? Hfail]
    ; cycle 1.
    - (* Success is_sealed : contradiction *)
      destruct p ; simplify_map_eq.

    - (* Success false *)
      iApply "Hφ"; iRight.
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.
      iDestruct (big_sepM_insert with "Hmmap") as "[Hpc_a Hmmap]"
      ; first by simplify_map_eq.
      iFrame.

    - (* Fail : contradiction *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto; solve_addr.

    - (* Success true *)
      iApply "Hφ"; iLeft.

      (* Registers *)
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca.
      { eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq. }

      assert (
          exists lws,
            length lws = length (finz.seq_between b0 e0) /\
              logical_range_map b0 e0 lws (v0 + 1) ⊆ mem')
        as (lws & Hlen_lws & Hmem'_be_next).
      { destruct Hupd as (_ & _ &Hupd) ; eapply logical_region_map_inv ; eauto. }

      rewrite -(insert_id mem' (pc_a, pc_v) lw); auto.
      iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame.

      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next
      ; eauto
      ; last (eapply logical_region_notin; eauto).
      iExists lws.

      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be_next); iClear "Hmmap".
      iApply big_sepM_to_big_sepL2; last iFrame; eauto.
      by rewrite map_length.
  Qed.

  (* TODO merge wp_opt from Dominique's branch and use it *)
  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
