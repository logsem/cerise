From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.
From cap_machine.proofmode Require Export region register_tactics.

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

  (* TODO @June: keep the lemma around,
     until doing the proof in a `wp_opt2` style
   *)
  Lemma incrementLPC_incrementPC_some regs regs' :
    incrementLPC regs = Some regs' ->
    incrementPC (lreg_strip regs) = Some (lreg_strip regs').
  Proof.
    rewrite /incrementPC /incrementLPC.
    intros Hlpc.
    rewrite /lreg_strip lookup_fmap; cbn.
    destruct (regs !! PC) as [lw|] eqn:Heq ; rewrite Heq; cbn in *; last done.
    destruct_lword lw; cbn in *; try done.
    destruct (a + 1)%a; last done.
    simplify_eq.
    by rewrite fmap_insert.
  Qed.

  Lemma incrementLPC_incrementPC_none regs :
    incrementLPC regs = None <-> incrementPC (lreg_strip regs) = None.
  Proof.
    intros.
    rewrite /incrementPC /incrementLPC.
    rewrite /lreg_strip lookup_fmap; cbn.
    destruct (regs !! PC) as [LX|] eqn:Heq ; rewrite Heq; cbn; last done.
    destruct LX ; cbn ; [(clear; firstorder) | | (clear; firstorder)].
    destruct sb as [? ? ? a' | ] ; eauto; cbn; last done.
    destruct (a' + 1)%a eqn:Heq'; done.
  Qed.

  Lemma incrementLPC_fail_updatePC regs m etbl ecur:
    incrementLPC regs = None ->
    updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} = None.
  Proof.
    intro Hincr. apply incrementLPC_incrementPC_none in Hincr.
    by apply incrementPC_fail_updatePC.
  Qed.


  Lemma incrementLPC_success_updatePC regs m etbl ecur regs' :
    incrementLPC regs = Some regs' ->
    ∃ p b e a a' (v : Version),
      regs !! PC = Some (LCap p b e a v) ∧
        (a + 1)%a = Some a' ∧
        updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} =
          Some (NextI,
              {| reg := (<[PC:=WCap p b e a']> (lreg_strip regs));
                mem := m;
                etable := etbl ;
                enumcur := ecur |})
      ∧ regs' = <[ PC := (LCap p b e a' v) ]> regs.
  Proof.
    intro Hincr.
    opose proof (incrementLPC_incrementPC_some _ _ Hincr) as HincrPC.
    eapply (incrementPC_success_updatePC _ m etbl ecur) in HincrPC.
    destruct HincrPC as (p'&b'&e'&a''&a'''&Hregs&Heq&Hupd&Hregseq).
    rewrite /incrementLPC in Hincr.
    destruct (regs !! PC) as [wpc |]; last done.
    destruct_lword wpc; try done.
    destruct (a + 1)%a as [a'|] eqn:Heq'; last done; simplify_eq.
    rewrite /lreg_strip fmap_insert //= -/(lreg_strip regs)  in Hregseq.
    exists p, b, e, a, a', v.
    repeat (split; try done).
    by rewrite Hupd Hregseq.
  Qed.


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
    get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword lwsrc ]> lregs)) = None ->
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_nupd (lwsrc: LWord) (z : Z):
    lregs !! src = Some lwsrc ->
    incrementLPC (<[ dst := LInt z ]> lregs) = None ->
    IsUnique_fail lregs lmem dst src.

  Inductive IsUnique_spec
    (lregs: LReg) (lmem : LMem) (dst src : RegName)
    (lregs': LReg) (lmem' : LMem) : cap_lang.val → Prop :=

  (* WPIsUniqueSuccessFull success branch *)
  | IsUnique_success_true_cap (p : Perm) (b e a : Addr) glmem (v : Version) :
    lregs !! src = Some (LCap p b e a v) ->
    p ≠ E ->
    (* we update the region of memory with the new version *)
    is_valid_updated_lmemory glmem lmem (finz.seq_between b e) v lmem' ->
    (finz.seq_between b e) ## reserved_addresses ->
    (* specific instance of unique_in_registers *)
    unique_in_registersL lregs (Some src) (LCap p b e a v) ->

    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword (LCap p b e a v) ]> lregs)) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_true_is_sealed (lwsrc : LWord) :
    lregs !! src = Some lwsrc ->
    is_sealed lwsrc ->
    (* specific instance of unique_in_registers *)
    unique_in_registersL lregs (Some src) lwsrc ->
    lmem' = lmem ->
    incrementLPC (<[ dst := LInt 1 ]> lregs) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  (* WPIsUniqueSuccessFull failure branch *)
  | IsUnique_success_false (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
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
        ∗ src        ↦ᵣ (p,b,b+2,_,v)
        ∗ dst        ↦ᵣ _
        ∗ (b, v)     ↦ₐ lwb
    }}}
    ->
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v+1)
        ∗ dst        ↦ᵣ LInt 1
        ∗ (b, v)     ↦ₐ lwb

        ∗         (b, v+1)   ↦ₐ lwb
        ∗ ∃ lwb', (b+1, v+1) ↦ₐ lwb'
    }}}


    --- E-cap, no ownership over part of the region  ---
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

  Definition allows_sweep (lregs : LReg) (r : RegName) :=
    ∀ p b e a v, lregs !! r = Some (LCap p b e a v) -> p ≠ E -> (finz.seq_between b e) ## reserved_addresses.

  Definition exec_optL_IsUnique
    (lregs : LReg) (lmem : LMem)
    (dst : RegName) (src : RegName)
    (bsweep : bool) : option LReg :=
    lwsrc        ← lregs !! src ;
    _            ← get_wlcap_slcap lwsrc ;
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

  Definition full_own_mem (lmem : LMem) : LMemF := (λ y : LWord, (DfracOwn 1, y)) <$> lmem.

  (* TODO generalise and move *)
  Lemma fmap_forall_inv (lmt : LMemF) :
    map_Forall (λ (_ : LAddr) (a : dfrac * LWord), a.1 = DfracOwn 1) lmt ->
    exists lm, lmt = (full_own_mem lm).
  Proof.
    induction lmt using map_ind; intro Hall.
    - exists ∅. by rewrite /full_own_mem fmap_empty.
    - assert (x.1 = DfracOwn 1) as Hx by (apply map_Forall_insert_1_1 in Hall; auto).
      apply map_Forall_insert_1_2 in Hall; auto.
      apply IHlmt in Hall.
      destruct Hall as (lm' & Hall).
      exists (<[i := (snd x)]> lm').
      rewrite /full_own_mem fmap_insert /=.
      by destruct x ; cbn in * ; subst.
  Qed.

  (* TODO move *)
  Lemma wp2_get_wcap_scap {Φf : iProp Σ} {w Φs} :
         Φf ∧ (∀ p b e a v, Φs (p, b, e, a, v) (p, b, e, a))
      ⊢ wp_opt2 (get_wlcap_slcap w) (get_wcap_scap (lword_get_word w)) Φf Φs.
  Proof.
    iIntros "HΦ".
    destruct w as [ | [ | ] | [] [ | ] ]; cbn.
    all: try now rewrite bi.and_elim_l.
    all: try now rewrite bi.and_elim_r.
  Qed.

  Lemma state_interp_transient_unique_in_lregs
    {σ σt lreg lrt lmemf lmt src lwsrc}:
    sweep_reg (mem σ) (reg σ) src = true ->
    lreg !! src = Some lwsrc ->
    state_interp_transient σ σt lreg lrt lmemf lmt ⊢
    ⌜ unique_in_registersL lreg (Some src) lwsrc ⌝.
  Proof.
    iIntros (Hsweep Hsrc) "Hσrm".
    iDestruct (transiently_abort with "Hσrm") as "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm vmap cur_tb prev_tb all_tb) "(Hr & Hm & %Hcurtbeq & Hcurtb & Hprevtb & Halltb & Hecauth & %Hcurprevdisj & %Hcompl & %Hcurprevdisj2 & %Hcompl2 & %HLinv)"; simpl in HLinv.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hregs_incl".
    iPureIntro.
    eapply unique_in_registersL_mono; first done.
    eapply lookup_weaken in Hsrc; eauto.
    eapply state_corresponds_unique_in_registers; eauto.
    eapply (sweep_reg_spec _ _ _ _ Hsweep) ; cbn.
    eapply state_corresponds_reg_get_word; eauto.
    eapply state_corresponds_reg_get_word; eauto.
  Qed.

  (* TODO generalise to not just LMem + find better name + move iris_extra *)
  Lemma map_full_own (lm : LMem) :
    ([∗ map] k↦y ∈ lm, k ↦ₐ y)%I
    ⊣⊢ ([∗ map] la↦dw ∈ (full_own_mem lm), la ↦ₐ{dw.1} dw.2).
  Proof.
    induction lm using map_ind.
    - rewrite /full_own_mem fmap_empty.
      by iSplit; iIntros "Hmem".
    - rewrite /full_own_mem fmap_insert.
      iSplit; iIntros "Hmem".
      + iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"; first done.
        iDestruct (IHlm with "Hmem") as "Hmem".
        iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
        by rewrite lookup_fmap fmap_None.
        by cbn.
      + iDestruct (big_sepM_insert with "Hmem") as "[Hi Hmem]"
        ; first (by rewrite lookup_fmap fmap_None).
        iDestruct (IHlm with "Hmem") as "Hmem".
        cbn.
        by iDestruct (big_sepM_insert with "[Hi Hmem]") as "Hmem"; try iFrame.
  Qed.

  (* TODO move *)
  Lemma update_version_addr_next
    (glmem llmem : LMem) (a : Addr) (v : Version) (lw : LWord) :
    glmem !! (a, v) = Some lw ->
    glmem !! (a, v + 1) = None ->
    update_version_addr glmem a v llmem !! (a, v+1) = Some lw.
  Proof.
    intros Hlw Hlw_max.
    by rewrite /update_version_addr Hlw ; simplify_map_eq.
  Qed.

  (* TODO move *)
  Lemma is_valid_updated_lmemory_update_version_region
    (glmem llmem : LMem) (la : list Addr) (v : Version) :
    llmem ⊆ glmem ->
    NoDup la ->
    Forall (λ a : Addr, glmem !! (a, v + 1) = None) la ->
    Forall (λ a' : Addr, is_Some (glmem !! (a', v))) la ->
    is_valid_updated_lmemory glmem llmem la v
      (update_version_region glmem la v llmem).
  Proof.
    induction la as [|a la] ; intros Hincl HnoDup Hmax Hsome ; destruct_cons ; cbn
    ; rewrite /is_valid_updated_lmemory //=.
    destruct IHla as (_ & Hla_max & Hla_upd) ; try by destruct_cons.
    split; [|split] ; cbn.
    - done.
    - apply Forall_cons; split; auto. eapply lookup_weaken_None; eauto.
    - rewrite -/(update_version_region glmem la v llmem).
      apply Forall_cons; split; auto.
      + destruct Hsome_a as [lw Hlw].
        exists lw.
        erewrite update_version_addr_next
        ; eauto
        ; rewrite update_version_region_notin_preserves_lmem; eauto.
      + eapply Forall_impl ; try eapply Hla_upd; cbn.
        intros a' [lw' Hlw'].
        destruct (decide (a = a')); subst.
        * rewrite update_version_region_notin_preserves_lmem in Hlw'; eauto.
          exfalso.
          eapply lookup_weaken in Hlw' ; eauto.
          by rewrite Hlw' in Hmax_a.
        * exists lw'; rewrite update_version_addr_lookup_neq; eauto.
  Qed.

  Lemma update_state_interp_next_version
    {σr σm lr lm vmap lregs lmem src lwsrc p b e a v} :

    let la := finz.seq_between b e in
    Forall (λ a0 : Addr, a0 ∉ reserved_addresses) la ->
    sweep_reg σm σr src = true ->
    lregs !! src = Some lwsrc ->
    get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
    gen_heap_interp lr ∗ gen_heap_interp lm ∗
      ⌜state_phys_log_corresponds σr σm lr lm vmap⌝%I
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem, k ↦ₐ{y.1} y.2)
      ⊢ |==>
      let lmem' := update_version_region lm la v lmem in
      let lm' := update_version_region lm la v lm in
      let lregs' := (<[src:=next_version_lword lwsrc]> lregs) in
      let lr' := (<[src:=next_version_lword lwsrc]> lr) in
      let vmap' := update_version_region_vmap la v vmap in
      ⌜ is_valid_updated_lmemory lm lmem (finz.seq_between b e) v lmem'⌝ ∗
        gen_heap_interp lr' ∗ gen_heap_interp lm' ∗
        ⌜state_phys_log_corresponds σr σm lr' lm' vmap' ⌝%I ∗ ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem', k ↦ₐ{y.1} y.2).
  Proof.
    iIntros (la Hnotres Hsweep Hlsrc Hlcap_wsrc) "(Hr & Hm & %Hcorr & Hregs & Hmem)".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iDestruct (map_full_own with "Hmem") as "Hmem".
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ src (next_version_lword lwsrc)) with "Hr Hregs") as
      "[Hr Hregs]"; eauto.
    assert (lr !! src = Some lwsrc) as Hsrc by (eapply lookup_weaken in Hlsrc ; eauto).
    assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).
    opose proof
      (state_corresponds_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ Hcorr _ Hsrc)
      as HcurMap ; first (by cbn).
    opose proof
      (state_corresponds_last_version_lword_region _ _ _ _ _ _ _ _ _ _ _ _  Hcorr _ Hsrc)
      as HmemMap_maxv; first (by cbn).
    opose proof
      (state_corresponds_access_lword_region _ _ _ _ _ _ _ _ _ _ _ _ Hcorr _ Hsrc)
      as HmemMap; first (by cbn).
    set (lmem' := update_version_region lm la v lmem).
    set (lm' := update_version_region lm la v lm).
    (* set (lregs' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lregs))). *)
    (* set (lr' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lr))). *)
    set (lregs' := <[src:=next_version_lword lwsrc]> lregs).
    set (lr' := <[src:=next_version_lword lwsrc]> lr).
    set (vmap' := update_version_region_vmap la v vmap).
    iMod ((gen_heap_lmem_version_update lm lmem lm lmem' _ vmap _ (finz.seq_between b e) v)
           with "Hm Hmem") as "[Hm Hmem]"; eauto.
    iModIntro.
    iSplitR.
    { iPureIntro. now apply is_valid_updated_lmemory_update_version_region. }
    iFrame.
    iSplitR "Hmem"; last by rewrite map_full_own.
    iPureIntro.
    assert (lr !! src = Some lwsrc) as Hsrc' by (eapply lookup_weaken; eauto).
    eapply sweep_true_specL in Hsweep; eauto.
    split.
    + rewrite (_: σr = (<[src:=(lword_get_word (next_version_lword lwsrc))]> σr)).
      * eapply update_version_region_lreg_corresponds_src; eauto.
        eapply update_version_word_region_update_lword; eauto.
        eapply lreg_corresponds_read_iscur; eauto.
        by destruct Hcorr.
      * rewrite lword_get_word_next_version.
        rewrite insert_id; first done.
        eapply state_corresponds_reg_get_word; eauto.
    + destruct (id Hcorr).
      eapply update_version_region_preserves_mem_corresponds; eauto.
      destruct (Hsweep Hsrc').
      eapply unique_in_machine_no_accessL; eauto.
      eapply lreg_corresponds_read_iscur; eauto.
  Qed.

  Lemma wp_isunique Ep
    pc_p pc_b pc_e pc_a pc_v
    (dst src : RegName) lw lmem lregs :
    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsUnique dst src) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allows_sweep lregs src ->

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ IsUnique_spec lregs lmem dst src lregs' lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    (* iIntros (Hinstr Hvpc HPC Dregs Hmem_pc Hallow φ) "(>Hmem & >Hmap) Hφ". *)
    (* apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc. *)
    (* iApply wp_lift_atomic_head_step_no_fork; auto. *)
    (* iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl. *)
    (* iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all) *)
    (*     "(Hr & Hm *)
    (*      & -> & Htbl_cur & Htbl_prev & Htbl_all *)
    (*      & HEC *)
    (*      & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4 *)
    (*      & %HLinv)" *)
    (* ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4. *)

    (* (* Derive necessary register values in r *) *)
    (* iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)
    (* have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs. *)
    (* specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
    (* odestruct (Hri dst) as [ldstv [Hldst' Hldst] ]; first by set_solver+. *)
    (* odestruct (Hri src) as [lsrcv [Hlsrc' Hlsrc] ]; first by set_solver+. *)

    (* (* Derive necessary memory *) *)
    (* iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem. *)
    (* iDestruct (gen_mem_valid_inSepM lmem lm with "Hm Hmem") as %Hma; eauto. *)

    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc Hallowsweep φ) "(>Hmem & >Hregs) Hφ".
    (*  extract the pc  *)
    rewrite (big_sepM_delete). 2: apply Hmem_pc. iDestruct "Hmem" as "[Hpc_a Hmem]".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hregs $Hpc_a Hmem Hφ]").
    iModIntro.
    iIntros (σ) "(Hσ & Hregs & Hpca)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) _".

    iCombine "Hpca Hmem" as "Hmem".
    rewrite -(big_sepM_delete (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y) _ _ _ Hmem_pc).

  (*   (* src contains a capability *) *)
  (*   destruct (is_lcap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *. *)
  (*   { (* Fail : not a capability *) *)
  (*     destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv. *)
  (*     all: simplify_map_eq. *)
  (*     all: (iSplitR "Hφ Hmap Hmem" *)
  (*           ; [ iExists lr, lm, vmap,_,_,_; iFrame; auto *)
  (*             | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_cap *)
  (*          ]). *)
  (*   } *)
  (*   destruct (get_is_lcap_inv lsrcv Hlsrcv) as (p & b & e & a & v & Hget_lsrcv). *)

  (*   set (lregs' := (<[ dst := LInt (if (sweep_reg mem reg src) then 1 else 0) ]> *)
  (*                     (if (andb (sweep_reg mem reg src) (negb (is_sealed lsrcv)) ) *)
  (*                      then (<[ src := next_version_lword lsrcv]> lregs) *)
  (*                      else lregs))). *)
  (*   set (lr' := (<[ dst := LInt (if (sweep_reg mem reg src) then 1 else 0) ]> *)
  (*                  (if (andb (sweep_reg mem reg src) (negb (is_sealed lsrcv)) ) *)
  (*                   then (<[ src := next_version_lword lsrcv]> lr) *)
  (*                   else lr))). *)
  (*   assert (lreg_strip lregs' ⊆ lreg_strip lr') as Hlregs'_in_lr'. *)
  (*   { subst lregs' lr'. *)
  (*     apply map_fmap_mono, insert_mono. *)
  (*     destruct (sweep_reg mem reg src); destruct (is_sealed lsrcv); cbn; auto. *)
  (*     apply insert_mono; auto. *)
  (*   } *)

  (*   assert ( (lreg_strip lr') = *)
  (*              (<[ dst := WInt (if (sweep_reg mem reg src) then 1 else 0) ]> reg)) *)
  (*     as Hstrip_lr'. *)
  (*   { subst lr'. *)
  (*     destruct HLinv as [ [Hstrips Hcurreg] _]. *)
  (*     destruct (sweep_reg mem reg src); destruct (is_sealed lsrcv); cbn; auto. *)
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
  (*       destruct (sweep_reg mem reg src) ; simplify_map_eq ; auto. *)
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
  (*     ; [ iExists lr, lm, vmap,_,_,_; iFrame; auto *)
  (*       | iApply "Hφ" ; iFrame]. *)
  (*     destruct (sweep_reg mem reg src) *)
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
  (*   destruct (sweep_reg mem reg src) as [|] eqn:Hsweep; cycle 1. *)
  (*   { (* sweep is false *) *)
  (*     iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
  (*     iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto *)
  (*     ; first by simplify_map_eq. *)

  (*     iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
  (*     ; [| iApply "Hφ" ; iFrame; iPureIntro; eapply IsUnique_success_false ; eauto]. *)

  (*     iExists _, lm, vmap,_,_,_; iFrame; auto *)
  (*     ; iPureIntro; econstructor; eauto *)
  (*     ; repeat (split ; first done) *)
  (*     ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ] *)
  (*     ; cbn in * *)
  (*     ; last (split;eauto) *)
  (*     ; last done *)
  (*     . *)
  (*     assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap ) as Hcur_PC. *)
  (*     { eapply lookup_weaken in HPC'' ; eauto. *)
  (*       eapply is_cur_lword_lea with (a' := a_pc1) ; cycle 2 ; eauto ; apply isWithin_refl. *)
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

  (*     iExists _, lm, vmap,_,_,_; iFrame; auto *)
  (*     ; iPureIntro; econstructor; eauto *)
  (*     ; repeat (split ; first done) *)
  (*     ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ] *)
  (*     ; cbn in * *)
  (*     ; last (split;eauto) *)
  (*     ; last done. *)

  (*     assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap ) as Hcur_PC. *)
  (*     { eapply lookup_weaken in HPC'' ; eauto. *)
  (*       eapply is_cur_lword_lea with (a' := a_pc1) ; cycle 2 ; eauto ; apply isWithin_refl. *)
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
  (*   assert (not_reserved_addresses_word (LCap p b e a v)) as Hreserved. *)
  (*   { rewrite /allows_sweep in Hallow. *)
  (*     rewrite /not_reserved_addresses_word /=. *)
  (*     eapply Hallow; eauto. *)
  (*   } *)

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

  (*       iExists _, lm', vmap',_,_,_; iFrame; auto *)
  (*       ; iPureIntro *)
  (*       ; repeat (split ; first done) *)
  (*       ; econstructor; eauto ; cbn in * *)
  (*       ; last (eapply update_cur_version_region_lmem_corresponds ; eauto) *)
  (*       ; destruct HLinv as [Hreg_inv Hmem_inv] *)
  (*       ; last done. *)
  (*       2: eauto. *)
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
  (*       iExists _, lm', vmap',_,_,_; iFrame; auto *)
  (*       ; iPureIntro *)
  (*       ; repeat (split ; first done) *)
  (*       ; econstructor; eauto ; cbn in * *)
  (*       ; last (eapply update_cur_version_region_lmem_corresponds ; eauto) *)
  (*       ; destruct HLinv as [Hreg_inv Hmem_inv] *)
  (*       ; last done. *)
  (*       2: done. *)
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
  (*     iExists _, lm', vmap',_,_,_; iFrame; auto *)
  (*     ; iPureIntro *)
  (*     ; repeat (split ; first done) *)
  (*     ; econstructor; eauto ; cbn in * *)
  (*     ; last (eapply update_cur_version_region_lmem_corresponds *)
  (*           with (src := PC) ; eauto ; done) *)
  (*     ; destruct HLinv as [Hreg_inv Hmem_inv]. *)
  (*     eapply update_cur_version_region_lreg_corresponds_src with *)
  (*       (phm := mem) (lwsrc := (LCap p1 b1 e1 a1 pc_v) ); eauto; cycle 1. *)
  (*     rewrite -/((next_version_lword (LCap p1 b1 e1 a_pc1 pc_v))). *)
  (*     eapply update_cur_version_region_lcap_update_lword ; eauto. *)
  (*     eapply is_cur_lword_lea with (lw := (LCap p1 b1 e1 a1 pc_v)); eauto; first apply isWithin_refl. *)
  (*     eapply lreg_corresponds_read_iscur; eauto. *)
  (*     by rewrite lookup_insert_ne // lookup_insert_ne //. *)
  (*     eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
  (*     split; eauto. *)
  (*     eapply lreg_corresponds_insert_respects; eauto; done. *)
  (* Qed. *)

  (* (* Because I don't know the whole content of the memory (only a local view), *) *)
  (* (*    any sucessful IsUnique wp-rule can have 2 outcomes: *) *)
  (* (*    either the sweep success or the sweep fails. *) *)

  (* (*   Importantly, we cannot derive any sweep success rule, because we would need *) *)
  (* (*   the entire footprint of the registers/memory. *) *)
  (* (*  *) *)
    set (bsweep := (sweep_reg (mem σ) (reg σ) src)).
    iApply (wp_wp2 (φ1 := exec_optL_IsUnique lregs lmem dst src bsweep) (φ2 := _)).
    iModIntro.
    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iDestruct "Hσ" as "(%lr & %lm & %vmap & %cur_tb & %prev_tb & %all_tb & Hlr & Hlm & %Hetable & Hcur_tb & Hprev_tb & Hall_tb & Hecauth & %Hdomcurtb & %Hdomtbcompl & %Htbdisj & %Htbcompl & %Hcorr0)".
    iDestruct (gen_heap_valid_inclSepM with "Hlm Hmem") as "%Hlmsub".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hregs") as "%Hlrsub".
    iCombine "Hlr Hlm Hregs Hmem" as "Hσ". 
    iDestruct (transiently_intro with "Hσ") as "Hσ".
    iApply wp_opt2_mono2.
    iSplitL "Hφ Hσ Hcur_tb Hprev_tb Hall_tb Hecauth".
    2: {
      iApply wp2_reg_lookup5; eauto.
      set_solver.
    }
    iSplit; first now iIntros "%Htr".  
    iIntros (lsrcv srcv) "-> %Hlsrcv %Hsrcv".
    assert (lr !! src = Some lsrcv) as Hlrsrc by eapply (lookup_weaken _ _ _ _ Hlsrcv Hlrsub).
    iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    iApply wp_opt2_mono2.
    iSplitL "Hφ Hσ Hcur_tb Hprev_tb Hall_tb Hecauth".
    2: now iApply (wp2_get_wcap_scap (Φf := True%I) (w := lsrcv) (Φs := fun _ _ => True)%I).
    iSplit.
    { (* src register does not contain a capability *) 
      iIntros "_ %Hislcap %Hwicos".
      iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem)".
      iSplitR "Hφ Hregs Hmem".
      iExists lr, lm, vmap, _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
      apply IsUnique_failure; eauto.
      eapply (IsUnique_fail_cap _ _ _ _ _ Hlsrcv).
      destruct lsrcv as [z|[? ? ? ? ?|? ? ? ?]|? [? ? ? ? ?|? ? ? ?] ];
        now inversion Hislcap.
    }
    iIntros (u1 u2) "_ %Hlclsrcv %Hwicos".
    destruct u1 as ((((p & b) & e) & a) & v).
    destruct u2 as (((p' & b') & e') & a').
    rewrite updatePC_incrementPC.
    
    destruct bsweep eqn:Hsweep.
    - (* the sweep has succeeded *)
      destruct (is_sealed lsrcv) eqn:Hslsrcv.
      + (* a sealed capability, we do not want to update the version map *)
        iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
        iApply wp_opt2_mono2.
        iSplitL "Hφ  Hcur_tb Hprev_tb Hall_tb Hecauth".
        2: {
          iApply transiently_wp_opt2.
          iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem)".
          iMod (gen_heap_update_inSepM _ _ dst (LInt 1) with "Hσr Hregs") as "(Hσr & Hregs)".
          { rewrite -elem_of_dom. set_solver. }
          iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
          iApply (wp_opt2_frame with "Hσm").
          iApply (wp_opt2_frame with "Hmem").
          iModIntro.
          iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
          { assert (PC ∈ dom lregs) by now rewrite elem_of_dom HPC. now set_solver. }
          subst bsweep. rewrite Hsweep.
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 1) eq_refl); cbn; eauto.
        }
        iSplit.
        { iIntros "Htr %HincLPC %HincPC".
          iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs & Hmem)".
          iSplitR "Hφ Hregs Hmem".
          iExists lr, lm, vmap, _, _, _; iFrame; now iPureIntro.
          iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
          apply IsUnique_failure; eauto.
          eapply IsUnique_fail_invalid_PC_nupd; eauto.
        }
        iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
        iApply wp2_val.
        iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %lr2 & Hσr & %Hcorr2 & Hregs)".
        iModIntro.
        iSplitR "Hφ Hregs Hmem".
        iExists _, _, _, _, _, _; iFrame; iPureIntro; intuition; cbn; eassumption.
        iApply ("Hφ" with "[$Hregs $Hmem]").
        iPureIntro.
        eapply IsUnique_success_true_is_sealed; eauto.
        eapply unique_in_registersL_mono; eauto.
        eapply state_corresponds_unique_in_registers; eauto.
        eapply sweep_reg_spec; eauto.
      + (* an unsealed capability, we do want to update the version map *)
        assert (lsrcv = LCap p b e a v /\ p ≠ E) as  [-> HnpE].
        { now destruct lsrcv as [z|[ [ | | | | | ] ? ? ? ?|? ? ? ?]|? [? ? ? ? ?|? ? ? ?] ];
            inversion Hlclsrcv. }
        iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
        iApply wp_opt2_mono2.
        iSplitL "Hφ Hcur_tb Hprev_tb Hall_tb Hecauth".
        2: {
          iApply transiently_wp_opt2.
          iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem)".
          rewrite map_full_own.
          iMod (update_state_interp_next_version with "[$Hσr $Hσm $Hregs $Hmem]") as "(%Hvm & Hσr & Hσm & #Hcorr' & Hregs & Hmem)"; eauto. 
          admit. (* DOMI: How do we know none of the addresses are reserved? Do the operational semantics need to check for this? *)
          iMod (gen_heap_update_inSepM _ _ dst (LInt 1) with "Hσr Hregs") as "(Hσr & Hregs)".
          { rewrite -elem_of_dom. set_solver. }
          iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
          iApply (wp_opt2_frame with "Hσm").
          iApply (wp_opt2_frame with "Hmem").
          iApply (wp_opt2_frame with "Hcorr'").
          iDestruct "Hcorr'" as "%Hcorr'".
          iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
          { assert (PC ∈ dom lregs) by now rewrite elem_of_dom HPC. now set_solver. }
          subst bsweep. rewrite Hsweep.
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 1) eq_refl); cbn; eauto.
        }
        iSplit.
        { iIntros "Htr %HincLPC %HincPC".
          iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs & Hmem)".
          iSplitR "Hφ Hregs Hmem".
          iExists lr, lm, vmap, _, _, _; now iFrame.
          iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
          apply IsUnique_failure; eauto.
          eapply IsUnique_fail_invalid_PC_upd; eauto.
        }
        iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
        iApply wp2_val.
        iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %Hcorr & %lr2 & Hσr & %Hcorr2 & Hregs)".
        iModIntro.
        iSplitR "Hφ Hregs Hmem".
        iExists _, _, _, _, _, _; now iFrame.
        rewrite -map_full_own.
        iApply ("Hφ" with "[$Hregs $Hmem]").
        iPureIntro.
        eapply IsUnique_success_true_cap; eauto.
        eapply is_valid_updated_lmemory_update_version_region;
        eauto using is_valid_updated_lmemory_update_version_region, lookup_weaken, finz_seq_between_NoDup, state_corresponds_last_version_lword_region, state_corresponds_access_lword_region.
        eapply unique_in_registersL_mono; eauto.
        eapply state_corresponds_unique_in_registers; eauto.
        eapply sweep_reg_spec; eauto.
    - (* the memory sweep has failed *)
      subst bsweep. rewrite Hsweep.
      iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
      iApply wp_opt2_mono2.
      iSplitL "Hφ Hcur_tb Hprev_tb Hall_tb Hecauth".
      2: {
        iApply transiently_wp_opt2.
        iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem)".
        iModIntro.
        iApply wp_opt2_mod.
        iMod (gen_heap_update_inSepM _ _ dst (LInt 0) with "Hσr Hregs") as "(Hσr & Hregs)".
        { rewrite -elem_of_dom. set_solver. }
        iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
        iApply (wp_opt2_frame with "Hσm").
        iApply (wp_opt2_frame with "Hmem").
        iModIntro.
        iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
        { assert (PC ∈ dom lregs) by now rewrite elem_of_dom HPC. now set_solver. }
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 0) eq_refl); cbn; eauto.
      }
      iSplit.
      { iIntros "Htr %HincLPC %HincPC".
        iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs & Hmem)".
        iSplitR "Hφ Hregs Hmem".
        iExists lr, lm, vmap, _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        apply IsUnique_failure; eauto.
        eapply IsUnique_fail_invalid_PC_nupd; eauto.
      }
      iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
      iApply wp2_val.
      iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %lr2 & Hσr & %Hcorr2 & Hregs)".
      iModIntro.
      iSplitR "Hφ Hregs Hmem ".
      iExists _, _, _, _, _, _; iFrame; iPureIntro; intuition eassumption.
      iApply ("Hφ" with "[$Hregs $Hmem]").
      iPureIntro.
      eapply IsUnique_success_false; eauto.
  Admitted.

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
    finz.seq_between b e ## reserved_addresses ->

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
    iIntros (Hinstr Hvpc Hpca_notin Hpca Hlen_lws Hp Hreserved φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a & >Hmap) Hφ".
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
    { rewrite /allows_sweep. intros p' b' e' a' v' ? ?.
      by simplify_map_eq.
    }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    rewrite -/(logical_range_map b e lws v).
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as
      (* [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hreserved' Hunique_regs Hincr_PC *)
      (* | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC *)
      [ ? ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hnotres Hunique_regs Hincr_PC
      | ? Hlwsrc Hnot_sealed Hmem' Hunique_regs Hincr_PC
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
      (* destruct Hupd as ( lm & Hlm_incl & Hvalid ). *)

      (* assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca *)
      (*     by (eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq). *)

      (* assert ( logical_range_map b0 e0 lws v0 ⊆ mem' ) *)
      (*   as Hmem'_be. *)
      (* { *)
      (*   eapply is_valid_updated_lmemory_lmem_incl with (glmem := lm); eauto. *)
      (*   (* destruct Hvalid as (Hupd&_&?). *) *)
      (*   (* eapply is_valid_updated_lmemory_insert; eauto. *) *)
      (*   admit. *)
      (*   (* eapply logical_range_notin; eauto. *) *)
      (*   (* eapply Forall_forall; intros a Ha. *) *)
      (*   (* eapply logical_range_version_neq; eauto; lia. *) *)
      (* } *)
      (* assert *)
      (*   (logical_range_map b0 e0 lws (v0 + 1) ⊆ mem') *)
      (*   as Hmem'_be_next. *)
      (* { clear -Hlm_incl Hvalid Hpca_notin Hlen_lws. *)
      (*   (* TODO extract as a lemma *) *)
      (*   eapply map_subseteq_spec; intros [a' v'] lw' Hlw'. *)
      (*   assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be] *)
      (*       by (eapply logical_range_map_some_inv; eauto) ; simplify_eq. *)
      (*   (* erewrite logical_range_map_lookup_versions with (v':=v0) in Hlw'; eauto. *) *)
      (*   (* rewrite /logical_range_map in Hlw'. *) *)
      (*   admit. *)
      (*   (* rewrite update_version_region_preserves_lmem_next; eauto. *) *)
      (*   (* eapply lookup_weaken. ; last eauto. *) *)
      (*   (* all: rewrite lookup_insert_ne //=; last (intro ; set_solver). *) *)
      (*   (* eapply logical_range_version_neq; eauto; lia. *) *)
      (* } *)

      (* rewrite -(insert_id mem' (pc_a, pc_v) lw); auto. *)
      (* iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame. *)
      (* eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be *)
      (* ; last (by eapply logical_region_notin; eauto). *)
      (* iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]" *)
      (* ; first (eapply Hmem'_be). *)
      (* iSplitL "Hrange". *)
      (* { iApply big_sepM_to_big_sepL2; last iFrame; eauto; by rewrite map_length. } *)
      (* eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next *)
      (* ; last (eapply logical_region_notin ; eauto). *)
      (* eapply delete_subseteq_list_r *)
      (*   with (m3 := list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws)) *)
      (*   in Hmem'_be_next *)
      (* ; eauto *)
      (* ; last by eapply update_logical_memory_region_disjoint. *)
      (* iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]" *)
      (* ; first (eapply Hmem'_be_next); iClear "Hmmap". *)
      (* iApply big_sepM_to_big_sepL2; last iFrame; eauto; by rewrite map_length. *)
  (* Qed. *)
  Admitted.

  Lemma wp_isunique_success'
    (Ep : coPset)
    (pc_p : Perm) (pc_b pc_e pc_a pc_a' : Addr) (pc_v : Version)
    (lw : LWord)
    (p : Perm) (b e a : Addr) (v : Version)
    (lwdst : LWord)
    (dst src : RegName) :

    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →
    p ≠ E ->
    finz.seq_between b e ## reserved_addresses ->

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
    iIntros (Hinstr Hvpc Hpca Hp Hreserved φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hrmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmmap".
    iApply (wp_isunique with "[$Hrmap Hmmap]"); eauto ; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    { rewrite /allows_sweep. intros p' b' e' a' v' ? ?.
      by simplify_map_eq.
    }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as
      (* [ ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hreserved' Hunique_regs Hincr_PC *)
      (* | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC *)
      [ ? ? ? ? ? ? Hlwsrc' Hp_neq_E Hupd Hnotres Hunique_regs Hincr_PC
      | ? Hlwsrc Hnot_sealed Hmem' Hunique_regs Hincr_PC
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
      destruct Hupd as ( lm & Hlm_incl & Hvalid ).

      assert ( Hpc_a : pc_a ∉ finz.seq_between b0 e0)
               by (eapply unique_in_registersL_pc_no_overlap; eauto; by simplify_map_eq).
      (* assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca. *)
      (* { eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto ; last by simplify_map_eq. } *)

      (* destruct Hvalid as (Hupd&_&?). *)
      (* assert ( *)
      (*     exists lws, *)
      (*       length lws = length (finz.seq_between b0 e0) /\ *)
      (*         logical_range_map b0 e0 lws (v0 + 1) ⊆ mem') *)
      (*   as (lws & Hlen_lws & Hmem'_be_next). *)
      (* { eapply logical_region_map_inv ; eauto. } *)

      (* rewrite -(insert_id mem' (pc_a, pc_v) lw); auto. *)
      (* iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame. *)

      (* eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next *)
      (* ; eauto *)
      (* ; last (eapply logical_region_notin; eauto). *)
      (* iExists lws. *)

      (* iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]" *)
      (* ; first (eapply Hmem'_be_next); iClear "Hmmap". *)
      (* iApply big_sepM_to_big_sepL2; last iFrame; eauto. *)
      (* by rewrite map_length. *)
  Admitted.

  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
