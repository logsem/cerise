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
    (∃ lm, lmem ⊆ lm ∧ is_valid_updated_lmemory lm lmem (finz.seq_between b e) v lmem') ->
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
  Lemma wp2_word_is_lcap {Φf : iProp Σ} {w Φs} :
         Φf ∧ (Φs () ())
      ⊢ wp_opt2 (if is_lcap w then Some () else None) (word_is_cap_or_scap (lword_get_word w)) Φf Φs.
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
    iIntros (Hsweep Hsrc) "Hσrm".
    iDestruct (transiently_abort with "Hσrm") as "(Hσ & Hregs & Hmem)".
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

    sweep σm σr src = true ->
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    gen_heap_interp lr ∗ gen_heap_interp lm ∗
      ⌜state_phys_log_corresponds σr σm lr lm vmap⌝%I
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem, k ↦ₐ{y.1} y.2)
      ⊢ |==>
      let la := finz.seq_between b e in
      let lmem' := update_version_region lm la v lmem in
      let lm' := update_version_region lm la v lm in
      (* let lregs' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lregs)) in *)
      let lregs' := (<[src:=next_version_lword lwsrc]> lregs) in
      (* let lr' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lr)) in *)
      let lr' := (<[src:=next_version_lword lwsrc]> lr) in
      let vmap' := update_version_region_vmap la v vmap in
      ⌜ is_valid_updated_lmemory lm lmem (finz.seq_between b e) v lmem'⌝ ∗
        gen_heap_interp lr' ∗ gen_heap_interp lm' ∗
        ⌜state_phys_log_corresponds σr σm lr' lm' vmap' ⌝%I ∗ ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗ ([∗ map] k↦y ∈ full_own_mem lmem', k ↦ₐ{y.1} y.2).
  Proof.
    iIntros (Hsweep Hlsrc Hlcap_wsrc) "(Hr & Hm & %Hcorr & Hregs & Hmem)".
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
    set (la := finz.seq_between b e).
    set (lmem' := update_version_region lm la v lmem).
    set (lm' := update_version_region lm la v lm).
    (* set (lregs' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lregs))). *)
    (* set (lr' := (if is_sealed lwsrc then lregs else (<[src:=next_version_lword lwsrc]> lr))). *)
    set (lregs' := <[src:=next_version_lword lwsrc]> lregs).
    set (lr' := <[src:=next_version_lword lwsrc]> lr).
    set (vmap' := update_version_region_vmap la v vmap).
    iMod ((gen_heap_lmem_version_update' lm lmem lm lmem' _ vmap _ (finz.seq_between b e) v)
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

    iCombine "Hpca Hmem" as "Hmem".
    rewrite -(big_sepM_delete (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y) _ _ _ Hmem_pc).

    destruct (sweep (mem σ) (reg σ) src) eqn:Hsweep
    ; cbn ; rewrite Hsweep
    ; unshelve iApply (wp_wp2 (φ1 := exec_optL_IsUnique lregs lmem dst src _) (φ2 := _))
    ; [exact true|exact false| |].
    all: iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
    - iDestruct "Hσ" as "(%lr & %lm & %vmap & Hlr & Hlm & %Hcorr0)".
      iDestruct (gen_heap_valid_inclSepM with "Hlm Hmem") as "%Hlmsub".
      iDestruct (gen_heap_valid_inclSepM with "Hlr Hregs") as "%Hlrsub".
      iCombine "Hlr Hlm Hregs Hmem" as "Hσ". 
      iDestruct (transiently_intro with "Hσ") as "Hσ".
      iModIntro. iApply wp_opt2_mono2.
      iSplitL "Hφ Hσ".
      2: {
        iApply wp2_reg_lookup5; eauto.
        set_solver.
      }
      iSplit.
      { now iIntros "%Htr". } 
      iIntros (lsrcv srcv) "-> %Hlsrcv %Hsrcv".
      assert (lr !! src = Some lsrcv) as Hlrsrc by eapply (lookup_weaken _ _ _ _ Hlsrcv Hlrsub).
      iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
      iApply wp_opt2_mono2.
      iSplitL "Hφ Hσ".
      2: now iApply (wp2_word_is_lcap (Φf := True%I) (w := lsrcv) (Φs := fun _ _ => True)%I).
      iSplit.
      { iIntros "_ %Hislcap %Hwicos".
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem)".
        iSplitR "Hφ Hregs Hmem".
        iExists lr, lm, vmap; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        apply IsUnique_failure; eauto.
        eapply (IsUnique_fail_cap _ _ _ _ _ Hlsrcv).
        destruct lsrcv as [z|[? ? ? ? ?|? ? ? ?]|? [? ? ? ? ?|? ? ? ?] ];
          now inversion Hislcap.
      }
      iIntros (u1 u2) "_ %Hlclsrcv %Hwicos".
      rewrite updatePC_incrementPC.
      destruct (is_lcap  lsrcv) eqn:Hillsrcv; last inversion Hlclsrcv.
      clear u1 u2 Hlclsrcv Hwicos.
      destruct (get_is_lcap_inv _ Hillsrcv) as (p & b & e & a & v & Hgllsrcv).
      destruct (is_sealed lsrcv) eqn:Hslsrcv.
      + iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
        iApply wp_opt2_mono2.
        iSplitL "Hφ".
        2: {
          iApply transiently_wp_opt2.
          iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem)".
          iModIntro.
          iApply wp_opt2_mod.
          iMod (gen_heap_update_inSepM _ _ dst (LInt 1) with "Hσr Hregs") as "(Hσr & Hregs)".
          { rewrite -elem_of_dom. set_solver. }
          iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
          iApply (wp_opt2_frame with "Hσm").
          iApply (wp_opt2_frame with "Hmem").
          iModIntro.
          iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
          { assert (PC ∈ dom lregs) by now rewrite elem_of_dom HPC. now set_solver. }
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 1) eq_refl); cbn; eauto.
        }
        iSplit.
        { iIntros "Htr %HincLPC %HincPC".
          iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs & Hmem)".
          iSplitR "Hφ Hregs Hmem".
          iExists lr, lm, vmap; now iFrame.
          iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
          apply IsUnique_failure; eauto.
          eapply IsUnique_fail_invalid_PC_nupd; eauto.
        }
        iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
        iApply wp2_val.
        iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %lr2 & Hσr & %Hcorr2 & Hregs)".
        iModIntro.
        iSplitR "Hφ Hregs Hmem".
        iExists _, _, _; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem]").
        iPureIntro.
        eapply IsUnique_success_true_is_sealed; eauto.
        eapply unique_in_registersL_mono; eauto.
        eapply state_corresponds_unique_in_registers; eauto.
        eapply sweep_spec; eauto.
      + assert (lsrcv = LCap p b e a v /\ p ≠ E) as  [-> HnpE].
        { now destruct lsrcv as [z|[ [ | | | | | ] ? ? ? ?|? ? ? ?]|? [? ? ? ? ?|? ? ? ?] ];
            inversion Hgllsrcv. }
        iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
        iApply wp_opt2_mono2.
        iSplitL "Hφ".
        2: {
          iApply transiently_wp_opt2.
          iMod "Hσ" as "(Hσr & Hσm & Hregs & Hmem)".
          iModIntro.
          iApply wp_opt2_mod.
          rewrite map_full_own.
          iMod (update_state_interp_next_version with "[$Hσr $Hσm $Hregs $Hmem]") as "(%Hvm & Hσr & Hσm & #Hcorr' & Hregs & Hmem)"; eauto. 
          iMod (gen_heap_update_inSepM _ _ dst (LInt 1) with "Hσr Hregs") as "(Hσr & Hregs)".
          { rewrite -elem_of_dom. set_solver. }
          iDestruct (gen_heap_valid_inclSepM with "Hσr Hregs") as "%Hlr2sub".
          iApply (wp_opt2_frame with "Hσm").
          iApply (wp_opt2_frame with "Hmem").
          iApply (wp_opt2_frame with "Hcorr'").
          iDestruct "Hcorr'" as "%Hcorr'".
          iApply (wp2_opt_incrementPC2 with "[$Hσr $Hregs]"); eauto.
          { assert (PC ∈ dom lregs) by now rewrite elem_of_dom HPC. now set_solver. }
          eapply (state_phys_log_corresponds_update_reg (lw := LInt 1) eq_refl); cbn; eauto.
        }
        iSplit.
        { iIntros "Htr %HincLPC %HincPC".
          iDestruct (transiently_abort with "Htr") as "(Hσr & Hσm &  Hregs & Hmem)".
          iSplitR "Hφ Hregs Hmem".
          iExists lr, lm, vmap; now iFrame.
          iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
          apply IsUnique_failure; eauto.
          eapply IsUnique_fail_invalid_PC_upd; eauto.
        }
        iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
        iApply wp2_val.
        iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %Hcorr & %lr2 & Hσr & %Hcorr2 & Hregs)".
        iModIntro.
        iSplitR "Hφ Hregs Hmem".
        iExists _, _, _; now iFrame.
        rewrite -map_full_own.
        iApply ("Hφ" with "[$Hregs $Hmem]").
        iPureIntro.
        eapply IsUnique_success_true_cap; eauto.
        exists lm.
        eauto using is_valid_updated_lmemory_update_version_region, lookup_weaken, finz_seq_between_NoDup, state_corresponds_last_version_lword_region, state_corresponds_access_lword_region.
        eapply unique_in_registersL_mono; eauto.
        eapply state_corresponds_unique_in_registers; eauto.
        eapply sweep_spec; eauto.
    - iDestruct "Hσ" as "(%lr & %lm & %vmap & Hlr & Hlm & %Hcorr0)".
      iDestruct (gen_heap_valid_inclSepM with "Hlm Hmem") as "%Hlmsub".
      iDestruct (gen_heap_valid_inclSepM with "Hlr Hregs") as "%Hlrsub".
      iCombine "Hlr Hlm Hregs Hmem" as "Hσ". 
      iDestruct (transiently_intro with "Hσ") as "Hσ".
      iModIntro. iApply wp_opt2_mono2.
      iSplitL "Hφ Hσ".
      2: {
        iApply wp2_reg_lookup5; eauto.
        set_solver.
      }
      iSplit.
      { now iIntros "%Htr". } 
      iIntros (lsrcv srcv) "-> %Hlsrcv %Hsrcv".
      iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
      iApply wp_opt2_mono2.
      iSplitL "Hφ Hσ".
      2: now iApply (wp2_word_is_lcap (Φf := True%I) (w := lsrcv) (Φs := fun _ _ => True)%I).
      iSplit.
      { iIntros "_ %Hislcap %Hwicos".
        iDestruct (transiently_abort with "Hσ") as "(Hσr & Hσm & Hregs & Hmem)".
        iSplitR "Hφ Hregs Hmem".
        iExists lr, lm, vmap; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        apply IsUnique_failure; eauto.
        eapply (IsUnique_fail_cap _ _ _ _ _ Hlsrcv).
        destruct lsrcv as [z|[? ? ? ? ?|? ? ? ?]|? [? ? ? ? ?|? ? ? ?] ];
          now inversion Hislcap.
      }
      iIntros (u1 u2) "_ %Hlclsrcv %Hwicos".
      rewrite updatePC_incrementPC.
      destruct (is_lcap  lsrcv) eqn:Hillsrcv; last inversion Hlclsrcv.
      clear u1 u2 Hlclsrcv Hwicos.
      destruct (get_is_lcap_inv _ Hillsrcv) as (p & b & e & a & v & Hgllsrcv).
      iApply wp_opt2_bind; iApply wp_opt2_eqn_both.
      iApply wp_opt2_mono2.
      iSplitL "Hφ".
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
        iExists lr, lm, vmap; now iFrame.
        iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
        apply IsUnique_failure; eauto.
        eapply IsUnique_fail_invalid_PC_nupd; eauto.
      }
      iIntros (lregs2 regs2) "Htr %HincLPC %HincPC".
      iApply wp2_val.
      iMod (transiently_commit with "Htr") as "(Hσm & Hmem & %lr2 & Hσr & %Hcorr2 & Hregs)".
      iModIntro.
      iSplitR "Hφ Hregs Hmem".
      iExists _, _, _; now iFrame.
      iApply ("Hφ" with "[$Hregs $Hmem]").
      iPureIntro.
      eapply IsUnique_success_false; eauto.
  Qed.

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
      destruct Hupd as ( lm & Hlm_incl & Hvalid ).

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca
          by (eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq).

      assert ( logical_range_map b0 e0 lws v0 ⊆ mem' )
        as Hmem'_be.
      {
        eapply is_valid_updated_lmemory_lmem_incl with (glmem := lm); eauto.
        (* destruct Hvalid as (Hupd&_&?). *)
        (* eapply is_valid_updated_lmemory_insert; eauto. *)
        admit.
        (* eapply logical_range_notin; eauto. *)
        (* eapply Forall_forall; intros a Ha. *)
        (* eapply logical_range_version_neq; eauto; lia. *)
      }
      assert
        (logical_range_map b0 e0 lws (v0 + 1) ⊆ mem')
        as Hmem'_be_next.
      { clear -Hlm_incl Hvalid Hpca_notin Hlen_lws.
        (* TODO extract as a lemma *)
        eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
        assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be]
            by (eapply logical_range_map_some_inv; eauto) ; simplify_eq.
        (* erewrite logical_range_map_lookup_versions with (v':=v0) in Hlw'; eauto. *)
        (* rewrite /logical_range_map in Hlw'. *)
        admit.
        (* rewrite update_version_region_preserves_lmem_next; eauto. *)
        (* eapply lookup_weaken. ; last eauto. *)
        (* all: rewrite lookup_insert_ne //=; last (intro ; set_solver). *)
        (* eapply logical_range_version_neq; eauto; lia. *)
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

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca.
      { eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq. }

      destruct Hvalid as (Hupd&_&?).
      assert (
          exists lws,
            length lws = length (finz.seq_between b0 e0) /\
              logical_range_map b0 e0 lws (v0 + 1) ⊆ mem')
        as (lws & Hlen_lws & Hmem'_be_next).
      { eapply logical_region_map_inv ; eauto. }

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

  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
