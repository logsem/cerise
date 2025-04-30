From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsUnique.
Import uPred.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Local Hint Resolve finz_seq_between_NoDup list_remove_elem_NoDup : core.

  Definition reg_allows_sweep
    (lregs : LReg) (r : RegName)
    (p : Perm) (b e a : Addr) (v : Version):=
    lregs !! r = Some (LCap p b e a v) ∧ readAllowed p = true.

  Definition allow_sweep_mask
    (a_pc : Addr) (v_pc : Version) (la : list Addr) (v : Version): coPset :=
    compute_mask_region (⊤ ∖ ↑logN.@(a_pc, v_pc)) (list_remove_elem a_pc la) v.

  Lemma allow_sweep_mask_remove_nodup
    (a_pc : Addr) (v_pc : Version) (la : list Addr) (v : Version) :
    NoDup la ->
    allow_sweep_mask a_pc v_pc (list_remove_elem a_pc la) v =
    allow_sweep_mask a_pc v_pc la v.
  Proof.
    intros HNoDup.
    by rewrite /allow_sweep_mask list_remove_elem_idem.
  Qed.

  Definition region_open_resources
    (a_pc : Addr) (v_pc : Version)
    (la : list Addr) (v : Version)
    (lws : list LWord) (Ps : list D)
    (has_later : bool)
    : iProp Σ :=

    let E := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E' := allow_sweep_mask a_pc v_pc la v in

    ([∗ list] lw;Pw ∈ lws;Ps, (if has_later then ▷ (Pw : D) lw else (Pw : D) lw))
    ∗ ( ⌜ Persistent ([∗ list] lw;Pw ∈ lws;Ps, (Pw : D) lw) ⌝ )
    ∗ ( if has_later
        then [∗ list] Pa ∈ Ps, read_cond Pa interp
        else [∗ list] Pa ∈ Ps, (□ ∀ (lw : LWord), (Pa : D) lw -∗ interp lw)
      )%I
    ∗ ( (▷ ([∗ list] a_Pa ∈ zip la Ps, (interp_ref_inv a_Pa.1 v a_Pa.2))) ={E', E }=∗ True).

  Definition sweep_mask_cond
    (lregs : LReg) (src : RegName)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (a_pc : Addr) (v_pc : Version) :=
    decide (reg_allows_sweep lregs src p_src b_src e_src a_src v_src
            /\ (src = PC \/ a_pc ∉ (finz.seq_between b_src e_src))).

  (* Description of what the resources are supposed to look like after opening the region *)
  (*    if we need to, but before closing the region up again*)
  Definition allow_sweep_res
    (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D)
    :=

    let la  := (list_remove_elem a_pc (finz.seq_between b_src e_src)) in
    let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E'  := allow_sweep_mask a_pc v_pc la v_src in

    (⌜read_reg_inr lregs src p_src b_src e_src a_src v_src⌝ ∗
     ⌜allows_sweep lregs src⌝ ∗
     if sweep_mask_cond lregs src p_src b_src e_src a_src v_src a_pc v_pc
     then
      (|={E, E'}=>
         ∃ (lws :list LWord),
         ⌜ length lws = length la ⌝
         ∗ ([∗ map] la↦lw ∈ (logical_region_map la lws v_src), la ↦ₐ lw)
         ∗ region_open_resources a_pc v_pc la v_src lws Ps true
      )%I
     else True)%I.

  Lemma create_sweep_res
    (lregs : LReg) (src : RegName)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version) :

    let la := (list_remove_elem a_pc (finz.seq_between b_src e_src)) in

    read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src
    -> a_pc ∈ finz.seq_between b_pc e_pc
    → (∀ (r : RegName) lw, ⌜r ≠ PC⌝ → ⌜lregs !! r = Some lw⌝ → (fixpoint interp1) lw)
    -∗ interp (LCap p_pc b_pc e_pc a_pc v_pc)
    -∗ (∃ (Ps : list D),
           ⌜ length la = length Ps ⌝
           ∗ allow_sweep_res
               (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src
               a_pc v_pc
               p_src b_src e_src a_src v_src Ps).
  Proof.
    intros * Hread Hapc_inbounds.
    iIntros "#Hreg #Hinterp_pc".
    apply list_remove_elem_in in Hapc_inbounds.
    destruct Hapc_inbounds as (la' & <- & Hapc_inbounds).
    rewrite /allow_sweep_res /sweep_mask_cond.
    case_decide as Hallows; cycle 1.
    { iExists (repeat (λne _, True%I) (length la)); iFrame "%".
      iSplit; first by rewrite repeat_length.
      iSplit; last done.
      iIntros (p b e a v Hlv Hp).
      destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq.
      + iDestruct (read_allowed_not_reserved with "Hinterp_pc") as "%"; auto.
      + iAssert (interp (LCap p b e a v)) as "Hinterp_src".
        { iApply "Hreg"; eauto. }
        iDestruct (read_allowed_not_reserved with "Hinterp_src") as "%"; auto.
    }
    iFrame "%".
    cbn in Hapc_inbounds.
    apply bind_Some in Hapc_inbounds.
    destruct Hapc_inbounds as (? & Hrem & ?) ; simplify_eq.
    rewrite /reg_allows_sweep in Hallows.
    destruct Hallows as ( (Hreg & HreadAllowed) & Hdecide).
    assert (la ⊆+ finz.seq_between b_src e_src)
      as Hla_subseteq by apply list_remove_elem_submsteq.
    assert (NoDup la) as Hla_NoDup by (by apply list_remove_elem_NoDup).
    rewrite /read_reg_inr in Hread; simplify_map_eq.

    destruct (decide (src = PC)) as [-> | Hneq_src_pc] ; simplify_map_eq.
    (* src = PC *)
    - rewrite /allow_sweep_mask.
      rewrite list_remove_elem_idem; last done.
      iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_src, v_src)) with "Hinterp_pc")
        as (Ps) "[%Hlen_Ps Hmod]" ; eauto.
      { eapply Forall_forall. intros a' Ha'.
        subst la.
        eapply namespaces.coPset_subseteq_difference_r; auto.
        assert (a' ≠ a_src).
        {
          eapply list_remove_elem_neq; cycle 1 ; eauto.
          apply list_remove_Some in Hrem.
          setoid_rewrite Hrem; set_solver.
        }
        solve_ndisj.
      }
      iExists Ps.
      iSplit ; first by subst.
      iSplit.
      { iIntros (p b e a v Hsrc Hp).
        iDestruct (read_allowed_not_reserved with "Hinterp_pc") as "%"; auto.
        + destruct p_src ; cbn in HreadAllowed; auto.
        + by simplify_map_eq.
      }
      iMod "Hmod".
      iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)".
      iExists lws.
      iFrame; iFrame "%".
      iModIntro.
      iIntros "H".
      iDestruct ("Hclose" with "H") as "Hclose".
      rewrite /allow_sweep_mask.
      rewrite list_remove_elem_notin.
      subst la.
      iFrame.
      apply not_elemof_list_remove_elem; done.

    (* src ≠ PC *)
    - destruct Hdecide as [Hcontra|Ha_notin_rem] ; first contradiction.
      iAssert (interp (LCap p_src b_src e_src a_src v_src)) as "#Hinterp_src"
      ; first (iApply "Hreg"; eauto).
      iDestruct (interp_open_region $ (⊤ ∖ ↑logN.@(a_pc, v_pc)) with "Hinterp_src")
        as (Ps) "[%Hlen_Ps Hmod]" ; eauto.
      { apply Forall_forall; intros a' Ha'.
        subst la.
        assert (a' ≠ a_pc).
        { intro ; subst. by apply not_elemof_list_remove_elem in Ha'. }
        apply namespaces.coPset_subseteq_difference_r; [solve_ndisj|set_solver].
      }
      iExists Ps.
      iSplit ; first by subst.
      iSplit.
      { iIntros (p b e a v Hsrc Hp).
        iDestruct (read_allowed_not_reserved with "Hinterp_src") as "%"; auto.
        + destruct p_src ; cbn in HreadAllowed; auto.
        + by simplify_map_eq.
      }
      iMod "Hmod".
      rewrite allow_sweep_mask_remove_nodup; auto.
      iDestruct "Hmod" as (lws) "(%Hlws & %Hpers & Hmem & HPs & HPs' & Hclose)".
      iExists lws.
      iFrame; iFrame "%".
      iModIntro.
      iIntros "H".
      iDestruct ("Hclose" with "H") as "Hclose".
      by rewrite allow_sweep_mask_remove_nodup.
  Qed.

  Definition allow_sweep_mem
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) (has_later : bool) :=

    let la  := (list_remove_elem a_pc (finz.seq_between b_src e_src)) in

    (⌜read_reg_inr lregs src p_src b_src e_src a_src v_src⌝ ∗
     if sweep_mask_cond lregs src p_src b_src e_src a_src v_src a_pc v_pc
     then (∃ (lws : list LWord),
              ⌜length lws = length la⌝
              ∗ ⌜lmem = <[(a_pc, v_pc):=lw_pc]> (logical_region_map la lws v_src)⌝
              ∗ region_open_resources a_pc v_pc la v_src lws Ps has_later)
     else ⌜lmem = <[(a_pc, v_pc):=lw_pc]> ∅⌝)%I.


  Lemma sweep_res_implies_mem_map
    (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) :

    let la := list_remove_elem a_pc (finz.seq_between b_src e_src) in
    let E  := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E' := allow_sweep_mask a_pc v_pc la v_src in

    allow_sweep_res lregs src a_pc v_pc p_src b_src e_src a_src v_src Ps
    -∗ (a_pc, v_pc) ↦ₐ lw_pc
    ={ E,
         if sweep_mask_cond lregs src p_src b_src e_src a_src v_src a_pc v_pc
         then E'
         else E
      }=∗
    ∃ lmem : LMem,
      allow_sweep_mem lmem lregs src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps true
      ∗ ▷ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw).
  Proof.
    intros *.
    iIntros "HSweepRes Ha_pc".
    iDestruct "HSweepRes" as "(%Hread & [ %Hreserved HSweepRes ] )".
    subst E'.
    rewrite /sweep_mask_cond.
    case_decide as Hallows; cycle 1.
      - iExists _.
        iSplitR "Ha_pc".
        + iFrame "%".
          rewrite /sweep_mask_cond; case_decide; first by exfalso. auto.
        + iModIntro; iNext. by iApply memMap_resource_1.
      - iMod "HSweepRes" as (lws) "(%Hlws & Hmem & HSweepRest)".
        iExists _.
        iSplitL "HSweepRest".
        * iFrame "%".
          rewrite decide_True; auto.
        * iModIntro;iNext.
          destruct Hallows as ((Hrinr & Hra) & Hne).
          iDestruct (big_sepM_insert with "[$Hmem $Ha_pc]") as "Hmem" ; cycle 1 ; auto.
          rewrite /logical_region_map.
          apply not_elem_of_list_to_map_1.
          rewrite fst_zip.
          2: { rewrite Hlws /logical_region fmap_length; lia. }
          rewrite /logical_region.
          intro Hcontra. clear -Hcontra.
          eapply elem_of_list_fmap_2 in Hcontra.
          destruct Hcontra as (a & Heq & Hcontra) ; simplify_eq.
          apply not_elemof_list_remove_elem in Hcontra; auto.
  Qed.

  Lemma mem_map_implies_pure_conds
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) (has_later : bool) :
    allow_sweep_mem lmem lregs src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps has_later
    -∗ ⌜lmem !! (a_pc, v_pc) = Some lw_pc⌝.
  Proof.
    iIntros "(% & HSweepRes)".
    rewrite /sweep_mask_cond.
    case_decide as Hallows.
    - pose (Hallows' := Hallows).
      destruct Hallows' as ((Hreg & Hread) & Hdecide).
      iDestruct "HSweepRes" as (lws) "(%Hlen & -> & HSweepRest)".
      by simplify_map_eq.
    - iDestruct "HSweepRes" as "->".
      by simplify_map_eq.
  Qed.

  Lemma allow_sweep_mem_later
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) :
    allow_sweep_mem lmem lregs src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps true
    -∗ ▷ allow_sweep_mem lmem lregs src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps false.
  Proof.
    iIntros "[% HSweepMem]".
    rewrite !/allow_sweep_mem /= /sweep_mask_cond. iSplit;[auto|].
    case_decide.
    - iApply later_exist_2. iDestruct "HSweepMem" as (lws) "(%&%&HSweepRest)".
      iExists lws.
      iDestruct "HSweepRest" as "(?&?&?&?)"; iFrame "%∗"; iNext ; iFrame.
    - iNext; iFrame.
  Qed.

  Lemma mem_map_recover_res_no_update
    (lmem : LMem) (lregs : LReg) (src : RegName)
    (a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) :

    let la  := (list_remove_elem a_pc (finz.seq_between b_src e_src)) in
    let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E'  := allow_sweep_mask a_pc v_pc la v_src in

    length la = length Ps ->
    allow_sweep_mem lmem lregs src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps false
    -∗ ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw)
    ={ if sweep_mask_cond lregs src p_src b_src e_src a_src v_src a_pc v_pc
      then E'
      else E, E }=∗
    (a_pc,v_pc) ↦ₐ lw_pc.
  Proof.
    intros * Hlen_Ps; iIntros "(%Hread & HSweepMem) Hmem".
    rewrite /sweep_mask_cond.
    case_decide as Hdecide; cycle 1.
    - iDestruct "HSweepMem" as "->"; iModIntro.
      iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; auto.
    - iDestruct "HSweepMem" as (lws Hlen_lws ->) "(HPrange & _ & _ & Hcls_src)".
      subst E'; rewrite !allow_sweep_mask_remove_nodup; auto.
      iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; auto.
      {
        apply logical_region_notin; auto.
        apply not_elemof_list_remove_elem; auto.
      }
      iMod ("Hcls_src" with "[Hmem HPrange]") as "_".
      {
        iNext.
        iApply region_inv_construct; auto.
        iExists (lws); iFrame "∗ %".
      }
      iModIntro; iFrame.
  Qed.

  (* If we have a valid sweep, but not opened the invariant,
   it necessarily means that the permission of the src word is O *)
  Lemma reg_allows_sweep_unique_O
    (lregs : LReg) (src : RegName)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version):

    p_src ≠ machine_base.E ->
    <[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! src = Some (LCap p_src b_src e_src a_src v_src) ->
    unique_in_registersL
      (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) (Some src)
      (LCap p_src b_src e_src a_src v_src) ->
    (b_pc <= a_pc < e_pc)%a ->
    ¬ (reg_allows_sweep
         (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src
         e_src a_src v_src ∧ (src = PC ∨ a_pc ∉ finz.seq_between b_src e_src))
    -> p_src = O.
  Proof.
    intros Hp_neq_E Hlwsrc' Hunique_regs Hbae Hdecide.
    rewrite /reg_allows_sweep in Hdecide.
    apply not_and_r in Hdecide.
    destruct Hdecide as [Hdecide|Hdecide]; cycle 1.
    - exfalso.
      apply not_or in Hdecide.
      destruct Hdecide as [Hsrc_neq_PC Ha_pc_overlap].
      apply dec_stable in Ha_pc_overlap.
      clear -Hunique_regs Ha_pc_overlap Hsrc_neq_PC Hbae.
      rewrite /unique_in_registersL in Hunique_regs.
      eapply map_Forall_insert_1_1 in Hunique_regs.
      rewrite decide_False in Hunique_regs; auto.
      apply Hunique_regs.
      rewrite /overlap_wordL /overlap_word //=.
      apply elem_of_finz_seq_between in Ha_pc_overlap.
      destruct (b_src <? b_pc)%a eqn:Hneq; solve_addr.
    - rewrite /reg_allows_sweep in Hdecide.
      apply not_and_r in Hdecide.
      destruct Hdecide as [Hdecide|Hdecide].
      + by rewrite Hlwsrc' in Hdecide.
      + destruct p_src ; try done.
  Qed.

  (* Given assumption that the sweep was successful,
     close the open invariants by giving back the memory resources.
   *)
  Lemma mem_map_recover_res_update_version
    (lmem lmem': LMem) (lregs : LReg) (src : RegName)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version) (lw_pc : LWord)
    (p_src : Perm) (b_src e_src a_src : Addr) (v_src : Version)
    (Ps : list D) (P : D) :

    let la  := (list_remove_elem a_pc (finz.seq_between b_src e_src)) in
    let E   := ⊤ ∖ ↑logN.@(a_pc, v_pc) in
    let E'  := allow_sweep_mask a_pc v_pc la v_src in

    let lregs' := (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) in

    length la = length Ps ->
    p_src ≠ machine_base.E ->
    is_valid_updated_lmemory lmem (finz.seq_between b_src e_src) v_src lmem' ->
    finz.seq_between b_src e_src ## reserved_addresses ->
    unique_in_registersL lregs' (Some src) (LCap p_src b_src e_src a_src v_src) ->
    lregs' !! src = Some (LCap p_src b_src e_src a_src v_src) ->
    isCorrectLPC (LCap p_pc b_pc e_pc a_pc v_pc) ->
    Persistent (P lw_pc) ->

    □ (∀ lw : LWord, P lw -∗ fixpoint interp1 lw)
    -∗ P lw_pc
    -∗ allow_sweep_mem lmem lregs' src a_pc v_pc lw_pc p_src b_src e_src a_src v_src Ps false
    -∗ ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw)
    ={ if sweep_mask_cond lregs' src p_src b_src e_src a_src v_src a_pc v_pc
       then E'
       else E, E}=∗
    (a_pc,v_pc) ↦ₐ lw_pc ∗
    (if sweep_mask_cond lregs' src p_src b_src e_src a_src v_src a_pc v_pc
    then interp (LCap p_src b_src e_src a_src (v_src+1))
    else emp).
  Proof.
    intros * Hlen_Ps Hp_ne_E Hvalid_lmem' Hreserved Hunique_regs Hlwsrc' Hcorrect_pc HpersP
    ; iIntros "#Hread #HP (%Hread & HSweepMem) Hmem".
    subst lregs'.
    assert ( (b_pc <= a_pc < e_pc)%a) as Hbae.
    { inversion Hcorrect_pc as [lpc ? ? ? ? Heq HcorrectPC Hlpc]
      ; inversion HcorrectPC ; cbn in * ; simplify_map_eq;  done.
    }
    rewrite /sweep_mask_cond.
    case_decide as Hdecide ; cycle 1.
    - iDestruct "HSweepMem" as "->".
      apply reg_allows_sweep_unique_O in Hdecide; auto ; simplify_eq.
      all: assert (src ≠ PC)
        as Hsrc_ne_pc
             by (intro ; subst
                 ; inversion Hcorrect_pc as [lpc ? ? ? ? Heq HcorrectPC Hlpc]
                 ; inversion HcorrectPC as [? ? ? ? Hbounds Hperm]
                 ; cbn in * ; simplify_map_eq
                 ; by destruct Hperm).
      all: assert ( lmem' !! (a_pc, v_pc) = Some lw_pc )
        as Hmem'_apc
             by (eapply is_valid_updated_lmemory_preserves_lmem; cycle 1 ; eauto; by simplify_map_eq).
      all: rewrite -(insert_id lmem' (a_pc,v_pc) lw_pc);auto.
      all: by iDestruct (big_sepM_insert_delete with "Hmem") as "[Hmem _]"; iFrame.
    - destruct Hdecide as [ [Hsrc_lregs Hread_src] Hvalid_sweep].
      (* TODO @June: is there any part of the proof that is common
         and could be refactored beforehand ? *)
      destruct (decide (src = PC)) as [->|Hsrc_ne_pc]
      ; [clear Hvalid_sweep |]
      ; simplify_map_eq.
      + (* r = PC *)
        iDestruct "HSweepMem" as (lws Hlen_lws ->) "HSweepRest".
        iDestruct "HSweepRest" as "(HPrange & %Hpers & #Hread_cond & Hcls_src)".
        subst E'.
        subst la ; set (la := (list_remove_elem a_src (finz.seq_between b_src e_src))).

        assert (a_src ∈ finz.seq_between b_src e_src) as Ha_pc_in_range.
        { by apply isCorrectLPC_isCorrectPC_iff, isCorrectPC_withinBounds, withinBounds_in_seq
         in Hcorrect_pc.
        }

        assert ( a_src ∉ la)
         as Ha_pc_notin_la' by (by subst la ; apply not_elemof_list_remove_elem).

        assert ( lmem' !! (a_src, v_src) = Some lw_pc ) as Hmem'_apc.
        { eapply is_valid_updated_lmemory_preserves_lmem ; cycle 1 ; eauto.
          by simplify_map_eq.
        }
        assert ( lmem' !! (a_src, v_src+1) = Some lw_pc ) as Hmem'_apc_next.
        { eapply is_valid_updated_lmemory_preserves_lmem_next; cycle 1
         ; eauto
         ; last by simplify_map_eq.
          eapply Forall_forall; intros a' Ha'.
          rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
          eapply logical_region_version_neq; eauto ; last lia.
        }

        assert (logical_region_map la lws v_src !! (a_src, v_src) = None)
         as Ha_src_notin_reg_la'.
        { subst la ; eapply logical_region_notin; eauto. }

        assert ( ((logical_region_map la lws) ) v_src ⊆ lmem' )
          as Hmem'_be.
        { subst la.
          eapply is_valid_updated_lmemory_lmem_incl with (la := (finz.seq_between b_src e_src))
          ; eauto.
          eapply is_valid_updated_lmemory_insert'; eauto.
          eapply Forall_forall; intros a' Ha'.
          eapply logical_region_version_neq; eauto ; last lia.
        }

        assert ( ((logical_region_map la lws) ) (v_src+1) ⊆ lmem' )
         as Hmem'_be_next.
        { eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
          assert (v' = v_src+1 /\ (a' ∈ la))
            as [? Ha'_in_be] by (subst la ; eapply logical_region_map_some_inv; eauto)
          ; simplify_eq.
          destruct Hvalid_lmem' as [Hupdate_version_region _].
          eapply lookup_weaken; last eapply Hupdate_version_region.
          rewrite update_version_region_preserves_lmem_next; eauto.
          { rewrite lookup_insert_ne.
            erewrite logical_region_map_lookup_versions; eauto.
            clear -Ha'_in_be.
            intro ; simplify_eq.
            apply not_elemof_list_remove_elem in Ha'_in_be ; auto.
          }
          { eapply elem_of_submseteq; eauto.
            eapply list_remove_elem_submsteq.
          }
          { rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
            eapply logical_region_version_neq; eauto; lia.
          }
        }

        rewrite -(insert_id lmem' (a_src, v_src) lw_pc); auto.
        iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha_pc Hmem]".
        rewrite -(insert_id (_ lmem') (a_src, v_src+1) lw_pc); auto.
        2: { rewrite lookup_delete_ne ; first by simplify_map_eq. intro ; simplify_eq ; lia. }
        iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha_next Hmem]".
        eapply delete_subseteq_r with (k := ((a_src, v_src) : LAddr)) in Hmem'_be
        ; last (eapply logical_region_notin; eauto).
        eapply delete_subseteq_r with (k := ((a_src, v_src+1) : LAddr)) in Hmem'_be
        ; last (eapply logical_region_notin; eauto).
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange Hmem]"
        ; first (eapply Hmem'_be).
        eapply delete_subseteq_r with (k := ((a_src, v_src) : LAddr)) in Hmem'_be_next
        ; last (eapply logical_region_notin ; eauto).
        eapply delete_subseteq_r with (k := ((a_src, v_src+1) : LAddr)) in Hmem'_be_next
        ; last (eapply logical_region_notin ; eauto).
        eapply delete_subseteq_list_r
          with (m3 := list_to_map (zip (map (λ a : Addr, (a, v_src)) la) lws))
          in Hmem'_be_next
        ; eauto
        ; last (by eapply update_logical_memory_region_disjoint).
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange' Hmem]"
        ; first (eapply Hmem'_be_next); iClear "Hmem".
        iDestruct "HPrange" as "#HPrange".

        iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
        {
         iNext. subst la.
         iApply region_inv_construct; try done; auto.
        }
        iSplitL "Ha_pc"; first by iFrame.

        iMod (region_valid_alloc' _ p_src b_src e_src a_src (v_src+1) (a_src::la) (lw_pc::lws)
         with "[HPrange HP] [Hrange' Ha_next]")
         as "#Hinterp__next"; last done.
        { destruct p_src ; cbn in * ; try congruence; done. }
        { done. }
        { eapply list_remove_list_region ; auto.
          apply list_remove_elem_in in Ha_pc_in_range.
          subst la.
          by destruct Ha_pc_in_range as (la' & -> & ->).
        }
        { iDestruct (big_sepL2_sep_sepL_r with "[$Hread_cond $HPrange]") as "Hread_Ps".
          iDestruct (big_sepL2_alt with "Hread_Ps") as "[_ Hread_Ps']".
          iAssert (
              (∀ (k : nat) (x0 : leibnizO LWord * D),
                 ⌜zip lws Ps !! k = Some x0⌝
                 → x0.2 x0.1 ∗ □ (∀ lw0 : LWord, x0.2 lw0 -∗ fixpoint interp1 lw0) -∗ interp x0.1)
            )%I as "Hread_Ps_unzip".
          { iIntros (? ? ?) "[Ha Hpa]"; by iDestruct ("Hpa" with "Ha") as "?". }
          iDestruct (big_sepL_impl _ (fun _ xy => interp xy.1) with "Hread_Ps' Hread_Ps_unzip"
                    ) as "Hread_Ps_zip".
          iDestruct (big_sepL2_alt (fun _ lw _ => interp lw) lws Ps with "[$Hread_Ps_zip]") as "Hinterp_Ps"
          ; first by rewrite Hlen_lws.
          iSplit.
          by iApply "Hread".
          by iDestruct (big_sepL2_const_sepL_l (fun _ lw => interp lw) lws Ps with "Hinterp_Ps") as "[? ?]".
        }
        { iClear "#". clear -Hlen_Ps Hlen_lws.
          iApply big_sepL2_alt.
          subst la.
          iSplit; first (iPureIntro; rewrite /= map_length; lia).
          iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame.
          rewrite fst_zip.
          apply NoDup_fmap; auto.
          { by intros x y Heq ; simplify_eq. }
          rewrite /logical_region map_length Hlen_lws ; lia.
        }

      + (* r ≠ PC *)
        iDestruct "HSweepMem" as (lws Hlen_lws ->) "HSweepRest".
        subst E'.
        destruct Hvalid_sweep as [Hcontra|Ha_pc_notin_src] ; first done.
        subst la.
        rewrite !list_remove_elem_notin in Hvalid_lmem', Hlen_Ps, Hlen_lws |- * ; auto.

        assert ( lmem' !! (a_pc, v_pc) = Some lw_pc ) as Hmem'_apc.
        { eapply is_valid_updated_lmemory_preserves_lmem; eauto; by simplify_map_eq. }
        assert ( logical_range_map b_src e_src lws v_src ⊆ lmem' )
          as Hmem'_be.
        {
          eapply is_valid_updated_lmemory_lmem_incl with
            (la := (finz.seq_between b_src e_src)) (v := v_src)
          ; eauto.
          eapply is_valid_updated_lmemory_insert; eauto.
          eapply logical_range_notin; eauto.
          eapply Forall_forall; intros a' Ha'.
          eapply logical_range_version_neq; eauto ; last lia.
        }
        assert
          (logical_range_map b_src e_src lws (v_src + 1) ⊆ lmem')
          as Hmem'_be_next.
        { clear -Hvalid_lmem' Hlen_lws Ha_pc_notin_src.
          eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
          assert (v' = v_src+1 /\ (a' ∈ (finz.seq_between b_src e_src)))
            as [? Ha'_in_be] by (eapply logical_range_map_some_inv; eauto); simplify_eq.
          destruct Hvalid_lmem'.
          eapply lookup_weaken; last eauto.
          rewrite update_version_region_preserves_lmem_next; eauto.
          all: rewrite lookup_insert_ne //=; last (intro ; set_solver).
          erewrite logical_region_map_lookup_versions; eauto.
          eapply logical_region_version_neq; eauto; lia.
        }

        rewrite -(insert_id lmem' (a_pc, v_pc) lw_pc); auto.
        iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha_pc Hmem]".
        eapply delete_subseteq_r with (k := ((a_pc, v_pc) : LAddr)) in Hmem'_be
        ; last (eapply logical_region_notin; eauto).
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange Hmem]"
        ; first (eapply Hmem'_be).
        eapply delete_subseteq_r with (k := ((a_pc, v_pc) : LAddr)) in Hmem'_be_next
        ; last (eapply logical_region_notin ; eauto).
        eapply delete_subseteq_list_r
          with (m3 := list_to_map (zip (map (λ a : Addr, (a, v_src))
                                          (finz.seq_between b_src e_src)) lws))
          in Hmem'_be_next
        ; eauto
        ; last (by eapply update_logical_memory_region_disjoint).
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hrange' Hmem]"
        ; first (eapply Hmem'_be_next); iClear "Hmem".
        iDestruct "HSweepRest" as "(HPrange & %Hpers & #Hread_cond & Hcls_src)".
        iDestruct "HPrange" as "#HPrange".
        iMod ("Hcls_src" with "[Hrange HPrange]") as "_".
        {
          iNext.
          iApply region_inv_construct; try done; auto.
        }
        iSplitL "Ha_pc"; first by iFrame.

        iMod (region_valid_alloc _ p_src b_src e_src a_src (v_src +1) lws
               with "[HPrange] [Hrange']")
          as "#Hinterp__next"; last done.
        { destruct p_src ; cbn in * ; try congruence; done. }
        { done. }
        { iDestruct ( big_sepL2_sep_sepL_r with "[$Hread_cond $HPrange]") as "Hread_Ps".
          iDestruct (big_sepL2_alt with "Hread_Ps") as "[_ Hread_Ps']".
          iAssert (
              (∀ (k : nat) (x0 : leibnizO LWord * D),
                 ⌜zip lws Ps !! k = Some x0⌝
                 → x0.2 x0.1 ∗ □ (∀ lw0 : LWord, x0.2 lw0 -∗ fixpoint interp1 lw0) -∗ interp x0.1)
            )%I as "Hread_Ps_unzip".
          { iIntros (? ? ?) "[Ha Hpa]"; by iDestruct ("Hpa" with "Ha") as "?". }
          iDestruct (big_sepL_impl _ (fun _ xy => interp xy.1) with "Hread_Ps' Hread_Ps_unzip"
                    ) as "Hread_Ps_zip".
          iDestruct (big_sepL2_alt (fun _ lw _ => interp lw) lws Ps with "[$Hread_Ps_zip]")
            as "Hinterp_Ps"
          ; first by rewrite Hlen_lws.
          by iDestruct (big_sepL2_const_sepL_l (fun _ lw => interp lw) lws Ps with "Hinterp_Ps") as "[? ?]".
        }
        { iClear "#". clear -Hlen_Ps Hlen_lws.
          iApply big_sepL2_alt.
          iSplit; first (iPureIntro; rewrite map_length; lia).
          iDestruct (big_sepM_list_to_map with "Hrange'") as "?" ; last iFrame.
          rewrite fst_zip; first (apply NoDup_logical_region).
          rewrite /logical_region map_length Hlen_lws ; lia.
        }
  Qed.

  Local Instance if_Persistent
    p_pc b_pc e_pc a_pc v_pc lregs src p_src b_src e_src a_src v_src:
    Persistent (if decide (reg_allows_sweep (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs)
                             src p_src b_src e_src a_src v_src
                           ∧ (src = PC ∨ a_pc ∉ finz.seq_between b_src e_src))
                then interp (LCap p_src b_src e_src a_src (v_src + 1))
                else emp)%I.
  Proof. intros; case_decide; apply _. Qed.


  Lemma isunique_case (lregs : leibnizO LReg)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (lw_pc : LWord) (dst src : RegName) (P : D):
    ftlr_instr lregs p_pc b_pc e_pc a_pc v_pc lw_pc (IsUnique dst src) P.
  Proof.
    intros Hp Hsome HcorrectLPC Hbae Hi.
    iIntros "#IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha #HP Hcls HPC Hmap".
    specialize (HpersP lw_pc).
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Hx|Hx].
      rewrite Hx lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p_src b_src e_src a_src v_src, read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src p_src b_src e_src a_src v_src)
      as (p_src & b_src & e_src & a_src & v_src & HV_Src).
    {
      specialize Hsome' with src as Hsrc.
      destruct Hsrc as [wsrc Hsome_src].
      unfold read_reg_inr. rewrite Hsome_src.
      destruct wsrc as [|[ p_src b_src e_src a_src v_src|] | ]; try done.
      by repeat eexists.
    }

    (* Step 1: open the region, if necessary,
       and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_sweep_res with "[$Hreg] [$Hinv]") as (Ps) "[%Hlen_Ps HSweepRes]"
    ; [ eassumption
      | by apply elem_of_finz_seq_between
      |].

    (* Step 2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iMod (sweep_res_implies_mem_map with "HSweepRes Ha") as (mem) "[HSweepMem >HMemRes]".
    set (E := ⊤ ∖ ↑logN.@(a_pc, v_pc)).
    set (E' := allow_sweep_mask a_pc v_pc (list_remove_elem a_pc (finz.seq_between b_src e_src)) v_src ).

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds with "HSweepMem") as %HReadPC.

    (* Step 4: move the later outside, so that we can remove it after applying wp_isunique *)
    iDestruct (allow_sweep_mem_later with "HSweepMem") as "HSweepMem"; auto.

    iAssert ( ⌜ allows_sweep (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) src ⌝)%I as "%Hallows_sweep".
    { iDestruct "HSweepRes" as "(_&%HsweepRes&_)".
      iPureIntro. apply HsweepRes.
    }

    iApply (wp_isunique with "[$Hmap $HMemRes]")
    ; eauto
    ; [ by simplify_map_eq
      | rewrite /subseteq /map_subseteq /set_subseteq_instance
        ; intros rr _; apply elem_of_dom
        ; rewrite lookup_insert_is_Some';
        eauto
      | ].
    iNext; iIntros (lregs' lmem' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as
      [ p_src' b_src' e_src' a_src' v_src' Hlwsrc' Hp_neq_E Hupd Hunique_regs Hincr_PC
      | ? Hlwsrc Hnot_sealed Hunique_regs Hmem' Hincr_PC
      | lwsrc' p_src' b_src' e_src' a_src' v_src' Hlwsrc Hlwsrc' Hmem' Hincr_PC
      | ? ? Hfail]
    ; simplify_map_eq
    ; try (rewrite Hlwsrc' in Hlregs_src; simplify_eq)
    ; try (rewrite Hlwsrc in Hlregs_src; simplify_eq)
    ; try (cbn in Hlwsrc' ; simplify_eq).

    { (* Sweep true cap : update *)
      rewrite /read_reg_inr Hlwsrc' in HV_Src ; simplify_eq.
      iMod (mem_map_recover_res_update_version with "Hread HP HSweepMem Hmem")
        as "[Ha #Hinterp]"; auto.

      iModIntro.
      iMod ("Hcls" with "[Ha HP]") as "_"; first (iNext ; iExists _ ; iFrame "#∗").
      iModIntro.
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      simplify_map_eq.

      incrementLPC_inv
        as (p_pc' & b_pc' & e_pc' &a_pc' &v_pc' & ? & HPC & Z & Hregs')
      ; simplify_map_eq.
      assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq); simplify_map_eq.
      rewrite /sweep_mask_cond.
      set (cond_open := decide ( _ /\ _ )).
      destruct cond_open as [Hdecide|Hdecide]; cycle 1.
      - (* Case (p_src = O) *)
        apply reg_allows_sweep_unique_O in Hdecide; auto ; simplify_eq.
        assert (src ≠ PC)
          as Hr_ne_pc
             by (intro ; subst
                 ; inversion HcorrectLPC as [lpc ? ? ? ? Heq HcorrectPC Hlpc]
                 ; inversion HcorrectPC as [? ? ? ? Hbounds Hperm]
                 ; cbn in * ; simplify_map_eq
                 ; by destruct Hperm).
        do 2 (rewrite (insert_commute _ _ PC) //); rewrite !insert_insert.
        simplify_map_eq.
        iApply ("IH" $! (<[dst := LInt 1]> (<[src := _]> lregs)) with "[%] [] [Hmap] [$Hown]")
        ; eauto.
        { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
        { iIntros (r1 lw1 Hr1 Hlw1).
          destruct (decide (r1 = dst)) as [ |Hr1_dst]
          ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
          destruct (decide (r1 = src)) as [ |Hr1_src]
          ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
          iApply "Hreg"; eauto.
        }
        { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; try done. }
      - destruct Hdecide as [ [Hsrc_lregs Hread_src] Hwf].
        destruct (decide (src = PC)) as [->|Hsrc_neq_pc]
        ; [clear Hwf | destruct Hwf ; simplify_eq]
        ; simplify_map_eq
        ; do 2 (rewrite (insert_commute _ _ PC) //); rewrite !insert_insert.
        + (* src = PC *)
          iApply ("IH" $! (<[dst := LInt 1]> lregs) with "[%] [] [Hmap] [$Hown]")
          ; eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (r1 lw1 Hr1 Hlw1).
            destruct (decide (r1 = dst)) as [ |Hr1_dst]
            ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
            iApply "Hreg"; eauto.
          }
          { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; try done. }
        + (* src ≠ PC *)
          iApply ("IH" $! (<[dst := LInt 1]> ( <[src := _ ]> lregs)) with "[%] [] [Hmap] [$Hown]")
          ; eauto.
          { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
          { iIntros (r1 lw1 Hr1 Hlw1).
            destruct (decide (r1 = dst)) as [ |Hr1_dst]
            ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
            destruct (decide (r1 = src)) as [ |Hr1_src]
            ; simplify_map_eq; first (rewrite !fixpoint_interp1_eq //=).
            iApply "Hreg"; eauto.
          }
          { rewrite !fixpoint_interp1_eq //= ; destruct p_pc'; destruct Hp ; try done. }
    }
    { (* Sweep false  *)

      iMod (mem_map_recover_res_no_update with "HSweepMem Hmem") as "Ha_pc"; auto.
      subst E.
      iModIntro.
      iMod ("Hcls" with "[Ha_pc HP]") as "_"; [iNext; iExists lw_pc ; iFrame|iModIntro]; auto.
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      incrementLPC_inv; simplify_map_eq.
      assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
      simplify_map_eq.
      rewrite (insert_commute _ _ PC) // insert_insert.
      iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
      { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
      {
        iIntros (ri ? Hri Hvs).
        destruct (decide (ri = dst)); simplify_map_eq.
        by rewrite !fixpoint_interp1_eq.
        iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
      }
      iModIntro.
      rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
    }

    { (* Sweep sealed  *)
      iMod (mem_map_recover_res_no_update with "HSweepMem Hmem") as "Ha_pc"; auto.
      subst E.
      iModIntro.
      iMod ("Hcls" with "[Ha_pc HP]") as "_"; [iNext; iExists lw_pc ; iFrame|iModIntro]; auto.
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      incrementLPC_inv; simplify_map_eq.
      assert (dst ≠ PC) as Hdst_pc by (intro ; simplify_map_eq).
      simplify_map_eq.
      rewrite (insert_commute _ _ PC) // insert_insert.
      iApply ("IH" $! (<[dst := _]> lregs) with "[%] [] [Hmap] [$Hown]"); eauto.
      { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
      {
        iIntros (ri ? Hri Hvs).
        destruct (decide (ri = dst)); simplify_map_eq.
        by rewrite !fixpoint_interp1_eq.
        iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
      }
      iModIntro.
      rewrite !fixpoint_interp1_eq /=; destruct Hp as [-> | ->]; iFrame "Hinv"; auto.
    }

    { (* Fail  *)
      iMod (mem_map_recover_res_no_update with "HSweepMem Hmem") as "Ha_pc"; auto.
      subst E.
      iModIntro.
      iMod ("Hcls" with "[Ha_pc HP]") as "_"; auto.
      iModIntro.
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_"; iApply wp_value; auto.
      iIntros; discriminate.
    }
Qed.

End fundamental.
