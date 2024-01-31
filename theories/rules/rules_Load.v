From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base stdpp_extra.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Definition reg_allows_load (lregs : LReg) (r : RegName) p b e a v :=
    lregs !! r = Some (LCap p b e a v) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure (lregs: LReg) (r1 r2: RegName) (lmem : LMem) :=
  | Load_fail_const lw:
      lregs !! r2 = Some lw ->
      is_log_cap lw = false →
      Load_failure lregs r1 r2 lmem
  | Load_fail_bounds p b e a v:
      lregs !! r2 = Some (LCap p b e a v) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      Load_failure lregs r1 r2 lmem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p b e a v loadv:
      lregs !! r2 = Some (LCap p b e a v) ->
      lmem !! (a, v) = Some loadv →
      incrementLPC (<[ r1 := loadv ]> lregs) = None ->
      Load_failure lregs r1 r2 lmem
  .

  Inductive Load_spec
    (lregs: LReg) (r1 r2: RegName)
    (lregs': LReg) (lmem : LMem) : cap_lang.val → Prop
  :=
  | Load_spec_success p b e a v loadv :
    reg_allows_load lregs r2 p b e a v →
    lmem !! (a, v) = Some loadv →
    incrementLPC (<[ r1 := loadv ]> lregs) = Some lregs' ->
    Load_spec lregs r1 r2 lregs' lmem NextIV

  | Load_spec_failure :
    Load_failure lregs r1 r2 lmem ->
    Load_spec lregs r1 r2 lregs' lmem FailedV.

  Definition allow_load_map_or_true r (lregs : LReg) (lmem : LMem):=
    ∃ p b e a v, read_reg_inr lregs r p b e a v ∧
      if decide (reg_allows_load lregs r p b e a v) then
        ∃ lw, lmem !! (a, v) = Some lw
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (lmem : LMem) (lr : LReg) (p : Perm) (b e a : Addr) v,
      allow_load_map_or_true r2 lr lmem
      → lr !! r2 = Some (LCap p b e a v)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : LWord),
          lmem !! (a, v) = Some loadv.
  Proof.
    intros r2 lmem lr p b e a v HaLoad Hr2v Hra Hwb.
    unfold allow_load_map_or_true, read_reg_inr in HaLoad.
    destruct HaLoad as (?&?&?&?&?& Hrinr & Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - exact Hmem.
    - contradiction Hrega. done.
  Qed.

  Lemma mem_eq_implies_allow_load_map:
    ∀ (lregs : LReg) (lmem : LMem)(r2 : RegName) (lw : LWord) p b e a v,
      lmem = <[(a, v):=lw]> ∅
      → lregs !! r2 = Some (LCap p b e a v)
      → allow_load_map_or_true r2 lregs lmem.
  Proof.
    intros lregs lmem r2 lw p b e a v Hmem Hrr2.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      exists lw. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (lregs : LReg) (lmem : LMem) (r2 : RegName) (pc_a : Addr) (pca_v : Version)
      (lw lw' : LWord) p b e a v,
      (a ≠ pc_a \/ v <> pca_v)
      → lmem = <[(pc_a, pca_v):= lw]> (<[(a, v) := lw']> ∅)
      → lregs !! r2 = Some (LCap p b e a v)
      → allow_load_map_or_true r2 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a pca_v lw lw' p b e a v H4 Hrr2 Hreg2.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hreg2.
    - case_decide; last done.
      exists lw'.
      destruct H4; assert ((pc_a, pca_v) <> (a, v)) by congruence; simplify_map_eq; auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (lregs : LReg)(lmem : LMem)(r2 : RegName) (pc_a : Addr) pca_v
      (lw lw' : LWord) p b e a v,
      (if ((a,v ) =? (pc_a, pca_v))%la
       then lmem = <[(pc_a, pca_v):=lw]> ∅
       else lmem = <[(pc_a, pca_v):=lw]> (<[(a, v):=lw']> ∅))
      → lregs !! r2 = Some (LCap p b e a v)
      → allow_load_map_or_true r2 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a pca_v lw lw' p b e a v H4 Hrr2.
    destruct ((a,v) =? (pc_a, pca_v))%la eqn:Heq; cbn in Heq.
      + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2].
        apply Z.eqb_eq, finz_to_z_eq in Heq1. subst a.
        apply Nat.eqb_eq in Heq2. subst v.
        eapply mem_eq_implies_allow_load_map; eauto.
      + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq]
      ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ]
      ; eapply (mem_neq_implies_allow_load_map _ _ _ pc_a pca_v _ _ _ _ _ a v) ; eauto.
        left ; solve_addr.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (pca_v : Version) (lw lw' : LWord) (a : Addr)
      (lmem : LMem) (loadv : LWord) v,
      (if ((a,v ) =? (pc_a, pca_v))%la
       then lmem = <[(pc_a, pca_v):=lw]> ∅
       else lmem = <[(pc_a, pca_v):=lw]> (<[(a, v):=lw']> ∅))→
      lmem !! (a,v) = Some loadv →
      loadv = (if ((a,v ) =? (pc_a, pca_v))%la then lw else lw').
  Proof.
    intros pc_a pca_v lw lw' a lmem loadv v H4 H6.
    destruct ((a,v ) =? (pc_a, pca_v))%la eqn:Heq; cbn in Heq ; rewrite H4 in H6.
    + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2].
      apply Z.eqb_eq, finz_to_z_eq in Heq1; subst a.
      apply Nat.eqb_eq in Heq2; subst v.
      by simplify_map_eq.
    + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq]
      ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ]
      ; rewrite lookup_insert_ne in H6; try congruence; try by simplify_map_eq.
  Qed.

  Lemma wp2_mem_lookup {lrt lmt dft φ φt lr lm df Φs Φf r p b e a v lwa} :
    withinBounds b e a = true ->
    lrt !! r = Some (LCap p b e a v) ->
    lmt !! (a,v) = Some lwa ->
    state_interp_transient φ φt lr lrt lm lmt df dft ∗
      (state_interp_transient φ φt lr lrt lm lmt df dft -∗ Φs lwa (lword_get_word lwa)) ⊢
      wp_opt2 (lmt !! (a,v)) (mem φt !! a) Φf Φs.
  Proof.
    iIntros (Hin_bounds Hlrt_r Hlmt_a) "(Hσr & Hk)".
    iPoseProof (state_interp_transient_corr with "Hσr") as "%Hcor".
    destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
    rewrite Hlmt_a.
    eapply lookup_weaken in Hlmt_a, Hlrt_r; eauto.
    eapply state_phys_corresponds_mem in Hlmt_a; eauto; cbn in Hlmt_a.
    2: { eapply state_corresponds_cap_cur_addr; eauto; by cbn. }
    rewrite Hlmt_a.
    iApply wp2_val. now iApply "Hk".
  Qed.

  Lemma update_state_interp_from_cap_mod {σ dst lw2 Ep lregs lmem df p b e a v r}:
    dst ∈ dom lregs ->
    dom df = dom lmem ->

    lregs !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    lmem !! (a, v) = Some lw2 ->

    state_interp_logical σ
      ∗ ([∗ map] k↦y ∈ lregs, k ↦ᵣ y)
      ∗ ([∗ map] la↦dw ∈ prod_merge df lmem, la ↦ₐ{dw.1} dw.2)
      ⊢ |={Ep}=>
          state_interp_logical (update_reg σ dst (lword_get_word lw2))
            ∗ ([∗ map] k↦y ∈ <[ dst := lw2 ]> lregs, k ↦ᵣ y)
            ∗ ([∗ map] la↦dw ∈ prod_merge df lmem, la ↦ₐ{dw.1} dw.2)
  .
  Proof.
    iIntros (Hdst Hdom Hr Hinbounds Ha) "(Hσ & Hregs & Hmem)".
    iDestruct "Hσ" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iPoseProof (gen_heap_valid_inclSepM with "Hr Hregs") as "%Hlregs_incl".
    iPoseProof (gen_heap_valid_inclSepM_general with "Hm Hmem") as "%Hlmem_incl".
    iMod ((gen_heap_update_inSepM _ _ dst lw2) with "Hr Hregs") as "[Hr Hregs]"; eauto.
    { now apply elem_of_dom. }
    iModIntro. iFrame.
    iExists _,_,cur_map; iFrame.
    iPureIntro.
    apply snd_prod_merge_subseteq in Hlmem_incl; last done.
    eapply lookup_weaken in Ha ; eauto.
    apply state_phys_log_corresponds_update_reg; try easy.
    destruct HLinv as [Hinv_reg Hinv_mem].
    eapply lmem_read_iscur; eauto.
    eapply lookup_weaken in Hr ; eauto.
    eapply reg_corresponds_cap_cur_addr ; eauto; by cbn.
  Qed.

  Lemma update_state_interp_transient_from_cap_mod
    {σ σt lr lrt lm lmt df dft dst lw2 r p b e a v}:
    dst ∈ dom lrt ->
    lrt !! r = Some (LCap p b e a v) ->
    withinBounds b e a = true ->
    lmt !! (a, v) = Some lw2 ->
    state_interp_transient σ σt lr lrt lm lmt df dft ⊢
      state_interp_transient
      σ (update_reg σt dst (lword_get_word lw2))
      lr (<[ dst := lw2 ]> lrt) lm lmt df dft.
  Proof.
    iIntros (Hdom Hr Hinbounds Ha) "(Hσ & Hregs & Hmem & %Hcor & %Hdom_eq & Hcommit)"; cbn in *.
    iFrame "Hσ Hregs Hmem".
    iSplitR.
    - iPureIntro; cbn.
      destruct Hcor as (lr' & lm' & cur_map & Hlrt_incl & Hlmt_incl & Hinv).
      exists (<[dst:=lw2]> lr'), lm', cur_map.
      split; auto.
      now apply insert_mono.
      split; auto.
      assert (is_cur_regs lr' cur_map) as Hcur_lr'
          by (by destruct Hinv as [[_ Hcur'] _]).
      eapply is_cur_regs_mono in Hcur_lr'; eauto.
      destruct Hinv as [Hregs ?] ; split ; auto.
      eapply lookup_weaken in Ha, Hr ; eauto.
      eapply lmem_read_iscur in Ha; eauto.
      by apply lreg_insert_respects_corresponds.
      eapply reg_corresponds_cap_cur_addr; eauto ; by cbn.
    - iSplit ; first done. iIntros (Ep) "H".
      iMod ("Hcommit" with "H") as "(Hσ & Hregs & Hmem)".
      destruct Hdom_eq as [_ Hdom_eq].
      iApply (update_state_interp_from_cap_mod Hdom Hdom_eq Hr Hinbounds Ha with "[$Hσ $Hregs $Hmem]").
  Qed.

  Lemma wp_load_general
    pc_p pc_b pc_e pc_a pc_v
    r1 r2 lw (lmem : LMem) (dfracs : LDFrac) lregs :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →

    lmem !! (pc_a, pc_v) = Some lw →
    allow_load_map_or_true r2 lregs lmem →
    dom lmem = dom dfracs →

    {{{ (▷ [∗ map] la↦dw ∈ prod_merge dfracs lmem, la ↦ₐ{dw.1} dw.2) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ ∅
      {{{ lregs' retv, RET retv;
          ⌜ Load_spec lregs r1 r2 lregs' lmem retv⌝ ∗
            ([∗ map] la↦dw ∈ prod_merge dfracs lmem, la ↦ₐ{dw.1} dw.2) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ) "(>Hmem & >Hregs) Hφ".
    (* extract pc_a *)
    assert (is_Some (dfracs !! (pc_a, pc_v))) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs lmem !! (pc_a, pc_v) = Some (dq,lw)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    rewrite -(insert_id (prod_merge dfracs lmem) _ _ Hmem_dpc).
    iDestruct (big_sepM_insert_delete with "Hmem") as "[Hpc_a Hmem]"; cbn.

    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hregs Hmem Hφ]").
    iModIntro.
    iIntros (σ) "(Hσ & Hregs &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    iApply wp_wp2.
    (* TODO is there a way to avoid writing the continuation by hand ? *)
    iApply (wp_opt2_bind (k1 := (fun (lwr : LWord) =>
             match lwr with
             | LCap p b e a v =>
                 if readAllowed p && withinBounds b e a
                 then (asrc ← lmem !! (a, v) ;
                       lpc ← incrementLPC ( <[r1 := asrc ]> lregs) ;
                      Some lpc) (* trick to bind with update_reg *)
                 else None
             | _ => None
             end))).
    iApply wp_opt2_eqn.

    iDestruct (big_sepM_insert_delete _ _ _ (dq, lw) with "[Hpc_a $Hmem]") as "Hmem"; iFrame.
    rewrite insert_id; auto.
    iMod (state_interp_transient_intro (lm := lmem) (df := dfracs)
           with "[$Hregs $Hσ Hmem]") as "Hσ"; iFrame ; first done.

    iApply (wp2_reg_lookup (lrt := lregs)) ; first by set_solver.

    iModIntro.
    iFrame "Hσ".
    iIntros (lw2) "Hσ %Hlrs %Hrs".
    destruct (is_log_cap lw2) eqn:Hlw2; cycle 1.
    {
      destruct_lword lw2 ; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & Hmem)".
      all: iFrame.
      all: iApply ("Hφ" with "[$Hmem $Hregs]").
      all: iPureIntro; constructor; eapply Load_fail_const; eauto.
    }

    destruct_lword lw2 ; cbn in * ; simplify_eq.
    destruct (decide (readAllowed p && withinBounds b e a = true)) as [Hread|Hread]
    ; [|apply not_true_is_false in Hread] ; rewrite Hread ;cycle 1;cbn.
    {
      apply andb_false_iff in Hread.
      iModIntro.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & Hmem)".
      iFrame.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro; constructor; eapply Load_fail_bounds; eauto.
    }

    apply andb_true_iff in Hread; destruct Hread as [ Hread Hinbounds ].
    iApply wp_opt2_bind.

    pose proof (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hlrs Hread Hinbounds)
      as Hmem_a; destruct Hmem_a as [lwa Hmem_a].

    iApply wp2_mem_lookup ; eauto.
    iFrame.
    iIntros "Hσ".

    iDestruct (update_state_interp_transient_from_cap_mod (dst := r1) (lw2 := lwa) with "Hσ")
      as "Hσ"; eauto.
    { now set_solver. }

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (φ1 := incrementLPC (<[ r1 := lwa]> lregs)) (k1 := (fun x => Some x))).
    iApply wp_opt2_eqn_both.
    iApply (wp2_opt_incrementPC with "[$Hσ Hφ]").
    { rewrite dom_insert. apply elem_of_union_r. now rewrite elem_of_dom HPC. }
    iSplit.
    - iIntros (φt' lrt') "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & Hmem)".
      iFrame.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      constructor.
      eapply Load_fail_invalid_PC; eassumption.
    - iIntros (regs' φt') "Hσ %Hlis %His".
      iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      eapply Load_spec_success; try eassumption; split; eauto.
  Qed.

  Lemma wp_load
    pc_p pc_b pc_e pc_a pc_v
    r1 r2 lw lmem lregs dq :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allow_load_map_or_true r2 lregs lmem →
    {{{ (▷ [∗ map] la↦w ∈ lmem, la ↦ₐ{dq} w) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ ∅
      {{{ lregs' retv, RET retv;
          ⌜ Load_spec lregs r1 r2 lregs' lmem retv⌝ ∗
            ([∗ map] la↦w ∈ lmem, la ↦ₐ{dq} w) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  Lemma wp_load_success
    r1 r2 pc_p pc_b pc_e pc_a pc_v
    lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ (if ((a, v) =? (pc_a, pc_v))%la then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ (if ((a, v) =? (pc_a, pc_v))%la then lw else lw')
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (if ((a, v) =? (pc_a, pc_v))%la then emp else (a, v) ↦ₐ{dq'} lw') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".

    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ la dq lw, la ↦ₐ{dq} lw)%I with "Hi Hr2a") as (lmem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs] ; cbn in *.

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto.
      destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Heq ; simplify_map_eq; eauto. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); simplify_eq
     ; subst ; rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pc_v).
         split ; eauto.
       }
       incrementLPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ _ _ Hmem H6) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_notinstr r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw'
    lw'' p b e a v pc_a' dq dq':
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a,v) ↦ₐ{dq'} lw' }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a,v) ↦ₐ{dq'} lw' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Ha.
    { apply andb_true_iff in Ha. destruct Ha as [Ha Hv].
      apply Z.eqb_eq in Ha; apply Nat.eqb_eq in Hv.
      replace a with pc_a by solve_addr.
      replace v with pc_v.
      iDestruct (mapsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      replace pc_a with a by solve_addr; auto.
      all: cbn.
      all: assert (pc_a =? pc_a = true)%Z as -> by (apply Z.eqb_refl).
      all: assert (pc_v =? pc_v = true) as -> by (apply Nat.eqb_refl).
      done.
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ". iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame. Unshelve. apply (LInt 0). apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_frominstr r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw'' p b e
    v pc_a' dq:
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e pc_a pc_v }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ r2 ↦ᵣ LCap p b e pc_a pc_v }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { by rewrite Z.eqb_refl Nat.eqb_refl ; cbn. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl Nat.eqb_refl ; cbn.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same r1 pc_p pc_b pc_e pc_a pc_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ (if ((a =? pc_a)%Z && (v =? pc_v)) then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ (if ((a =? pc_a)%Z && (v =? pc_v)) then lw else lw')
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ (if ((a =? pc_a)%Z && (v =? pc_v)) then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ la dq lw, la ↦ₐ{dq} lw)%I with "Hi Hr1a") as
        (lmem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto.
      destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Heq ; simplify_map_eq; eauto. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); simplify_eq
     ; subst ; rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pc_v).
         split ; eauto.
       }
       incrementLPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ _ _ Hmem H4) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       destruct ((a0 =? x2)%Z && (v0 =? x3)); iFrame.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  (* TODO not useful without automation *)

  Lemma wp_load_success_same_notinstr r1 pc_p pc_b pc_e pc_a pc_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, pc_v) ↦ₐ{dq'} lw' }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ (a, pc_v) ↦ₐ{dq'} lw' }}}.
  Proof.
  (*   intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)". *)
  (*   destruct (a =? pc_a)%a eqn:Ha. *)
  (*   { assert (a = pc_a) as Heqa. *)
  (*     { apply Z.eqb_eq in Ha. solve_addr. } *)
  (*     rewrite Heqa. subst a. *)
  (*     iDestruct (mapsto_agree with "Hpc_a Ha") as %->. *)
  (*     iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto. *)
  (*     rewrite Ha. done. *)
  (*     iNext. iIntros "(? & ? & ? & ?)". *)
  (*     iApply "Hφ". iFrame. rewrite Ha. iFrame. *)
  (*   } *)
  (*   iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]"); eauto. *)
  (*   rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ?)". rewrite Ha. *)
  (*   iApply "Hφ". iFrame. Unshelve. apply (WInt 0). apply DfracDiscarded. *)
  (* Qed. *)
  Admitted.

  Lemma wp_load_success_same_frominstr r1 pc_p pc_b pc_e pc_a pc_v lw p b e v pc_a' dq :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e pc_a v}}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw }}}.
  Proof.
  (*   intros. iIntros "(>HPC & >Hpc_a & >Hr1)". *)
  (*   iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto. *)
  (*   { rewrite Z.eqb_refl. eauto. } *)
  (*   iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl. *)
  (*   iApply "Hφ". iFrame. Unshelve. all: eauto. *)
  (* Qed. *)
  Admitted.

  (* (* If a points to a capability, the load into PC success if its address can be incr *) *)
  Lemma wp_load_success_PC r2 pc_p pc_b pc_e pc_a pc_v lw
        p b e a v p' b' e' a' v' a'' :
    decodeInstrWL lw = Load PC r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ LCap p' b' e' a' v' }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap p' b' e' a'' v'
             ∗ (pc_a, pc_v) ↦ₐ lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a, v) ↦ₐ LCap p' b' e' a' v' }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) *)
  (*           "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]". *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto. *)
  (*   iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto. *)
  (*     by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [ | * Hfail ]. *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H4 as [Hrr2 _]. simplify_map_eq. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: congruence. } *)
  (* Qed. *)
  Admitted.

  Lemma wp_load_success_fromPC r1 pc_p pc_b pc_e pc_a pc_v pc_a' lw lw'' dq :
    decodeInstrWL lw = Load r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw'' }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ r1 ↦ᵣ lw }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' φ) *)
  (*           "(>HPC & >Hi & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   rewrite memMap_resource_1_dq. *)
  (*   iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto. *)
  (*     by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [ | * Hfail ]. *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H3 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite -memMap_resource_1_dq. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_commute //= insert_insert insert_commute //= insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb]. *)
  (*      destruct o; apply Is_true_false in H3. all: try congruence. done. *)
  (*    } *)
  (* Qed. *)
  Admitted.

  Lemma wp_load_success_alt r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw' lw'' p
    b e a v pc_a' :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ lw' }}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a, v) ↦ₐ lw' }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ". *)
  (*   iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse. *)
  (*   { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. } *)
  (*   iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame. *)
  (* Qed. *)
  Admitted.

  Lemma wp_load_success_same_alt r1 pc_p pc_b pc_e pc_a pc_v lw lw' p b e a v pc_a' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ lw'}}}
      Instr Executable @ ∅
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ lw
             ∗ (a, v) ↦ₐ lw' }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ". *)
  (*   iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse. *)
  (*   { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. } *)
  (*   iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame. *)
  (* Qed. *)
  Admitted.

End cap_lang_rules.
