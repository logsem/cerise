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

  Lemma wp_load_general Ep
    pc_p pc_b pc_e pc_a pc_v pca_v
    r1 r2 lw (lmem : LMem) (dfracs : LDFrac) lregs :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →

    lmem !! (pc_a, pca_v) = Some lw →
    allow_load_map_or_true r2 lregs lmem →
    dom lmem = dom dfracs →

    {{{ (▷ [∗ map] la↦dw ∈ prod_merge dfracs lmem, la ↦ₐ{dw.1} dw.2) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Load_spec lregs r1 r2 lregs' lmem retv⌝ ∗
            ([∗ map] la↦dw ∈ prod_merge dfracs lmem, la ↦ₐ{dw.1} dw.2) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ) "(>Hmem & >Hmap) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid_inclSepM_general with "Hm Hmem") as %Hmem.
    rewrite prod_merge_snd_inv in Hmem.

    (* Derive necessary register values in r *)
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [lr2v [Hlr'2 Hlr2]]. by set_solver+.
    odestruct (Hri r1) as [lr1v [Hlr'1 _]]. by set_solver+. clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! (pc_a, pca_v))) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs lmem !! (pc_a, pca_v) = Some (dq,lw)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs lmem) lm with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto; eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_corresponds_reg ; eauto ; cbn ; eauto.
    2: eapply state_phys_corresponds_mem ; eauto; cbn ; eauto.

    set (lrw2 := lword_get_word lr2v).
    assert ( reg !! r2 = Some lrw2 ) as Hr2 by (eapply state_phys_log_reg_get_word ; eauto).
    rewrite /exec /= Hr2 /= in Hstep.

    (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
    destruct (is_log_cap lr2v) eqn:Hlr2v.
    2:{ (* Failure: r2 is not a capability *)
      assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->).
      {
        apply is_log_cap_is_cap_false_iff in Hlr2v.
        subst lrw2; cbn in *.
        destruct_lword lr2v; cbn in * ; try by simplify_pair_eq.
      }

      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, cur_map; iFrame; auto
        | iApply "Hφ" ; iFrame ; iFailCore Load_fail_const
        ].
    }
    subst lrw2; cbn in *.
    destruct_lword lr2v; cbn in * ; try congruence. clear Hlr2v.

    destruct (readAllowed p && withinBounds b e a) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, cur_map; iFrame; eauto
        | iApply "Hφ" ; iFrame ; iFailCore Load_fail_bounds
        ].
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    pose proof (allow_load_implies_loadv r2 lmem lregs p b e a v) as (loadv & Hmema); auto.

    assert (is_Some (dfracs !! (a, v))) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs lmem !! (a, v) = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs lmem) lm (a, v) loadv with "Hm Hmem" ) as %Hma' ; eauto.
    assert ( mem !! a = Some (lword_get_word loadv) ) as Hma2
        by (eapply state_phys_log_mem_get_word ; eauto).

    rewrite Hma2 /= in Hstep.
    rewrite /update_reg /= in Hstep.
    destruct (incrementLPC (<[ r1 := loadv ]> lregs)) as  [ lregs' |] eqn:Hlregs'
    ; pose proof Hlregs' as H'lregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      cbn in Hlregs'.
      apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'.


      eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hlregs'.
      2: {
        rewrite /lreg_strip lookup_fmap.
        apply fmap_is_Some.
        destruct (decide (r1 = PC)) ; simplify_map_eq; auto.
      }
      2: by apply map_fmap_mono; apply insert_mono ; eauto.
      simplify_pair_eq.
      rewrite ( _ :
                (λ lw : LWord, lword_get_word lw) <$> <[r1:=loadv]> lr = <[r1:= lword_get_word loadv]> reg
              ) in Hlregs'; cycle 1.
      { destruct HLinv as [[Hstrips Hcurreg] _].
        rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto.
      }
      rewrite Hlregs' in Hstep. inversion Hstep.
      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, cur_map; iFrame; auto
        | iApply "Hφ" ; iFrame ; iFailCore Load_fail_invalid_PC
        ].
    }

    (* TODO this part of the proof is awful, but it is because we need to destruct r1 = PC *)
    (* Success *)
    destruct (decide (r1 = PC)); subst
    ; rewrite /update_reg /= in Hstep
    ; eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
          as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->)
    ; simplify_map_eq
    ; (eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC ; [|by apply map_fmap_mono; apply insert_mono ; eauto])
    ; [replace ((λ lw : LWord, lword_get_word lw) <$> <[PC:=LCap p1 b1 e1 a1 v1]> lr)
        with (<[PC:=WCap p1 b1 e1 a1]> reg) in HuPC
          by (destruct HLinv as [[Hstrips Hcurreg] _] ; rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto)
      |
        replace ((λ lw : LWord, lword_get_word lw) <$> <[r1:=loadv]> lr)
        with (<[r1:= (lword_get_word loadv)]> reg) in HuPC
          by (destruct HLinv as [[Hstrips Hcurreg] _] ; rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto)]
    ; rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn
    ; [rewrite insert_insert; rewrite insert_insert in H'lregs' |]
    ; [|iMod ((gen_heap_update_inSepM _ _ r1 loadv) with "Hr Hmap") as "[Hr Hmap]"; eauto]
    ; iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
    ; try (by destruct (decide (r1 = PC)) ; simplify_map_eq; auto).
    all: iFrame; iModIntro
    ; iSplitR "Hφ Hmap Hmem"
    ; [|iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto
        ; rewrite /reg_allows_load; eauto ; eapply lookup_prod_merge_snd ; eauto].
    all: iExists _, lm, cur_map; iFrame; auto
    ; iPureIntro; econstructor; eauto
    ; [| by destruct HLinv as [_ ?]]
    ; destruct HLinv as [[Hstrips Hcur_reg] HmemInv]
    ; cbn in *
    ; split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=.
    - apply map_Forall_insert_2; auto.
      destruct HmemInv as [Hdom Hroot].
      eapply map_Forall_lookup_1 with (i := (a,v)) in Hdom ; eauto.
      eapply map_Forall_lookup_1 with (i := a) in Hroot ; eauto.
      destruct Hroot as (lw' & ? & Hma'' & Hcur').
      rewrite Hma2 in Hma'' ; simplify_eq.
      destruct_lword lw'; cbn in * ; simplify_eq.
      eapply lookup_prod_merge_snd in Hmemadq.
      eapply lookup_weaken_inv in Hmem; eauto; cbn in * ; simplify_eq.
      auto.
    - clear Hlr'1 Hlr'2.
      apply map_Forall_insert_2 ; [ | apply map_Forall_insert_2; cbn ; auto].
      cbn.
      assert (lr !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v)) by (eapply lookup_weaken; eauto).
      eapply map_Forall_lookup_1 with (i := PC) in Hcur_reg ; eauto.
      rewrite /is_cur_word in Hcur_reg.
      eapply lookup_weaken_inv in Hregs; eauto; cbn in * ; simplify_eq.
      eapply Hcur_reg.
      eapply mem_phys_log_current_word; eauto ; eapply lookup_weaken; eauto.
  Qed.

  Lemma wp_load Ep
    pc_p pc_b pc_e pc_a pc_v pca_v
    r1 r2 lw lmem lregs dq :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →
    lmem !! (pc_a, pca_v) = Some lw →
    allow_load_map_or_true r2 lregs lmem →
    {{{ (▷ [∗ map] la↦w ∈ lmem, la ↦ₐ{dq} w) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
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
    E r1 r2 pc_p pc_b pc_e pc_a pc_v pca_v
    lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ (if ((a, v) =? (pc_a, pca_v))%la then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ (if ((a, v) =? (pc_a, pca_v))%la then lw else lw')
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (if ((a, v) =? (pc_a, pca_v))%la then emp else (a, v) ↦ₐ{dq'} lw') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".

    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ la dq lw, la ↦ₐ{dq} lw)%I with "Hi Hr2a") as (lmem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs] ; cbn in *.

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pca_v)); by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto.
      destruct ((a =? pc_a)%Z && (v =? pca_v)) eqn:Heq ; simplify_map_eq; eauto. }
    { destruct ((a =? pc_a)%Z && (v =? pca_v)); simplify_eq
     ; subst ; rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pca_v).
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

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_b pc_e pc_a pc_v pca_v lw lw'
    lw'' p b e a v pc_a' dq dq':
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a,v) ↦ₐ{dq'} lw' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a,v) ↦ₐ{dq'} lw' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct ((a =? pc_a)%Z && (v =? pca_v)) eqn:Ha.
    { apply andb_true_iff in Ha. destruct Ha as [Ha Hv].
      apply Z.eqb_eq in Ha; apply Nat.eqb_eq in Hv.
      replace a with pc_a by solve_addr.
      replace v with pca_v.
      iDestruct (mapsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      replace pc_a with a by solve_addr; auto.
      all: cbn.
      all: assert (pc_a =? pc_a = true)%Z as -> by (apply Z.eqb_refl).
      all: assert (pca_v =? pca_v = true) as -> by (apply Nat.eqb_refl).
      done.
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ". iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame. Unshelve. apply (LInt 0). apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw'' p b e
    v pc_a' dq:
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e pc_a pc_v }}}
      Instr Executable @ E
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

  Lemma wp_load_success_same E r1 pc_p pc_b pc_e pc_a pc_v pca_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ (if ((a =? pc_a)%Z && (v =? pca_v)) then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ (if ((a =? pc_a)%Z && (v =? pca_v)) then lw else lw')
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw
             ∗ (if ((a =? pc_a)%Z && (v =? pca_v)) then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ la dq lw, la ↦ₐ{dq} lw)%I with "Hi Hr1a") as
        (lmem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pca_v)); by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto.
      destruct ((a =? pc_a)%Z && (v =? pca_v)) eqn:Heq ; simplify_map_eq; eauto. }
    { destruct ((a =? pc_a)%Z && (v =? pca_v)); simplify_eq
     ; subst ; rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pca_v).
         split ; eauto.
       }
       incrementLPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ _ _ Hmem H4) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       destruct ((a0 =? x2)%Z && (v0 =? pca_v)); iFrame.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  (* TODO not useful without automation *)

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_b pc_e pc_a pc_v pca_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, pc_v) ↦ₐ{dq'} lw' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw
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

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_b pc_e pc_a pc_v pca_v lw p b e v pc_a' dq :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e pc_a v}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw }}}.
  Proof.
  (*   intros. iIntros "(>HPC & >Hpc_a & >Hr1)". *)
  (*   iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto. *)
  (*   { rewrite Z.eqb_refl. eauto. } *)
  (*   iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl. *)
  (*   iApply "Hφ". iFrame. Unshelve. all: eauto. *)
  (* Qed. *)
  Admitted.

  (* (* If a points to a capability, the load into PC success if its address can be incr *) *)
  Lemma wp_load_success_PC E r2 pc_p pc_b pc_e pc_a pc_v pca_v lw
        p b e a v p' b' e' a' v' a'' :
    decodeInstrWL lw = Load PC r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ lw
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ LCap p' b' e' a' v' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap p' b' e' a'' v'
             ∗ (pc_a, pca_v) ↦ₐ lw
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

  Lemma wp_load_success_fromPC E r1 pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw lw'' dq :
    decodeInstrWL lw = Load r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ (pc_a, pca_v) ↦ₐ{dq} lw
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

  Lemma wp_load_success_alt E r1 r2 pc_p pc_b pc_e pc_a pc_v pca_v lw lw' lw'' p
    b e a v pc_a' :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ lw' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pca_v) ↦ₐ lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a, v) ↦ₐ lw' }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ". *)
  (*   iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse. *)
  (*   { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. } *)
  (*   iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame. *)
  (* Qed. *)
  Admitted.

  Lemma wp_load_success_same_alt E r1 pc_p pc_b pc_e pc_a pc_v pca_v lw lw' p b e a v pc_a' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pca_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ lw'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pca_v) ↦ₐ lw
             ∗ (a, v) ↦ₐ lw' }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ". *)
  (*   iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse. *)
  (*   { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. } *)
  (*   iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame. *)
  (* Qed. *)
  Admitted.



End cap_lang_rules.
