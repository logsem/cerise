From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base stdpp_extra.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
  Context `{reservedaddresses : ReservedAddresses}.
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

  Definition exec_optL_Load
    (lregs : LReg) (lmem : LMem)
    (dst src : RegName) : option LReg :=
    lwsrc ← lregs !! src ;
    match lwsrc with
    | LCap p b e a v =>
        if readAllowed p && withinBounds b e a
        then
          lwa ← lmem !! (a, v) ;
          lpc ← incrementLPC ( <[dst := lwa ]> lregs) ;
          Some lpc (* trick to bind with update_reg *)
        else None
    | _ => None
    end.

  Lemma wp_load_general Ep
    pc_p pc_b pc_e pc_a pc_v
    r1 r2 lw (lmem : LMemF) lregs :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →
    (snd <$> lmem) !! (pc_a, pc_v) = Some lw →
    allow_load_map_or_true r2 lregs (snd <$> lmem) →

    {{{ (▷ [∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Load_spec lregs r1 r2 lregs' (snd <$> lmem) retv⌝ ∗
            ([∗ map] la↦dw ∈ lmem, la ↦ₐ{dw.1} dw.2) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad φ) "(>Hmem & >Hregs) Hφ".
    (* extract pc_a *)
    assert (is_Some ((fst <$> lmem) !! (pc_a, pc_v))) as [dq Hdq].
    { apply elem_of_dom. rewrite dom_fmap. apply mk_is_Some in Hmem_pc. rewrite -elem_of_dom in Hmem_pc. now rewrite dom_fmap in Hmem_pc. }
    assert (lmem !! (pc_a, pc_v) = Some (dq,lw)) as Hmem_dpc.
    { rewrite !lookup_fmap in Hdq, Hmem_pc.
      unfold LMemF in *. (* necessary... *)

      destruct (lmem !! (pc_a, pc_v)) as [[a' b']|];
      inversion Hdq; inversion Hmem_pc; easy. }

    rewrite -(insert_id lmem _ _ Hmem_dpc).
    iDestruct (big_sepM_insert_delete with "Hmem") as "[Hpc_a Hmem]"; cbn.

   iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hregs Hmem Hφ]").

    iModIntro.
    iIntros (σ) "(Hσ & Hregs &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Load lregs (snd <$> lmem) r1 r2)).
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.

    iDestruct (big_sepM_insert_delete _ _ _ (dq, lw) with "[Hpc_a $Hmem]") as "Hmem"; iFrame.
    rewrite insert_id; auto.
    iDestruct (state_interp_transient_intro with "[$Hregs $Hσ $Hmem]") as "Hσ".

    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver.
    iIntros (lw2) "Hσ %Hlrs %Hrs".

    destruct (is_log_cap lw2) eqn:Hlw2; cycle 1.
    {
      destruct_lword lw2 ; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      all: iApply ("Hφ" with "[$Hmem $Hregs]").
      all: iPureIntro; constructor; by eapply Load_fail_const.
    }

    destruct_lword lw2 ; cbn in * ; simplify_eq.
    destruct (decide (readAllowed p && withinBounds b e a = true)) as [Hread|Hread]
    ; [|apply not_true_is_false in Hread] ; rewrite Hread ;cycle 1;cbn.
    {
      apply andb_false_iff in Hread.
      iModIntro.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro; constructor; by eapply Load_fail_bounds.
    }

    apply andb_true_iff in Hread; destruct Hread as [ Hread Hinbounds ].
    iApply wp_opt2_bind.

    destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hlrs Hread Hinbounds) as [lwa Hmem_a].
    iApply (wp2_mem_lookup with "[$Hσ Hcred Hφ]"); eauto.
    iIntros "Hσ".

    iDestruct (update_state_interp_transient_from_cap_mod (dst := r1) (lw2 := lwa) with "Hσ")
      as "Hσ"; eauto.
    { now set_solver. }

    rewrite updatePC_incrementPC.
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_opt_incrementPC with "[$Hσ Hφ]").
    { rewrite dom_insert. apply elem_of_union_r. now rewrite elem_of_dom HPC. }
    iSplit.
    - iIntros "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      constructor.
      by eapply Load_fail_invalid_PC.
    - iIntros (regs' φt') "Hσ %Hlis %His".
      iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      by eapply Load_spec_success.
  Qed.

  Lemma wp_load Ep
    pc_p pc_b pc_e pc_a pc_v
    r1 r2 lw (lmem : LMem) lregs dq :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
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
    iApply (wp_load_general with "[Hmem $Hreg]").
    7: { iModIntro. rewrite -(big_opM_fmap (fun w => (dq, w)) (fun la dw => la ↦ₐ{dw.1} dw.2)%I). iFrame. }
    all: eauto.
    1,2: by rewrite -map_fmap_compose map_fmap_id.
    iModIntro.
    iIntros (lregs' retv) "(HLoad & Hmem & Hregs)". iApply "Hφ".
    rewrite -map_fmap_compose map_fmap_id. iFrame.
    by rewrite big_opM_fmap.
  Qed.

  Lemma wp_load_success Ep
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
      Instr Executable @ Ep
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
    { destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Heq; simplify_eq;
      rewrite prod_merge_insert;
      by simplify_map_eq.
    }
    { eapply mem_implies_allow_load_map with (pc_a := pc_a) (pca_v := pc_v) (lw := lw) (lw' := lw')
      ; eauto; last by simplify_map_eq.
      cbn.
      destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Heq
      ; simplify_eq
      ; by rewrite !prod_merge_insert prod_merge_empty_l !fmap_insert fmap_empty.
    }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pc_v).
         split ; eauto.
       }
       incrementLPC_inv.
       assert (lmem !! (a0, v0) = Some loadv) as Hload.
       { destruct (decide ((a0 = pc_a) /\ (v0 = pc_v))) as [ [Heq_a Heq_v] |Heq]; subst.
         - assert (((pc_a =? pc_a)%f && (pc_v =? pc_v)) = true) as Heq.
           {
             rewrite andb_true_iff ; split; [solve_addr | by rewrite Nat.eqb_refl].
           }
           rewrite Heq in Hmem, Hdfracs ; simplify_map_eq.
           rewrite prod_merge_insert prod_merge_empty_l in H3.
           by simplify_map_eq.
         - rewrite not_and_r in Heq.
           assert (((a0 =? pc_a)%f && (v0 =? pc_v)) = false) as Hneq.
           {
             rewrite andb_false_iff.
             destruct Heq as [Hneq | Hneq]; [left;solve_addr|right;by rewrite Nat.eqb_neq].
           }
           assert ((pc_a,pc_v) ≠ (a0,v0)).
           { intro ; simplify_eq. destruct Heq ; congruence. }
           rewrite Hneq in Hmem, Hdfracs ; simplify_map_eq.
           rewrite !prod_merge_insert prod_merge_empty_l in H3.
           by simplify_map_eq.
       }
       pose proof (mem_implies_loadv _ _ _ _ _ _ _ _ Hmem Hload) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_notinstr Ep r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw'
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
      Instr Executable @ Ep
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

  Lemma wp_load_success_frominstr Ep r1 r2 pc_p pc_b pc_e pc_a pc_v lw lw'' p b e
    v pc_a' dq:
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw''
          ∗ ▷ r2 ↦ᵣ LCap p b e pc_a pc_v }}}
      Instr Executable @ Ep
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

  Lemma wp_load_success_same Ep r1 pc_p pc_b pc_e pc_a pc_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ (if ((a =? pc_a)%Z && (v =? pc_v)) then emp else ▷ (a, v) ↦ₐ{dq'} lw') }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ (if ((a =? pc_a)%Z && (v =? pc_v)) then lw else lw')
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ (if ((a =? pc_a)%Z && (v =? pc_v)) then emp else (a, v) ↦ₐ{dq'} lw') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ la dq lw, la ↦ₐ{dq} lw)%I with "Hi Hr1a") as
        (lmem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); simplify_eq
      ; rewrite prod_merge_insert; by simplify_map_eq.
    }
    { eapply mem_implies_allow_load_map with (pc_a := pc_a) (pca_v := pc_v) (lw := lw) (lw' := lw')
      ; eauto; last by simplify_map_eq.
      cbn.
      destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Heq
      ; simplify_eq
      ; by rewrite !prod_merge_insert prod_merge_empty_l !fmap_insert fmap_empty.
    }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]"; cbn in *.
       { iExists lmem,dfracs; iSplitL; eauto.
         iPureIntro. Unshelve. 3: exact (a0, v0). 2: exact (pc_a, pc_v).
         split ; eauto.
       }
       incrementLPC_inv.
       assert (lmem !! (a0, v0) = Some loadv) as Hload.
       { destruct (decide ((a0 = pc_a) /\ (v0 = pc_v))) as [ [Heq_a Heq_v] |Heq]; subst.
         - assert (((pc_a =? pc_a)%f && (pc_v =? pc_v)) = true) as Heq.
           {
             rewrite andb_true_iff ; split; [solve_addr | by rewrite Nat.eqb_refl].
           }
           rewrite Heq in Hmem, Hfracs ; simplify_map_eq.
           rewrite prod_merge_insert prod_merge_empty_l in H1.
           by simplify_map_eq.
         - rewrite not_and_r in Heq.
           assert (((a0 =? pc_a)%f && (v0 =? pc_v)) = false) as Hneq.
           {
             rewrite andb_false_iff.
             destruct Heq as [Hneq | Hneq]; [left;solve_addr|right;by rewrite Nat.eqb_neq].
           }
           assert ((pc_a,pc_v) ≠ (a0,v0)).
           { intro ; simplify_eq. destruct Heq ; congruence. }
           rewrite Hneq in Hmem, Hfracs ; simplify_map_eq.
           rewrite !prod_merge_insert prod_merge_empty_l in H1.
           by simplify_map_eq.
       }
       pose proof (mem_implies_loadv _ _ _ _ _ _ _ _ Hmem Hload) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  Lemma wp_load_success_same_notinstr Ep r1 pc_p pc_b pc_e pc_a pc_v lw lw' lw'' p b e a v pc_a' dq dq' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ{dq'} lw' }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ (a, v) ↦ₐ{dq'} lw' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct ((a =? pc_a)%Z && (v =? pc_v)) eqn:Ha.
    { assert (a = pc_a)
        as Heqa by (apply andb_true_iff in Ha; destruct Ha as [Ha _]; solve_addr).
      assert (v = pc_v)
        as Heqv by (by apply andb_true_iff in Ha; destruct Ha as [_ Ha]; apply Nat.eqb_eq).
      simplify_eq.
      iDestruct (mapsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
      rewrite Ha. done.
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame. Unshelve. apply (LInt 0). apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr Ep r1 pc_p pc_b pc_e pc_a pc_v lw p b e pc_a' dq :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ LCap p b e pc_a pc_v}}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl Nat.eqb_refl; eauto. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl Nat.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC Ep r2 pc_p pc_b pc_e pc_a pc_v lw
        p b e a v p' b' e' a' v' a'' :
    decodeInstrWL lw = Load PC r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r2 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ LCap p' b' e' a' v' }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap p' b' e' a'' v'
             ∗ (pc_a, pc_v) ↦ₐ lw
             ∗ r2 ↦ᵣ LCap p b e a v
             ∗ (a, v) ↦ₐ LCap p' b' e' a' v' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map
        with (pc_a := pc_a) (pca_v := pc_v) (a := a) (v := v) ; eauto.
      destruct (decide (a = pc_a)) ; simplify_eq ; eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementLPC_inv; simplify_map_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma isCorrectLPC_ra_wb pc_p pc_b pc_e pc_a pc_v :
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a).
  Proof.
    intros Hcorrect.
    inversion Hcorrect ; cbn in *; simplify_eq.
    by apply isCorrectPC_ra_wb.
  Qed.

  Lemma wp_load_success_fromPC Ep r1 pc_p pc_b pc_e pc_a pc_v pc_a' lw lw'' dq :
    decodeInstrWL lw = Load r1 PC →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ{dq} lw
          ∗ ▷ r1 ↦ᵣ lw'' }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ (pc_a, pc_v) ↦ₐ{dq} lw
             ∗ r1 ↦ᵣ lw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' φ)
            "(>HPC & >Hi & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite -memMap_resource_1_dq.
       incrementLPC_inv.
       simplify_map_eq.
       rewrite insert_commute //= insert_insert insert_commute //= insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto.
       apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
       destruct o; apply Is_true_false in H0. all: try congruence. done.
     }
  Qed.

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
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(a =? pc_a)%a && (v =? pc_v) = false⌝)%I as %Hfalse.
    { rewrite andb_false_iff Z.eqb_neq Nat.eqb_neq.
      iDestruct (address_neq with "Hr2a Hi") as %Hneq.
      destruct (decide (v = pc_v)) ; simplify_eq ; eauto.
      iLeft; iIntros (->%finz_to_z_eq); done. }
    iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt Ep r1 pc_p pc_b pc_e pc_a pc_v lw lw' p b e a v pc_a' :
    decodeInstrWL lw = Load r1 r1 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
          ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ ▷ r1 ↦ᵣ LCap p b e a v
          ∗ ▷ (a, v) ↦ₐ lw'}}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
             ∗ r1 ↦ᵣ lw'
             ∗ (pc_a, pc_v) ↦ₐ lw
             ∗ (a, v) ↦ₐ lw' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(a =? pc_a)%a && (v =? pc_v) = false⌝)%I as %Hfalse.
    { rewrite andb_false_iff Z.eqb_neq Nat.eqb_neq.
      iDestruct (address_neq with "Ha Hpc_a") as %Hneq.
      destruct (decide (v = pc_v)) ; simplify_eq ; eauto.
      iLeft; iIntros (->%finz_to_z_eq); done. }
    iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]") ;eauto;rewrite Hfalse;iFrame.
  Qed.

End cap_lang_rules.
