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

  Definition reg_allows_store (lregs : LReg) (r : RegName) p b e a v :=
    lregs !! r = Some (LCap p b e a v) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Inductive Store_failure_store (lregs: LReg) (r1 : RegName)(r2 : Z + RegName) (lmem : LMem):=
  | Store_fail_const lw:
      lregs !! r1 = Some lw ->
      lword_get_cap lw = None →
      Store_failure_store lregs r1 r2 lmem
  | Store_fail_bounds p b e a v:
      lregs !! r1 = Some(LCap p b e a v) ->
      (writeAllowed p = false ∨ withinBounds b e a = false) →
      Store_failure_store lregs r1 r2 lmem
  | Store_fail_invalid_PC:
      incrementLPC (lregs) = None ->
      Store_failure_store lregs r1 r2 lmem
  .

  Inductive Store_spec
    (lregs: LReg) (r1 : RegName) (r2 : Z + RegName)
    (lregs': LReg) (lmem lmem' : LMem) : cap_lang.val → Prop
    :=
  | Store_spec_success p b e a v storev oldv :
    word_of_argumentL lregs r2 = Some storev ->
    reg_allows_store lregs r1 p b e a v →
    lmem !! (a, v) = Some oldv →
    lmem' = (<[(a, v) := storev]> lmem) →
    incrementLPC(lregs) = Some lregs' ->
    Store_spec lregs r1 r2 lregs' lmem lmem' NextIV
  | Store_spec_failure_store :
    lmem' = lmem →
    Store_failure_store lregs r1 r2 lmem ->
    Store_spec lregs r1 r2 lregs' lmem lmem' FailedV.

  Definition allow_store_map_or_true (r1 : RegName) (lregs : LReg) (lmem : LMem):=
    ∃ p b e a v,
      read_reg_inr lregs r1 p b e a v ∧
      if decide (reg_allows_store lregs r1 p b e a v) then
        ∃ lw, lmem !! (a, v) = Some lw
      else True.

  Lemma allow_store_implies_storev:
    ∀ (r1 : RegName) (r2 : Z + RegName) (lmem : LMem) (lregs : LReg)
      (p : Perm) (b e a : Addr) v storev,
      allow_store_map_or_true r1 lregs lmem
      → lregs !! r1 = Some (LCap p b e a v)
      → word_of_argumentL lregs r2 = Some storev
      → writeAllowed p = true
      → withinBounds b e a = true
      → ∃ (storev : LWord),
          lmem !! (a, v) = Some storev.
  Proof.
    intros r1 r2 lmem lregs p b e a v storev HaStore Hr2v Hwoa Hwa Hwb.
    unfold allow_store_map_or_true, read_reg_inr in HaStore.
    destruct HaStore as (?&?&?&?&?& Hrinr & Hwo).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hra.
    - exact Hwo.
    - contradiction Hra; done.
  Qed.

  Lemma mem_eq_implies_allow_store_map:
    ∀ (lregs : LReg) (lmem : LMem)(r1 : RegName) (lw : LWord) p b e a v,
      lmem = <[(a, v):= lw]> ∅
      → lregs !! r1 = Some (LCap p b e a v)
      → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros lregs lmem r1 lw p b e a v Hmem Hrr2.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      exists lw. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_store_map:
    ∀ (lregs : LReg) (lmem : LMem) (r1 : RegName) (pc_a : Addr) (pc_v : Version)
      (lw lw' : LWord) p b e a v,
      (a ≠ pc_a \/ v <> pc_v)
      → lmem = <[(pc_a, pc_v):= lw]> (<[(a, v) := lw']> ∅)
      → lregs !! r1 = Some (LCap p b e a v)
      → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros lregs lmem r1 pc_a pc_v lw lw' p b e a v H4 Hrr2 Hreg1.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hreg1.
    - case_decide; last done.
      exists lw'.
      destruct H4; assert ((pc_a, pc_v) <> (a, v)) by congruence; simplify_map_eq; auto.
  Qed.

  Lemma mem_implies_allow_store_map:
    ∀ (lregs : LReg) (lmem : LMem) (r1 : RegName) (pc_a : Addr) (pc_v : Version)
      (lw lw' : LWord) p b e a v,
      (if ((a,v) =? (pc_a, pc_v))%la
       then lmem = <[(pc_a, pc_v):=lw]> ∅
       else lmem = <[(pc_a, pc_v):=lw]> (<[(a, v):=lw']> ∅))
      → lregs !! r1 = Some (LCap p b e a v)
      → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a pc_v lw lw' p b e a v H4 Hrr2.
    destruct ((a,v) =? (pc_a, pc_v))%la eqn:Heq; cbn in Heq.
      + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2].
        apply Z.eqb_eq, finz_to_z_eq in Heq1. subst a.
        apply Nat.eqb_eq in Heq2. subst v.
        eapply mem_eq_implies_allow_store_map; eauto.
      + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq]
      ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ]
      ; eapply (mem_neq_implies_allow_store_map _ _ _ pc_a pc_v _ _ _ _ _ a v) ; eauto.
        left ; solve_addr.
  Qed.

  Lemma nwanwb_implies_allow_store_map r1 lregs lmem p b e a v :
      lregs !! r1 = Some (LCap p b e a v)
    → writeAllowed p = false ∨ withinBounds b e a = false
    → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros Hr1 Hnw. exists p, b, e, a, v. split.
    rewrite /read_reg_inr Hr1 //.
    destruct decide as [(_ & ? & ?)|]; [|easy].
    intuition congruence.
  Qed.

  Definition exec_optL_Store
    (lregs : LReg) (lmem : LMem)
    (dst : RegName) (ρ : Z + RegName) : option LReg :=
    tostore          ← word_of_argumentL lregs ρ;
    lwdst            ← lregs !! dst ;
    '(p, b, e, a, v) ← lword_get_cap lwdst;
    if writeAllowed p && withinBounds b e a then
      lregs' ← incrementLPC lregs ; Some lregs'
    else None.

  Lemma wp_store Ep
    pc_p pc_b pc_e pc_a pc_v
    r1 (r2 : Z + RegName) lw lmem lregs :
    decodeInstrWL lw = Store r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Store r1 r2) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allow_store_map_or_true r1 lregs lmem →

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ Store_spec lregs r1 r2 lregs' lmem lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hregs) Hφ".
    (*  extract the pc  *)
    rewrite (big_sepM_delete). 2: apply Hmem_pc. iDestruct "Hmem" as "[Hpc_a Hmem]".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hregs $Hpc_a Hmem Hφ]").
    iModIntro.
    iIntros (σ) "(Hσ & Hregs & Hpca)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Store lregs lmem r1 r2 ) (φ2 := _)).

    iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
    iDestruct (state_interp_transient_intro_nodfracs (lm := lmem) with "[$Hregs $Hσ Hmem Hpca]") as "Hσ".
    { iCombine "Hpca Hmem" as "Hmem".
      rewrite -(big_sepM_insert (fun x y => mapsto x (DfracOwn (pos_to_Qp 1)) y)).
      rewrite insert_delete. iFrame. auto. by rewrite lookup_delete. }
    iApply (wp2_word_of_argument (lrt := lregs) (lw := lw) with "[Hφ Hcred $Hσ]"). { set_solver. }

    iIntros (r2v) "Hσ %Hlr2v %Hr2v".
    iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver.
    iIntros (r1v) "Hσ %Hlr1v %Hr1v".

    iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
    iApply wp2_word_get_cap. iSplit.

    { (* failure case: r1v contains something, but it is not a capability. *)
      iIntros "%Hcr1v %Hgcr1v".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap.
      iApply ("Hφ" with "[$Hregs $Hmem]"). iPureIntro.
      constructor 2 with (lmem' := lmem); try easy. now constructor 1 with (lw := r1v). }

    iIntros (p b e a v) "%Heqlwr1v %Heqgwr1v".

    destruct r1v; try destruct sb; unfold reg_allows_store;
    auto; inversion Heqlwr1v; inversion Heqgwr1v; subst.
    destruct (writeAllowed p && withinBounds b e a)  eqn:?; cbn. all: revgoals.
    { (* failure case: no valid capability for writing to memory *)
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      iModIntro. rewrite big_sepM_fmap. iApply ("Hφ" with "[$Hregs $Hmem]").
      iPureIntro. constructor 2 with (lmem' := lmem); try easy.
      constructor 2 with (p := p) (b := b) (e := e) (a := a) (v := v); auto.
      by rewrite andb_false_iff in Heqb0. }

    (* valid capability for writing to memory *)

    destruct HaStore as [p' [b' [e' [a' [v' [Hreadreg Hlmem]]]]]].
    rewrite decide_True in Hlmem. destruct Hlmem as [oldlw Hlmem].
    2: { unfold read_reg_inr in *. rewrite Hlr1v in Hreadreg.
         rewrite andb_true_iff in Heqb0. destruct Heqb0 as [Hwrite Hinbounds].
         inversion Hreadreg; subst. unfold reg_allows_store; auto. }
    rewrite updatePC_incrementPC. cbn.

    iApply wp_opt2_bind. iApply wp_opt2_eqn_both.
    unfold read_reg_inr in *. rewrite Hlr1v in Hreadreg.
    inversion Heqlwr1v; inversion Hreadreg; subst.

    (* update the transient logical memory to have a' point to the value in r2 *)
    rewrite (update_state_interp_transient_from_mem_mod (a', v') r2v _).
    2: { intros cur_map Hcurr. apply (word_of_argumentL_cur Hlr2v Hcurr). }
    2: { intros cur_map Hcurr. apply Is_true_true_2 in Heqb0. rewrite andb_True in Heqb0. destruct Heqb0. apply (@cap_of_argumentL_cur lregs r1 p' b' e'); eauto. }
    2: {  rewrite lookup_fmap. unfold LMem, LAddr in *. rewrite option_fmap_compose.
          destruct (lmem !! (a', v')); cbn; by inversion Hlmem. }

    iApply (wp2_opt_incrementPC with "[$Hσ Hφ]"). { now rewrite elem_of_dom. }
    iSplit.
    { (* failure case: incrementing the pc failed *)
      iIntros "Hσ %Hlincr %Hincr".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap.
      iApply ("Hφ" with "[$Hregs $Hmem]").
      iPureIntro. constructor 2; auto.
      now constructor 3. }

    (* pc incr success *)
    iIntros (lregs' regs') "Hσ %Hlincr Hincr".
    iApply wp2_val. cbn.
    iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
    rewrite -fmap_insert big_sepM_fmap; cbn.
    iApply ("Hφ" with "[$Hmem $Hregs]").
    iPureIntro.

    apply (Store_spec_success _ _ _ _ _ _ p' b' e' a' v' r2v oldlw); auto.
    unfold reg_allows_store.
    rewrite andb_true_iff in Heqb0; destruct Heqb0 as [Hwrite Hinbounds].
    auto.
  Qed.

  Lemma isCorrectLPC_ra_wb pc_p pc_b pc_e pc_a pc_v :
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a).
  Proof.
    intros HVlpc. inversion HVlpc as [lpc p b e a Hlpc HVpc] ; cbn in * ; simplify_eq.
    by apply isCorrectPC_ra_wb.
  Qed.

  Lemma wp_store_success_z_PC E pc_p pc_b pc_e pc_a pc_v pc_a' lw z :
     decodeInstrWL lw = Store PC (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ (LInt z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       apply isCorrectLPC_ra_wb in Hvpc.
       apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o; last apply Is_true_false in H. all:try congruence.
       done.
     }
  Qed.

   Lemma wp_store_success_reg_PC E src lwsrc pc_p pc_b pc_e pc_a pc_v pc_a' lw :
     decodeInstrWL lw = Store PC (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lwsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lwsrc
              ∗ src ↦ᵣ lwsrc }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi & >Hsrc) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H0. congruence. done. congruence.
     }
    Qed.

   Lemma wp_store_success_reg_PC_same E pc_p pc_b pc_e pc_a pc_v pc_a' lw lw' :
     decodeInstrWL lw = Store PC (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
           ∗ (pc_a, pc_v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. }
      { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H. congruence. done. congruence.
     }
    Qed.

   Lemma wp_store_success_same E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst z lw'
         p b e :
     decodeInstrWL lw = Store dst (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a pc_v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ (LInt z)
              ∗ dst ↦ᵣ LCap p b e pc_a pc_v }}}.
    Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence.
     }
     Qed.

   Lemma wp_store_success_reg' E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst lw'
         p b e a v :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ if ((a,v) =? (pc_a, pc_v))%la
             then emp
             else ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ
                  (if ((a,v) =? (pc_a, pc_v))%la
                  then (LCap pc_p pc_b pc_e pc_a pc_v)
                  else lw)
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ if ((a,v) =? (pc_a, pc_v))%la
                then emp
                else (a,v) ↦ₐ (LCap pc_p pc_b pc_e pc_a pc_v) }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst & Ha) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ la w, la ↦ₐ w)%I  with "Hi Ha") as (mem) "[>Hmem %]".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct ((a =? pc_a)%Z && (v =? pc_v)); by simplify_map_eq. }
    { eapply mem_implies_allow_store_map; eauto. all: by simplify_map_eq. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       destruct ((a0 =? pc_a)%Z && (v0 =? pc_v)) eqn:Heq; subst mem.
       - rewrite andb_true_iff in Heq.
         destruct Heq as [Heq_a Heq_v].
         apply Z.eqb_eq, finz_to_z_eq in Heq_a.
         apply Nat.eqb_eq in Heq_v.
         simplify_eq.
         rewrite insert_insert.
         rewrite memMap_resource_1.
         incrementLPC_inv.
         simplify_map_eq. rewrite insert_insert.
         iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame.
       - assert ((pc_a, pc_v) ≠ (a0, v0)).
         {
           intro. simplify_eq.
           by rewrite Z.eqb_refl Nat.eqb_refl andb_diag in Heq.
         }
         rewrite insert_commute; last congruence. rewrite insert_insert.
         iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Hpc_a]" ; first congruence.
         incrementLPC_inv.
         rewrite lookup_insert_ne in H3; last congruence. simplify_map_eq. rewrite insert_insert.
         iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg_frominstr_same E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst lw'
         p b e :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a pc_v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v
              ∗ dst ↦ᵣ LCap p b e pc_a pc_v }}}.
   Proof.
     intros. iIntros "(HPC & Hpc_a & Hdst) Hφ".
     iApply (wp_store_success_reg' with "[$HPC $Hpc_a $Hdst]"); eauto.
     { cbn. rewrite Z.eqb_refl Nat.eqb_refl. eauto. }
     iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl Nat.eqb_refl andb_diag.
     iApply "Hφ". iFrame. Unshelve. eauto.
   Qed.

   Lemma wp_store_success_reg_frominstr E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst lw'
         p b e a :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a pc_v
           ∗ ▷ (a,pc_v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a pc_v
              ∗ (a, pc_v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v }}}.
   Proof.
     intros. iIntros "(>HPC & >Hpc_a & >Hdst & >Ha) Hφ".
     destruct (a =? pc_a)%a eqn:Ha.
     { rewrite (_: a = pc_a); cycle 1.
       apply Z.eqb_eq in Ha; solve_addr.
       by iDestruct (addr_dupl_false with "Ha Hpc_a") as "?". }
     iApply (wp_store_success_reg' with "[$HPC $Hpc_a $Hdst Ha]"); eauto.
     rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
     iApply "Hφ". iFrame.
  Qed.

   Lemma wp_store_success_reg_same' E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst
         p b e :
     decodeInstrWL lw = Store dst (inr dst) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a pc_v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ LCap p b e pc_a pc_v
              ∗ dst ↦ᵣ LCap p b e pc_a pc_v }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg_same_a E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst src
         p b e a lw'' :
      decodeInstrWL lw = Store dst (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lw''
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a pc_v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw''
              ∗ src ↦ᵣ lw''
              ∗ dst ↦ᵣ LCap p b e pc_a pc_v}}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementLPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst src lw'
         p b e a v lw'' :
      decodeInstrWL lw = Store dst (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lw''
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ src ↦ᵣ lw''
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ lw'' }}}.
    Proof.
      iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a) (v := v)
                                                  (pc_a := pc_a) (pc_v := pc_v)
      ; eauto.
      rewrite pair_eq in H2. apply not_and_l in H2. destruct H2 ; [left|right]; done.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementLPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

   Lemma wp_store_success_reg_same E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst lw'
         p b e a v:
     decodeInstrWL lw = Store dst (inr dst) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ LCap p b e a v }}}.
   Proof.
    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a) (v := v)
                                                  (pc_a := pc_a) (pc_v := pc_v)
      ; eauto.
      rewrite pair_eq in H0. apply not_and_l in H0. destruct H0 ; [left|right]; done.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementLPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

   Lemma wp_store_success_z E pc_p pc_b pc_e pc_a pc_v pc_a' lw dst z lw'
         p b e a v :
     decodeInstrWL lw = Store dst (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pc_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pc_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ LInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a) (v := v)
                                                  (pc_a := pc_a) (pc_v := pc_v)
      ; eauto.
      rewrite pair_eq in H0. apply not_and_l in H0. destruct H0 ; [left|right]; done.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iApply "Hφ".
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementLPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementLPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

  Lemma wp_store_fail_reg Ep dst src pc_p pc_b pc_e pc_a pc_v lw p b e a v lw' :
    decodeInstrWL lw = Store dst (inr src) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (writeAllowed p = false ∨ withinBounds b e a = false) →
    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
      ∗ ▷ (pc_a, pc_v) ↦ₐ lw
      ∗ ▷ dst ↦ᵣ LCap p b e a v
      ∗ ▷ src ↦ᵣ lw'
    }}}
      Instr Executable @ Ep
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hnwawb φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "(Hmap & %Hpcdst & %Hpcsrc & %Hdstsrc)".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { set_solver. }
    { eapply nwanwb_implies_allow_store_map; by simplify_map_eq. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
    { (* Success (contradiction) *)
      exfalso. destruct H0 as (Hdst & Hwa & Hwb). simplify_map_eq.
      apply lookup_insert_Some in H1.
      destruct H1 as [[]|[]]; simplify_eq.
      intuition congruence.
    }
    { (* Failure  *)
      by iApply "Hφ".
    }
  Qed.

  Lemma wp_store_fail_z Ep dst pc_p pc_b pc_e pc_a pc_v lw p b e a v z :
    decodeInstrWL lw = Store dst (inl z) →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (writeAllowed p = false ∨ withinBounds b e a = false) →
    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
      ∗ ▷ (pc_a, pc_v) ↦ₐ lw
      ∗ ▷ dst ↦ᵣ LCap p b e a v
    }}}
      Instr Executable @ Ep
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hnwawb φ) "(>HPC & >Hi & >Hdst) Hφ".

    iDestruct (map_of_regs_2 with "HPC Hdst") as "(Hmap & %Hpcdst)".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { set_solver. }
    { eapply nwanwb_implies_allow_store_map; by simplify_map_eq. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
    { (* Success (contradiction) *)
      exfalso. destruct H0 as (Hdst & Hwa & Hwb). simplify_map_eq.
      apply lookup_insert_Some in H1.
      destruct H1 as [[]|[]]; simplify_eq.
      intuition congruence.
    }
    { (* Failure  *)
      by iApply "Hφ".
    }
  Qed.

 End cap_lang_rules.
