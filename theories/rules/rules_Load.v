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
  Implicit Types w : Word.
  Implicit Types lw : LWord.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition reg_allows_load (lregs : LReg) (r : RegName) p b e a v :=
    lregs !! r = Some (LCap p b e a v) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure (lregs: LReg) (r1 r2: RegName) (lmem : LMem) :=
  | Load_fail_const lw:
      lregs !! r2 = Some lw ->
      is_lcap lw = false →
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

  Definition read_reg_inr (lregs : LReg) (r : RegName) p b e a v :=
    match lregs !! r with
      | Some (LWCap w p' b' e' a' Heq v') => (LWCap w p' b' e' a' Heq v') = LCap p b e a v
      | Some _ => True
      | None => False end.

  Instance reg_allows_load_dec lregs r p b e a v :
    Decision (reg_allows_load lregs r p b e a v).
  Proof.
    rewrite /reg_allows_load.
    apply and_dec; [|apply and_dec]; try solve_decision.
    destruct (lregs !! r); try solve_decision.
    destruct l; last (right; congruence).
    destruct (decide (p0 = p)); [ subst | right; congruence].
    destruct (decide (b0 = b)); [ subst | right; congruence].
    destruct (decide (e0 = e)); [ subst | right; congruence].
    destruct (decide (a0 = a)); [ subst | right; congruence].
    destruct (decide (v0 = v)); [ subst | right; congruence].
    destruct (decide (w = WSealable (SCap p b e a))); [ subst | right; congruence].
    left; f_equal.
    cbn in e1.
    rewrite (_ : e1 = eq_refl); auto.
    (* TODO I should be able to get (e1 : eq_refl )*)
  Admitted.

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

  (* TODO do we need v and pca_v to be different ? *)
  Lemma mem_neq_implies_allow_load_map:
    ∀ (lregs : LReg)(lmem : LMem)(r2 : RegName) (pc_a : Addr)
      (lw lw' : LWord) p b e a v,
      a ≠ pc_a
      → lmem = <[(pc_a, v):= lw]> (<[(a, v) := lw']> ∅)
      → lregs !! r2 = Some (LCap p b e a v)
      → allow_load_map_or_true r2 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a lw lw' p b e a v H4 Hrr2 Hreg2.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hreg2.
    - case_decide; last done.
      exists lw'.
      assert ((pc_a, v) <> (a, v)) by congruence; simplify_map_eq.
      auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (lregs : LReg)(lmem : LMem)(r2 : RegName) (pc_a : Addr)
      (lw lw' : LWord) p b e a v,
      (if (a =? pc_a)%a
       then lmem = <[(pc_a, v):=lw]> ∅
       else lmem = <[(pc_a, v):=lw]> (<[(a, v):=lw']> ∅))
      → lregs !! r2 = Some (LCap p b e a v)
      → allow_load_map_or_true r2 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a lw lw' p b e a v H4 Hrr2.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_load_map; eauto.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map; eauto. congruence.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (lw lw' : LWord) (a : Addr)
      (lmem : LMem) (loadv : LWord) v,
      (if (a =? pc_a)%a
       then lmem = <[(pc_a, v):=lw]> ∅
       else lmem = <[(pc_a, v):=lw]> (<[(a, v):=lw']> ∅))→
      lmem !! (a,v) = Some loadv →
      loadv = (if (a =? pc_a)%a then lw else lw').
  Proof.
    intros pc_a lw lw' a lmem loadv v H4 H6.
    destruct (a =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a. by simplify_map_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq.
  Qed.

  (* a more general version of load to work also with any fraction and persistent points tos *)
  (* Lemma gen_mem_valid_inSepM_general: *)
  (*   ∀ lmem (lm : LMem) (a : Addr) (lw : Word) dq v, *)
  (*     lmem !! (a, v) = Some (dq,lw) → *)
  (*     gen_heap_interp lm *)
  (*                  -∗ ([∗ map] a↦dqw ∈ lmem, mapsto a dqw.1 dqw.2) *)
  (*                  -∗ ⌜lm !! a = Some lw⌝. *)
  (* Proof. *)
  (*   iIntros (mem0 m a w dq Hmem_pc) "Hm Hmem". *)
  (*   iDestruct (big_sepM_delete _ _ a with "Hmem") as "[Hpc_a Hmem]"; eauto. *)
  (*   iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto. *)
  (* Qed. *)

  (* Definition prod_op {A B : Type} := *)
  (*   λ (o1 : option A) (o2 : option B), match o1 with *)
  (*            | Some b => match o2 with *)
  (*                       | Some c => Some (b,c) *)
  (*                       | None => None *)
  (*                       end *)
  (*            | None => None *)
  (*            end. *)

  (* Definition prod_merge {A B C : Type} `{Countable A} : gmap A B → gmap A C → gmap A (B * C) := *)
  (*   λ m1 m2, merge prod_op m1 m2. *)

  (* Instance prod_op_DiagNone {A B : Type} : (DiagNone (@prod_op A B)). *)
  (* Proof. cbv. auto. Qed. *)

  Lemma wp_load_general Ep
     pc_p pc_b pc_e pc_a pc_v
     r1 r2
     lw
     lmem
     lregs :
    decodeInstrWL lw = Load r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Load r1 r2) ⊆ dom lregs →

    lmem !! (pc_a, pc_v) = Some lw →
    allow_load_map_or_true r2 lregs lmem →

    {{{ (▷ [∗ map] a↦lw ∈ lmem, a ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Load_spec lregs r1 r2 lregs' lmem retv⌝ ∗
            ([∗ map] a↦lw ∈ lmem, a ↦ₐ lw) ∗
         [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad φ) "(>Hmem & >Hmap) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem.

    (* Derive necessary register values in r *)
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    feed destruct (Hri r2) as [lr2v [Hlr'2 Hlr2]]. by set_solver+.
    feed destruct (Hri r1) as [lr1v [Hlr'1 _]]. by set_solver+. clear Hri.
    (* Derive the PC in memory *)
    iDestruct (@gen_heap_valid_inSepM with "Hm Hmem") as %Hlpc_a ; eauto.

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
    destruct (is_lcap lr2v) eqn:Hlr2v.
    2:{ (* Failure: r2 is not a capability *)
      assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem ; etable := etable ; enumcur := enumcur |}) as (-> & ->).
      {
        apply is_lcap_is_cap_false_iff in Hlr2v.
        subst lrw2; cbn in *.
        destruct lr2v eqn:Heq; cbn in *
        ; try congruence; destruct_word w ; by simplify_pair_eq.
      }

      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, cur_map; iFrame; auto
        | iApply "Hφ" ; iFrame ; iFailCore Load_fail_const
        ].
    }
    subst lrw2; cbn in *.
    destruct lr2v; cbn in * ; try congruence.
    destruct w as [ | [p' b' e' a' | ] | ] eqn:Heq; cbn in *; try congruence.
    injection e0; intros ; subst.
    rewrite (_ : e0 = eq_refl) in Hlr'2. 2: admit.
    rewrite (_ : e0 = eq_refl) in Hlr2. 2: admit.
    clear e0.

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
    iDestruct (@gen_heap_valid_inSepM with "Hm Hmem") as %Hma' ; eauto.
    assert ( mem !! a = Some (lword_get_word loadv) ) as Hma
        by (eapply state_phys_log_mem_get_word ; eauto).

    rewrite Hma /= in Hstep.
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

    (* TODO we need to destruct r1 = PC *)
    (* Success *)
    destruct (decide (r1 = PC)); subst.
    - (* r1 = PC *) admit.
    - (* r1 <> PC *)
      rewrite /update_reg /= in Hstep.
      eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
          as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->).

      rewrite lookup_insert_ne in HPC''; auto.
      rewrite HPC'' in HPC.
      injection HPC ; intros ; subst. clear H7 H8 H9 H10.

      eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
      2: by apply map_fmap_mono; apply insert_mono ; eauto.
      rewrite ( _ :
                (λ lw : LWord, lword_get_word lw) <$> <[r1:=loadv]> lr = <[r1:= (lword_get_word loadv)]> reg
              ) in HuPC; cycle 1.
      { destruct HLinv as [[Hstrips Hcurreg] _].
        rewrite -Hstrips fmap_insert -/(lreg_strip lr); auto. }

      rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn.
      iMod ((gen_heap_update_inSepM _ _ r1 loadv) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod ((gen_heap_update_inSepM _ _ PC (LCap pc_p pc_b pc_e a_pc1 pc_v)) with "Hr Hmap") as
        "[Hr Hmap]"; eauto.
      { destruct (decide (r1 = PC)) ; simplify_map_eq; auto. }
      iFrame. iModIntro.
      iSplitR "Hφ Hmap Hmem" ; cycle 1.
      + iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto.
        rewrite /reg_allows_load; eauto.
      + iExists _, lm, cur_map; iFrame; auto.
        destruct HLinv as [[Hstrips Hcur_reg] HmemInv]; cbn in *.
        iPureIntro; econstructor; eauto.
        split.
        by rewrite -Hstrips /lreg_strip !fmap_insert /=.
        clear Hlr'1 Hlr'2.
        apply map_Forall_insert_2 ; [ | apply map_Forall_insert_2; cbn ; auto].
        cbn.

        eapply map_Forall_lookup_1 with (i := PC) in Hcur_reg ; eauto.
        rewrite /is_cur_word in Hcur_reg.
        eapply Hcur_reg.
        eapply mem_phys_log_current_word; eauto.
  Admitted.

  (* TODO: move to stdpp_extra *)
  Lemma create_gmap_default_lookup_None {K V : Type} `{Countable K}
      (l : list K) (d : V) (k : K) :
    k ∉ l →
    (create_gmap_default l d) !! k = None.
  Proof.
    intros Hk.
    induction l;auto.
    simpl. apply not_elem_of_cons in Hk as [Hne Hk].
    rewrite lookup_insert_ne//. apply IHl. auto.
  Qed.
  Lemma create_gmap_default_permutation {K V : Type} `{Countable K}
      (l l' : list K) (d : V) :
    l ≡ₚl' →
    (create_gmap_default l d) = (create_gmap_default l' d).
  Proof.
    intros Hperm.
    apply map_eq. intros k.
    destruct (decide (k ∈ l)).
    - assert (k ∈ l') as e';[rewrite -Hperm;auto|].
      apply (create_gmap_default_lookup _ d) in e as ->.
      apply (create_gmap_default_lookup _ d) in e' as ->. auto.
    - assert (k ∉ l') as e';[rewrite -Hperm;auto|].
      apply (create_gmap_default_lookup_None _ d) in n as ->.
      apply (create_gmap_default_lookup_None _ d) in e' as ->. auto.
  Qed.

  Lemma mem_remove_dq mem dq :
    ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ⊣⊢
    ([∗ map] a↦dw ∈ (prod_merge (create_gmap_default (elements (dom mem)) dq) mem), a ↦ₐ{dw.1} dw.2).
  Proof.
    iInduction (mem) as [|a k mem] "IH" using map_ind.
    - rewrite big_sepM_empty dom_empty_L elements_empty
              /= /prod_merge merge_empty big_sepM_empty. done.
    - rewrite dom_insert_L.
      assert (elements ({[a]} ∪ dom mem) ≡ₚ a :: elements (dom mem)) as Hperm.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply (create_gmap_default_permutation _ _ dq) in Hperm. rewrite Hperm /=.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq,k)) //.
      iSplit.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        iApply big_sepM_insert.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a);auto; rewrite H2;auto. }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a);auto; rewrite H2;auto. }
        iApply big_sepM_insert. auto.
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma wp_load Ep
     pc_p pc_b pc_e pc_a
     r1 r2 w mem regs dq :
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of (Load r1 r2) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  Lemma memMap_resource_2gen_clater_dq (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word) (Φ : Addr -> dfrac → Word -> iProp Σ)  :
    (▷ Φ a1 dq1 w1) -∗
    (if (a2 =? a1)%a then emp else ▷ Φ a2 dq2 w2) -∗
    (∃ mem dfracs, ▷ ([∗ map] a↦w ∈ prod_merge dfracs mem, Φ a w.1 w.2) ∗
       ⌜(if  (a2 =? a1)%a
       then mem = (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
       (if  (a2 =? a1)%a
       then dfracs = (<[a1:=dq1]> ∅)
       else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (a2 =? a1)%a eqn:Heq.
    - iExists (<[a1:= w1]> ∅),(<[a1:= dq1]> ∅); iSplitL; auto. iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto. rewrite merge_empty.
      iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[a1:=w1]> (<[a2:=w2]> ∅)),(<[a1:=dq1]> (<[a2:=dq2]> ∅)); iSplitL; auto.
      iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2));auto.
      rewrite merge_empty.
      iApply big_sepM_insert;[|iFrame].
      { apply Z.eqb_neq in Heq. rewrite lookup_insert_ne//. congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_resource_2gen_d_dq (Φ : Addr → dfrac → Word → iProp Σ) (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word)  :
    ( ∃ mem dfracs, ([∗ map] a↦w ∈ prod_merge dfracs mem, Φ a w.1 w.2) ∧
       ⌜ (if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
          else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
       (if  (a2 =? a1)%a
       then dfracs = (<[a1:=dq1]> ∅)
       else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝
    ) -∗ (Φ a1 dq1 w1 ∗ if (a2 =? a1)%a then emp else Φ a2 dq2 w2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem dfracs) "[Hmem [Hif Hif'] ]".
    destruct ((a2 =? a1)%a) eqn:Heq.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto. rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2));auto.
      rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply Z.eqb_neq in Heq. solve_addr. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  Lemma wp_load_success E r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap p b e a
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (eqb_addr a pc_a) then w else w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap p b e a
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H6) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap p b e a
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (a =? pc_a)%Z eqn:Ha.
    { rewrite (_: a = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (mapsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. auto.
      apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. assert (pc_a =? pc_a = true)%Z as ->. apply Z.eqb_refl.
      done. iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ". iFrame. assert (pc_a =? pc_a = true)%Z as ->. apply Z.eqb_refl. iFrame. }
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame. Unshelve. apply DfracDiscarded. apply (WInt 0).
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_b pc_e pc_a w w'' p b e pc_a' dq :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap p b e pc_a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap p b e pc_a }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap p b e a
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (a =? pc_a)%a then w else w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H4) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct (a =? pc_a)%a eqn:Ha.
    { assert (a = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst a.
      iDestruct (mapsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
      rewrite Ha. done.
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame. Unshelve. apply (WInt 0). apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_b pc_e pc_a w p b e pc_a' dq :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap p b e pc_a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_b pc_e pc_a w
        p b e a p' b' e' a' a'' :
    decodeInstrW w = Load PC r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ WCap p' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap p' b' e' a''
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap p b e a
             ∗ a ↦ₐ WCap p' b' e' a' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma memMap_resource_1_dq (a : Addr) (w : Word) dq :
        a ↦ₐ{dq} w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ{dq} w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite big_sepM_empty.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_b pc_e pc_a pc_a' w w'' dq :
    decodeInstrW w = Load r1 PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ w }}}.
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
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite -memMap_resource_1_dq.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_commute //= insert_insert insert_commute //= insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
       destruct o; apply Is_true_false in H3. all: try congruence. done.
     }
  Qed.

End cap_lang_rules.
