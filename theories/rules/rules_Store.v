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

  Definition reg_allows_store (lregs : LReg) (r : RegName) p b e a v :=
    lregs !! r = Some (LCap p b e a v) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Inductive Store_failure_store (lregs: LReg) (r1 : RegName)(r2 : Z + RegName) (lmem : LMem):=
  | Store_fail_const lw:
      lregs !! r1 = Some lw ->
      is_log_cap lw = false →
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
    lword_of_argument lregs r2 = Some storev ->
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
      → lword_of_argument lregs r2 = Some storev
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
    ∀ (lregs : LReg) (lmem : LMem) (r1 : RegName) (pc_a : Addr) (pca_v : Version)
      (lw lw' : LWord) p b e a v,
      (a ≠ pc_a \/ v <> pca_v)
      → lmem = <[(pc_a, pca_v):= lw]> (<[(a, v) := lw']> ∅)
      → lregs !! r1 = Some (LCap p b e a v)
      → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros lregs lmem r1 pc_a pca_v lw lw' p b e a v H4 Hrr2 Hreg1.
    exists p,b,e,a,v; split.
    - unfold read_reg_inr. by rewrite Hreg1.
    - case_decide; last done.
      exists lw'.
      destruct H4; assert ((pc_a, pca_v) <> (a, v)) by congruence; simplify_map_eq; auto.
  Qed.

  Lemma mem_implies_allow_store_map:
    ∀ (lregs : LReg) (lmem : LMem) (r1 : RegName) (pc_a : Addr) (pca_v : Version)
      (lw lw' : LWord) p b e a v,
      (if ((a,v) =? (pc_a, pca_v))%la
       then lmem = <[(pc_a, pca_v):=lw]> ∅
       else lmem = <[(pc_a, pca_v):=lw]> (<[(a, v):=lw']> ∅))
      → lregs !! r1 = Some (LCap p b e a v)
      → allow_store_map_or_true r1 lregs lmem.
  Proof.
    intros lregs lmem r2 pc_a pca_v lw lw' p b e a v H4 Hrr2.
    destruct ((a,v) =? (pc_a, pca_v))%la eqn:Heq; cbn in Heq.
      + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2].
        apply Z.eqb_eq, finz_to_z_eq in Heq1. subst a.
        apply Nat.eqb_eq in Heq2. subst v.
        eapply mem_eq_implies_allow_store_map; eauto.
      + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq]
      ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ]
      ; eapply (mem_neq_implies_allow_store_map _ _ _ pc_a pca_v _ _ _ _ _ a v) ; eauto.
        left ; solve_addr.
  Qed.

  Lemma wp_store Ep
    pc_p pc_b pc_e pc_a pc_v pca_v
    r1 (r2 : Z + RegName) lw lmem lregs :
    decodeInstrWL lw = Store r1 r2 →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Store r1 r2) ⊆ dom lregs →
    lmem !! (pc_a, pca_v) = Some lw →
    allow_store_map_or_true r1 lregs lmem →

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ Store_spec lregs r1 r2 lregs' lmem lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
    (* iApply wp_lift_atomic_head_step_no_fork; auto. *)
    (* iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl. *)
    (* iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs. *)

    (*  (* Derive necessary register values in r *) *)
    (*  pose proof (lookup_weaken _ _ _ _ HPC Hregs). *)
    (*  specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri. *)
    (*  odestruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+. *)
    (*  iDestruct (gen_mem_valid_inSepM mem mem0 with "Hm Hmem") as %Hma; eauto. *)

    (*  iModIntro. *)
    (*  iSplitR. by iPureIntro; apply normal_always_head_reducible. *)
    (*  iNext. iIntros (e2 σ2 efs Hpstep). *)
    (*  apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)). *)
    (*  iIntros "_". *)
    (*  iSplitR; auto. eapply step_exec_inv in Hstep; eauto. *)

    (*  rewrite /exec /= Hr1 /= in Hstep. *)

    (*  (* Now we start splitting on the different cases in the Store spec, and prove them one at a time *) *)

    (*  destruct (word_of_argument regs r2) as [ storev | ] eqn:HSV. *)
    (*  2: { *)
    (*    destruct r2 as [z | r2]. *)
    (*    - cbn in HSV; inversion HSV. *)
    (*    - destruct (Hri r2) as [r0v [Hr0 _] ]. by set_solver+. *)
    (*      cbn in HSV. rewrite Hr0 in HSV. inversion HSV. *)
    (*  } *)
    (*  apply (word_of_arg_mono _ reg) in HSV as HSV'; auto. rewrite HSV' in Hstep. cbn in Hstep. *)

    (*  destruct (is_cap r1v) eqn:Hr1v. *)
    (*  2: { (* Failure: r1 is not a capability *) *)
    (*    assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem0 ; etable := etable ; enumcur := enumcur |}) as (-> & ->). *)
    (*    { *)
    (*      unfold is_cap in Hr1v. *)
    (*      destruct_word r1v; by simplify_pair_eq. *)
    (*    } *)
    (*    iFailWP "Hφ" Store_fail_const. *)
    (*  } *)
    (*  destruct r1v as [ | [p b e a | ] | ]; try inversion Hr1v. clear Hr1v. *)

    (*  destruct (writeAllowed p && withinBounds b e a) eqn:HWA. *)
    (*  2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *) *)
    (*    inversion Hstep. *)
    (*    apply andb_false_iff in HWA. *)
    (*    iFailWP "Hφ" Store_fail_bounds. *)
    (*  } *)
    (*  apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb). *)

    (*  (* Prove that a is in the memory map now, otherwise we cannot continue *) *)
    (*  pose proof (allow_store_implies_storev r1 r2 mem regs p b e a storev) as (oldv & Hmema); auto. *)

    (*  (* Given this, prove that a is also present in the memory itself *) *)
    (*  iDestruct (gen_mem_valid_inSepM mem mem0 a oldv with "Hm Hmem" ) as %Hma' ; auto. *)

    (*   destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'. *)
    (*   2: { (* Failure: the PC could not be incremented correctly *) *)
    (*     assert (incrementPC reg = None). *)
    (*     { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. } *)
    (*     rewrite incrementPC_fail_updatePC /= in Hstep; auto. *)
    (*     inversion Hstep. *)
    (*     cbn; iFrame; iApply "Hφ"; iFrame. *)
    (*     iPureIntro. eapply Store_spec_failure_store;eauto. by constructor. *)
    (*   } *)

    (*   iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]"; eauto. *)

    (*  (* Success *) *)
    (*   rewrite /update_mem /= in Hstep. *)
    (*   eapply (incrementPC_success_updatePC _ (<[a:=storev]> mem0)) in Hregs' *)
    (*     as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & HuPC & ->). *)
    (*   eapply (updatePC_success_incl _ (<[a:=storev]> mem0)) in HuPC. 2: by eauto. *)
    (*   rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn. *)

    (*   iFrame. *)
    (*   iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
    (*   iFrame. iModIntro. iApply "Hφ". iFrame. *)
    (*   iPureIntro. eapply Store_spec_success; eauto. *)
    (*     * split; auto. exact Hr'1. all: auto. *)
    (*     * unfold incrementPC. rewrite a_pc1 HPC''.  *)
    (*   Unshelve. all: auto. *)
   (* Qed. *)
  Admitted.

  Lemma wp_store_success_z_PC E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw z :
     decodeInstrWL lw = Store PC (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ (LInt z) }}}.
  Proof.
  (*   iIntros (Hinstr Hvpc Hpca' Hwa φ) *)
  (*           "(>HPC & >Hi) Hφ". *)
  (*   iDestruct (map_of_regs_1 with "HPC") as "Hmap". *)
  (*   iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H3 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite !insert_insert. *)
  (*      iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb]. *)
  (*      destruct o; last apply Is_true_false in H2. all:try congruence. done. *)
  (*    } *)
  (*  Qed. *)
  Admitted.

   Lemma wp_store_success_reg_PC E src lwsrc pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw :
     decodeInstrWL lw = Store PC (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lwsrc }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lwsrc
              ∗ src ↦ᵣ lwsrc }}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa φ) *)
  (*           "(>HPC & >Hi & >Hsrc) Hφ". *)
  (*    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]". *)
  (*    iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H4 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      do 2 rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb]. *)
  (*      destruct o; last apply Is_true_false in H3. congruence. done. congruence. *)
  (*    } *)
  (*   Qed. *)
  Admitted.

   Lemma wp_store_success_reg_PC_same E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw lw' :
     decodeInstrWL lw = Store PC (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v }}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa φ) *)
  (*           "(>HPC & >Hi) Hφ". *)
  (*    iDestruct (map_of_regs_1 with "HPC") as "Hmap". *)
  (*    iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H3 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      do 2 rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. } *)
  (*     { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      apply isCorrectLPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb]. *)
  (*      destruct o; last apply Is_true_false in H2. congruence. done. congruence. *)
  (*    } *)
  (*   Qed. *)
  Admitted.

   Lemma wp_store_success_same E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst z lw'
         p b e v :
     decodeInstrWL lw = Store dst (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ (LInt z)
              ∗ dst ↦ᵣ LCap p b e pc_a v }}}.
    Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*           "(>HPC & >Hi & >Hdst) Hφ". *)
  (*    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
  (*    iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H4 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      do 2 rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: congruence. *)
  (*    } *)
  (*    Qed. *)
  Admitted.

   Lemma wp_store_success_reg' E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw'
         p b e a v :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ if ((a,v) =? (pc_a, pca_v))%la
             then emp
             else ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ (if (a =? pc_a)%a
                         then (LCap pc_p pc_b pc_e pc_a pc_v)
                         else lw)
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ if ((a,v) =? (pc_a, pca_v))%la
                then emp
                else (a,v) ↦ₐ (LCap pc_p pc_b pc_e pc_a pc_v) }}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*           "(>HPC & >Hi & >Hdst & Ha) Hφ". *)
  (*    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
  (*    iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↦ₐ w)%I  with "Hi Ha") as (mem) "[>Hmem %]". *)

  (*   iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { destruct (a =? pc_a)%a; by simplify_map_eq. } *)
  (*   { eapply mem_implies_allow_store_map; eauto. all: by simplify_map_eq. } *)

  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H5 as [Hrr2 _]. simplify_map_eq. *)
  (*      destruct (a0 =? pc_a)%a eqn:Heq; subst mem. *)
  (*      -  apply Z.eqb_eq, finz_to_z_eq in Heq. subst a0. *)
  (*         rewrite insert_insert. *)
  (*         rewrite memMap_resource_1. *)
  (*         incrementPC_inv. *)
  (*         simplify_map_eq. rewrite insert_insert. *)
  (*         iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. *)

  (*      - apply Z.eqb_neq in Heq. *)
  (*        rewrite insert_commute; last congruence. rewrite insert_insert. *)
  (*        iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Hpc_a]"; first congruence. *)
  (*        incrementPC_inv. *)
  (*        rewrite lookup_insert_ne in H6; last congruence. simplify_map_eq. rewrite insert_insert. *)
  (*        iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. *)
  (*    } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*  Qed. *)
  Admitted.

   Lemma wp_store_success_reg_frominstr_same E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw'
         p b e v :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v
              ∗ dst ↦ᵣ LCap p b e pc_a v }}}.
   Proof.
  (*    intros. iIntros "(HPC & Hpc_a & Hdst) Hφ". *)
  (*    iApply (wp_store_success_reg' with "[$HPC $Hpc_a $Hdst]"); eauto. *)
  (*    { rewrite Z.eqb_refl. eauto. } *)
  (*    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl. *)
  (*    iApply "Hφ". iFrame. Unshelve. eauto. *)
  (*  Qed. *)
  Admitted.

   Lemma wp_store_success_reg_frominstr E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw'
         p b e a v :
      decodeInstrWL lw = Store dst (inr PC) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a, v) ↦ₐ LCap pc_p pc_b pc_e pc_a pc_v }}}.
   Proof.
  (*    intros. iIntros "(>HPC & >Hpc_a & >Hdst & >Ha) Hφ". *)
  (*    destruct (a =? pc_a)%a eqn:Ha. *)
  (*    { rewrite (_: a = pc_a); cycle 1. *)
  (*      apply Z.eqb_eq in Ha; solve_addr. *)
  (*      by iDestruct (addr_dupl_false with "Ha Hpc_a") as "?". } *)
  (*    iApply (wp_store_success_reg' with "[$HPC $Hpc_a $Hdst Ha]"); eauto. *)
  (*    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ?)". rewrite Ha. *)
  (*    iApply "Hφ". iFrame. *)
  (* Qed. *)
  Admitted.

   Lemma wp_store_success_reg_same' E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst
         p b e v :
     decodeInstrWL lw = Store dst (inr dst) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ LCap p b e pc_a v
              ∗ dst ↦ᵣ LCap p b e pc_a v }}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*           "(>HPC & >Hi & >Hdst) Hφ". *)
  (*    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
  (*    iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H4 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      do 2 rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*  Qed. *)
  Admitted.

   Lemma wp_store_success_reg_same_a E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst src
         p b e a v lw'' :
      decodeInstrWL lw = Store dst (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lw''
           ∗ ▷ dst ↦ᵣ LCap p b e pc_a v }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw''
              ∗ src ↦ᵣ lw''
              ∗ dst ↦ᵣ LCap p b e pc_a v}}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*            "(>HPC & >Hi & >Hsrc & >Hdst) Hφ". *)
  (*    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]". *)
  (*    iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_eq_implies_allow_store_map; eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H6 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite memMap_resource_1. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      do 2 rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*  Qed. *)
  Admitted.

   Lemma wp_store_success_reg E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst src lw'
         p b e a v lw'' :
      decodeInstrWL lw = Store dst (inr src) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ src ↦ᵣ lw''
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ src ↦ᵣ lw''
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ lw'' }}}.
    Proof.
  (*     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*            "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]". *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto. *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_store_map with (a := a); eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H7 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite insert_commute // insert_insert. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*   Qed. *)
  Admitted.

   Lemma wp_store_success_reg_same E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst lw'
         p b e a v:
     decodeInstrWL lw = Store dst (inr dst) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ LCap p b e a v }}}.
   Proof.
  (*   iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*            "(>HPC & >Hi & >Hdst & >Hsrca) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto. *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_store_map with (a := a); eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H5 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite insert_commute // insert_insert. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*   Qed. *)
  Admitted.

   Lemma wp_store_success_z E pc_p pc_b pc_e pc_a pc_v pca_v pc_a' lw dst z lw'
         p b e a v :
     decodeInstrWL lw = Store dst (inl z) →
     isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
           ∗ ▷ (pc_a, pca_v) ↦ₐ lw
           ∗ ▷ dst ↦ᵣ LCap p b e a v
           ∗ ▷ (a,v) ↦ₐ lw' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
              ∗ (pc_a, pca_v) ↦ₐ lw
              ∗ dst ↦ᵣ LCap p b e a v
              ∗ (a,v) ↦ₐ LInt z }}}.
   Proof.
  (*    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ) *)
  (*            "(>HPC & >Hi & >Hdst & >Hsrca) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto. *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_store_map with (a := a); eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec.  *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H5 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite insert_commute // insert_insert. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct X; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*    } *)
  (*   Qed. *)
  Admitted.

 End cap_lang_rules.
