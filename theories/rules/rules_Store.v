From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, @regG Σ CP}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr. 
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val. 
  Implicit Types w : Word.
  Implicit Types reg : gmap (CoreN * RegName) Word.
  Implicit Types ms : gmap Addr Word.

  Definition reg_allows_store (i: CoreN) (regs : Reg) (r : RegName) p b e a :=
    regs !! (i, r) = Some (WCap p b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Inductive Store_failure_store (i: CoreN) (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (mem : gmap Addr Word):=
  | Store_fail_const z:
      regs !! (i, r1) = Some(WInt z) ->
      Store_failure_store i regs r1 r2 mem
  | Store_fail_bounds p b e a:
      regs !! (i, r1) = Some(WCap p b e a) ->
      (writeAllowed p = false ∨ withinBounds b e a = false) →
      Store_failure_store i regs r1 r2 mem
  | Store_fail_invalid_PC:
      incrementPC (regs) i = None ->
      Store_failure_store i regs r1 r2 mem
  .

  Inductive Store_failure_incr (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (mem : gmap Addr Word):=
  .

  Inductive Store_spec
    (i : CoreN)
    (regs: Reg) (r1 : RegName) (r2 : Z + RegName)
    (regs': Reg) (mem mem' : gmap Addr Word) : cap_lang.val → Prop
  :=
  | Store_spec_success p b e a storev oldv :
      word_of_argument regs i r2 = Some storev ->
      reg_allows_store i regs r1 p b e a  →
      mem !! a = Some oldv →
      mem' = (<[a := storev]> mem) →
      incrementPC(regs) i = Some regs' ->
      Store_spec i regs r1 r2 regs' mem mem' (i, NextIV)
  | Store_spec_failure_store :
      mem' = mem →
      Store_failure_store i regs r1 r2 mem ->
      Store_spec i regs r1 r2 regs' mem mem' (i, FailedV).

  Definition allow_store_map_or_true (i: CoreN) (r1 : RegName) (regs : Reg) (mem : gmap Addr Word):=
    ∃ p b e a,
      read_reg_inr regs i r1 p b e a ∧
      if decide (reg_allows_store i regs r1 p b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_store_implies_storev:
    ∀ (i: CoreN) (r1 : RegName)(r2 : Z + RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm) (b e a : Addr) storev,
      allow_store_map_or_true i r1 r mem0
      → r !! (i, r1) = Some (WCap p b e a)
      → word_of_argument r i r2 = Some storev
      → writeAllowed p = true
      → withinBounds b e a = true
      → ∃ (storev : Word),
          mem0 !! a = Some storev.
  Proof.
    intros i r1 r2 mem0 r p b e a storev HaStore Hr2v Hwoa Hwa Hwb.
    unfold allow_store_map_or_true in HaStore.
    destruct HaStore as (?&?&?&?&[Hrr | Hrl]&Hwo).
    - assert (Hrr' := Hrr).
      rewrite Hrr in Hr2v; inversion Hr2v; subst.
      case_decide as HAL.
      * auto.
      * unfold reg_allows_store in HAL.
        destruct HAL. inversion Hwoa. auto. 
    - destruct Hrl as [z Hrl].  by congruence.
  Qed.

  Lemma mem_eq_implies_allow_store_map:
    ∀ (i: CoreN)(regs : Reg)(mem : gmap Addr Word)(r1 : RegName)(w : Word) p b e a,
      mem = <[a:=w]> ∅
      → regs !! (i, r1) = Some (WCap p b e a)
      → allow_store_map_or_true i r1 regs mem.
  Proof.
    intros i regs mem r1 w p b e a Hmem Hrr2.
    exists p,b,e,a; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_store_map:
    ∀ (i: CoreN)(regs : Reg)(mem : gmap Addr Word)(r1 : RegName)(pc_a : Addr)
      (w w' : Word) p b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → regs !! (i, r1) = Some (WCap p b e a)
      → allow_store_map_or_true i r1 regs mem.
  Proof.
    intros i regs mem r1 pc_a w w' p b e a H4 Hrr2.
    exists p,b,e,a; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_store_map:
    ∀ (i: CoreN)(regs : Reg)(mem : gmap Addr Word)(r1 : RegName)(pc_a : Addr)
      (w w' : Word) p b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → regs !! (i, r1) = Some (WCap p b e a)
      → allow_store_map_or_true i r1 regs mem.
  Proof.
    intros i regs mem r1 pc_a w w' p b e a H4 Hrr2.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_store_map; eauto.
      + apply Z.eqb_neq in Heq.  eapply mem_neq_implies_allow_store_map; eauto. congruence.
  Qed.

   Lemma wp_store Ep i
     pc_p pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
   decodeInstrW w = Store r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of_core (Store r1 r2) i ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true i r1 regs mem →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     (i, Instr Executable) @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ Store_spec i regs r1 r2 regs' mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri i r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     iDestruct (gen_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iIntros "_".
     iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.

     unfold exec in Hstep. simpl in Hstep.
     rewrite Hr1 in Hstep.

     (* Now we start splitting on the different cases in the Store spec, and prove them one at a time *)

     destruct (word_of_argument regs i r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri i r2) as [r0v [Hr0 _] ]. rewrite /regs_of_core; by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     apply (word_of_arg_mono _ r) in HSV as HSV'; auto. rewrite HSV' in Hstep. cbn in Hstep.

     destruct r1v as  [| p b e a ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       inversion Hstep.
       cbn; iFrame; iApply "Hφ"; iFrame.
       iPureIntro. econstructor; eauto. econstructor; eauto. 
     }

     destruct (writeAllowed p && withinBounds b e a) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev i r1 r2 mem regs p b e a storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (gen_mem_valid_inSepM mem m a oldv with "Hm Hmem" ) as %Hma' ; auto.

      destruct (incrementPC regs i) as [ regs' |] eqn:Hregs'.
      2: { (* Failure: the PC could not be incremented correctly *)
        assert (incrementPC r i = None).
        { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
        rewrite incrementPC_fail_updatePC /= in Hstep; auto.
        inversion Hstep.
        cbn; iFrame; iApply "Hφ"; iFrame.
        iPureIntro. eapply Store_spec_failure_store;eauto. by constructor.
      }

      iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]" ; eauto.

     (* Success *)
      rewrite /update_mem /= in Hstep.
      Unshelve.
      eapply (incrementPC_success_updatePC _ i (<[a:=storev]> m) ) in Hregs'
        as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & HuPC & ->).
      eapply (updatePC_success_incl i _ (<[a:=storev]> m)) in HuPC. 2: by eauto.

      rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.

      iFrame.
      iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iModIntro. iApply "Hφ". iFrame.
      iPureIntro. eapply Store_spec_success; eauto.
        * split; auto. exact Hr'1. all: auto.
        * unfold incrementPC. rewrite a_pc1 HPC''.
      Unshelve. all: auto.
   Qed.

  Lemma wp_store_success_z_PC E i pc_p pc_b pc_e pc_a pc_a' w z :
     decodeInstrW w = Store PC (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; simplify_map_eq by simplify_pair_eq
      ; eauto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H3; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false_2 in H2. all:try congruence. done.
     }
   Qed.

   Lemma wp_store_success_reg_PC E i src wsrc pc_p pc_b pc_e pc_a pc_a' w :
     decodeInstrW w = Store PC (inr src) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, src) ↦ᵣ wsrc }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wsrc
              ∗ (i, src) ↦ᵣ wsrc }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi & >Hsrc) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H4; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false_2 in H3. congruence. done. congruence.
     }
    Qed.

   Lemma wp_store_success_reg_PC_same E i pc_p pc_b pc_e pc_a pc_a' w w' :
     decodeInstrW w = Store PC (inr PC) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ WCap pc_p pc_b pc_e pc_a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. }
      { (* Failure (contradiction) *)
       destruct H3; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false_2 in H2. congruence. done. congruence.
     }
    Qed.

   Lemma wp_store_success_same E i pc_p pc_b pc_e pc_a pc_a' w dst z w'
         p b e :
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e pc_a }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (WInt z)
              ∗ (i, dst) ↦ᵣ WCap p b e pc_a }}}.
    Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H4; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: congruence.
     }
     Qed.

   Lemma wp_store_success_reg' E i pc_p pc_b pc_e pc_a pc_a' w dst w'
         p b e a :
      decodeInstrW w = Store dst (inr PC) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e a
           ∗ if (a =? pc_a)%a
             then emp
             else ▷ a ↦ₐ w' }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ (if (a =? pc_a)%a
                         then (WCap pc_p pc_b pc_e pc_a)
                         else w)
              ∗ (i, dst) ↦ᵣ WCap p b e a
              ∗ if (a =? pc_a)%a
                then emp
                else a ↦ₐ (WCap pc_p pc_b pc_e pc_a) }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst & Ha) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↦ₐ w)%I  with "Hi Ha") as (mem) "[>Hmem %]".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq by simplify_pair_eq. }
    { eapply mem_implies_allow_store_map; eauto. all: by simplify_map_eq by simplify_pair_eq. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       destruct (a0 =? pc_a)%a eqn:Heq; subst mem.
       -  apply Z.eqb_eq, finz_to_z_eq in Heq. subst a0.
          rewrite insert_insert.
          rewrite memMap_resource_1.
          incrementPC_inv.
          simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
          iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame.

       - apply Z.eqb_neq in Heq.
         rewrite insert_commute; last congruence. rewrite insert_insert.
         iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Hpc_a]"; first congruence.
         incrementPC_inv.
         rewrite lookup_insert_ne in H6; last congruence. simplify_map_eq by simplify_pair_eq. rewrite insert_insert.
         iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame.
     }
     { (* Failure (contradiction) *)
       destruct H5; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg_frominstr_same E i pc_p pc_b pc_e pc_a pc_a' w dst w'
         p b e :
      decodeInstrW w = Store dst (inr PC) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e pc_a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e pc_a }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ WCap pc_p pc_b pc_e pc_a
              ∗ (i, dst) ↦ᵣ WCap p b e pc_a }}}.
   Proof.
     intros. iIntros "(HPC & Hpc_a & Hdst) Hφ".
     iApply (wp_store_success_reg' with "[$HPC $Hpc_a $Hdst]"); eauto.
     { rewrite Z.eqb_refl. eauto. }
     iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
     iApply "Hφ". iFrame. Unshelve. eauto.
   Qed.

   Lemma wp_store_success_reg_frominstr E i pc_p pc_b pc_e pc_a pc_a' w dst w'
         p b e a :
      decodeInstrW w = Store dst (inr PC) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true →
     withinBounds b e a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e a
           ∗ ▷ a ↦ₐ w' }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, dst) ↦ᵣ WCap p b e a
              ∗ a ↦ₐ WCap pc_p pc_b pc_e pc_a }}}.
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

   Lemma wp_store_success_reg_same' E i pc_p pc_b pc_e pc_a pc_a' w dst
         p b e :
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e pc_a }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ WCap p b e pc_a
              ∗ (i, dst) ↦ᵣ WCap p b e pc_a }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of /regs_of_argument.
      rewrite set_map_union_L set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H4; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg_same_a E i pc_p pc_b pc_e pc_a pc_a' w dst src
         p b e w'' :
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, src) ↦ᵣ w''
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e pc_a }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w''
              ∗ (i, src) ↦ᵣ w''
              ∗ (i, dst) ↦ᵣ WCap p b e pc_a}}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H6 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H6; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
   Qed.

   Lemma wp_store_success_reg E i pc_p pc_b pc_e pc_a pc_a' w dst src w'
         p b e a w'' :
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, src) ↦ᵣ w''
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e a
           ∗ ▷ a ↦ₐ w' }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, src) ↦ᵣ w''
              ∗ (i, dst) ↦ᵣ WCap p b e a
              ∗ a ↦ₐ w'' }}}.
    Proof.
      iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H7 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H7; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

   Lemma wp_store_success_reg_same E i pc_p pc_b pc_e pc_a pc_a' w dst w'
         p b e a :
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e a
           ∗ ▷ a ↦ₐ w' }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, dst) ↦ᵣ WCap p b e a
              ∗ a ↦ₐ WCap p b e a }}}.
   Proof.
    iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite !dom_insert /regs_of_core /regs_of /regs_of_argument
      ; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H5; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

   Lemma wp_store_success_z E i pc_p pc_b pc_e pc_a pc_a' w dst z w'
         p b e a :
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →

     {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i, dst) ↦ᵣ WCap p b e a
           ∗ ▷ a ↦ₐ w' }}}
       (i, Instr Executable) @ E

       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ w
              ∗ (i, dst) ↦ᵣ WCap p b e a
              ∗ a ↦ₐ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hwa Hwb φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _  i pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec. 
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct H5; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: try congruence.
     }
    Qed.

 End cap_lang_rules.
