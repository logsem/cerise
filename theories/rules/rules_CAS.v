From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
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

  Inductive Cas_failure_spec (i: CoreN) (regs: Reg)
    (loc cond newvalue: RegName)
    (mem : gmap Addr Word):=
  | Cas_fail_const z:
      regs !! (i, loc) = Some(WInt z) ->
      Cas_failure_spec i regs loc cond newvalue mem
  | Cas_fail_bounds p b e a:
      regs !! (i, loc) = Some(WCap p b e a) ->
      (writeAllowed p = false ∨ withinBounds b e a = false) →
      Cas_failure_spec i regs loc cond newvalue mem
  | Cas_fail_invalid_PC oldv:
      incrementPC (<[ (i, cond) := oldv ]> regs) i = None ->
      Cas_failure_spec i regs loc cond newvalue mem
  .

  Inductive Cas_spec (i: CoreN) (regs regs': Reg)
    (loc cond newvalue: RegName)
    (mem mem' : gmap Addr Word)
    : cap_lang.val → Prop :=
  | Cas_spec_failure:
      regs = regs' ->
      mem = mem' ->
      Cas_failure_spec i regs loc cond newvalue mem  ->
      Cas_spec i regs regs' loc cond newvalue mem mem' (i, FailedV)
  | Cas_spec_success_eq p b e a (oldv newv : Word) :
      reg_allows_store i regs loc p b e a  →
      mem !! a = Some oldv →
      regs !! (i, cond) = Some oldv ->
      regs !! (i, newvalue) = Some newv ->
      mem' = (<[a := newv]> mem) →
      incrementPC (<[ (i, cond) := oldv ]> regs) i = Some regs' ->
      Cas_spec i regs regs' loc cond newvalue mem mem' (i, NextIV)
  | Cas_spec_success_neq p b e a (c oldv newv : Word) :
      reg_allows_store i regs loc p b e a  →
      oldv ≠ c ->
      mem !! a = Some oldv →
      mem = mem' ->
      regs !! (i, cond) = Some c ->
      regs !! (i, newvalue) = Some newv ->
      incrementPC (<[ (i, cond) := oldv ]> regs) i = Some regs' ->
      Cas_spec i regs regs' loc cond newvalue mem mem' (i, NextIV)
.

  Definition allow_store_map_or_true (i: CoreN) (r1 : RegName) (regs : Reg) (mem : gmap Addr Word):=
    ∃ p b e a,
      read_reg_inr regs i r1 p b e a ∧
      if decide (reg_allows_store i regs r1 p b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_store_implies_storev:
    ∀ (i: CoreN) (r1 : RegName)(r2 : RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm) (b e a : Addr) storev,
      allow_store_map_or_true i r1 r mem0
      → r !! (i, r1) = Some (WCap p b e a)
      → r !! (i, r2) = Some storev
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


  Lemma wp_Cas Ep i
     pc_p pc_b pc_e pc_a
     (loc cond newvalue : RegName)
     w mem regs :
   decodeInstrW w = CAS loc cond newvalue →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of_core (CAS loc cond newvalue) i ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true i loc regs mem → (* ???? *)

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     (i, Instr Executable) @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ Cas_spec i regs regs' loc cond newvalue mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 n) "[Hr Hm] /=". destruct σ1; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri i loc) as [locv [Hloc' Hloc]]. by set_solver+.
     iDestruct (gen_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep). iIntros "_".
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.

     unfold exec in Hstep. simpl in Hstep.
     rewrite Hloc in Hstep.


     (* Now we start splitting on the different cases in the Cas spec, and prove them one at a time *)

     destruct locv as  [| p b e a ] eqn:Hlocv.
     { (* Failure: loc is not a capability *)
       inversion Hstep as [Hs].
       destruct (r !! (i, cond)), (r !! (i, newvalue)) ; cbn in Hs
       ; simplify_eq.
       all: cbn ; iFrame ; iApply "Hφ"; iFrame.
       all: iPureIntro; econstructor; eauto; econstructor; eauto.
     }

     destruct (writeAllowed p && withinBounds b e a) eqn:HWA.
     2 : { (* Failure: loc is either not within bounds or doesnt allow reading *)
       apply andb_false_iff in HWA.
       inversion Hstep as [Hs].
       assert (HWA_neq: writeAllowed p && withinBounds b e a = false)
         by (destruct HWA as [-> | ->]
             ; [ apply andb_false_l | apply andb_false_r]
             ; done).
       rewrite HWA_neq in Hs ; clear HWA_neq.
       destruct (r !! (i, cond)), (r !! (i, newvalue)), (m !! a)
       ; cbn in Hs ; simplify_eq.
       all: iFailWP "Hφ" Cas_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).
     cbn in Hstep.

     destruct (regs !! (i, cond)) as [c'|] eqn:HCV ; cbn in Hstep.
     2: { destruct (Hri i cond) as [ ? [ Hrcond _ ] ].
          rewrite /regs_of_core ; by set_solver +.
          rewrite Hrcond in HCV ; inversion HCV.
     }
     apply (lookup_weaken regs r) in HCV as HCV' ; auto.
     rewrite HCV' in Hstep ; cbn in Hstep.

     destruct (regs !! (i, newvalue)) as [nv|] eqn:HNV ; cbn in Hstep.
     2: { destruct (Hri i newvalue) as [ ? [ Hrnv _ ] ].
          rewrite /regs_of_core ; by set_solver +.
          rewrite Hrnv in HNV ; inversion HNV.
     }
     apply (lookup_weaken regs r) in HNV as HNV' ; auto.
     rewrite HNV' in Hstep ; cbn in Hstep.

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev i loc newvalue mem regs p b e a nv)
       as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (gen_mem_valid_inSepM mem m a oldv with "Hm Hmem" ) as %Hma' ; auto.
     rewrite Hma' in Hstep ; cbn in Hstep.
     assert (Hwa_eq : writeAllowed p && withinBounds b e a = true)
       by (apply andb_true_iff ; auto).
     rewrite Hwa_eq in Hstep ; clear Hwa_eq.
     destruct (decide (oldv = c')).
     - (* oldv = c', the memory is modified *)
       destruct (incrementPC (<[ (i, cond) := oldv ]> regs) i) as [ regs' |] eqn:Hregs'.
      2: { (* Failure: the PC could not be incremented correctly *)
        assert ((incrementPC (<[ (i, cond) := oldv ]> r) i) = None).
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
        by apply (@lookup_insert_is_Some'
                    (prod (@CoreN CP) RegName) _ _ _ _ _ _ _ _ _ finmap_reg)
        ; eauto.
        by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto
            ; apply finmap_reg). }
        rewrite incrementPC_fail_updatePC /= in Hstep; auto.
        simplify_eq.
        iFailWP "Hφ" Cas_fail_invalid_PC.
      }
      simplify_eq.

      iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]" ; eauto.

     (* Success *)
      rewrite /update_mem /update_reg /= in Hstep.
      Unshelve.
      eapply (incrementPC_success_updatePC _ i (<[a:=nv]> m) ) in Hregs'
        as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & HuPC & ->).
      eapply (updatePC_success_incl i _ (<[a:=nv]> m)) in HuPC.
      2: by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto
            ; apply finmap_reg).
      rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
      iFrame.
      iMod ((gen_heap_update_inSepM _ _ (i, cond)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iModIntro. iApply "Hφ". iFrame.
      iPureIntro. eapply Cas_spec_success_eq; eauto.
        * split; auto. eassumption. all: auto.
        * unfold incrementPC. by rewrite a_pc1 HPC''.

     - (* oldv =! c', the memory is not modified *)
     destruct (incrementPC (<[ (i, cond) := oldv ]> regs) i) as [ regs' |] eqn:Hregs'.
      2: { (* Failure: the PC could not be incremented correctly *)
        assert ((incrementPC (<[ (i, cond) := oldv ]> r) i) = None).
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
        by apply (@lookup_insert_is_Some'
                    (prod (@CoreN CP) RegName) _ _ _ _ _ _ _ _ _ finmap_reg)
        ; eauto.
        by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto
            ; apply finmap_reg). }
        rewrite incrementPC_fail_updatePC /= in Hstep; auto.
        simplify_eq.
        iFailWP "Hφ" Cas_fail_invalid_PC.
      }

     (* Success *)
      rewrite /update_mem /update_reg /= in Hstep.
      Unshelve.
      eapply (incrementPC_success_updatePC _ i m) in Hregs'
        as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & HuPC & ->).
      eapply (updatePC_success_incl i _ m) in HuPC.
      2: by (eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto
            ; apply finmap_reg).
      rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
      iFrame.
      iMod ((gen_heap_update_inSepM _ _ (i, cond)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iModIntro. iApply "Hφ". iFrame.
      iPureIntro. eapply Cas_spec_success_neq; eauto.
        * split; auto. eassumption. all: auto.
        * unfold incrementPC. by rewrite a_pc1 HPC''.
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



  Lemma wp_cas_success_eq_PC
    E i r2 r3
    pc_b pc_e pc_a pc_a'
    instr newv v
    :
    decodeInstrW instr = CAS PC r2 r3 →
    isCorrectPC (WCap RWX pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →


    {{{ ▷ (i, PC) ↦ᵣ WCap RWX pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ instr
        ∗ ▷ (i, r2) ↦ᵣ instr
        ∗ ▷ (i, r3) ↦ᵣ newv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap RWX pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ newv
          ∗ (i, r2) ↦ᵣ instr
          ∗ (i, r3) ↦ᵣ newv }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & Hr2 & Hr3) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hr3") as ">[Hmap Hregs]".
    iDestruct "Hregs" as "[% [% %]]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".

    iApply (wp_Cas with "[$Hmap $Hmem]"); eauto
    ; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of.
      rewrite !set_map_union_L !set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all : by simplify_map_eq by simplify_pair_eq. }
    iModIntro.
    iIntros (regs' mem' retv) "[#Hspec [Hmem Hregs]]".
    iDestruct "Hspec" as %Hspec.

    inversion Hspec ; subst.
    - (* Failure *)
      destruct H10; try incrementPC_inv; simplify_map_eq by simplify_pair_eq
      ; eauto.
      inversion H3 ; subst.
      destruct o. destruct H13 ; subst ; cbn in *.
      all: try congruence.
      rewrite /withinBounds in H8; solve_addr.
    - (* Success with equality *)
      iApply "Hφ".
      (* destruct H4 as [Hrr2 _]. *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      destruct ( decide (x2 = a) ) ; subst ; simplify_map_eq.
      rewrite (insert_commute _ (i, PC) (i, r2)) ; simplify_pair_eq.
      rewrite insert_insert insert_insert.
      rewrite (insert_commute _ (i, r2) (i, PC)) ; simplify_pair_eq.
      rewrite insert_insert.
      iFrame.
      iDestruct (regs_of_map_3 with "[$Hregs]") as "(HPC & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_1.
      iFrame.
    - (* Success with non-equality *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      destruct ( decide (x2 = a) ) ; subst ; simplify_map_eq.
  Qed.


  Lemma wp_cas_success_neq_PC
    E i r2 r3
    pc_b pc_e pc_a pc_a'
    instr cond newv v
    :
    decodeInstrW instr = CAS PC r2 r3 →
    isCorrectPC (WCap RWX pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    cond ≠ instr ->

    {{{ ▷ (i, PC) ↦ᵣ WCap RWX pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ instr
        ∗ ▷ (i, r2) ↦ᵣ cond
        ∗ ▷ (i, r3) ↦ᵣ newv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap RWX pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ instr
          ∗ (i, r2) ↦ᵣ instr
          ∗ (i, r3) ↦ᵣ newv }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & Hr2 & Hr3) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hr3") as ">[Hmap Hregs]".
    iDestruct "Hregs" as "[% [% %]]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".

    iApply (wp_Cas with "[$Hmap $Hmem]"); eauto
    ; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of.
      rewrite !set_map_union_L !set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all : by simplify_map_eq by simplify_pair_eq. }
    iModIntro.
    iIntros (regs' mem' retv) "[#Hspec [Hmem Hregs]]".
    iDestruct "Hspec" as %Hspec.

    inversion Hspec ; subst.
    - (* Failure *)
      destruct H11; try incrementPC_inv; simplify_map_eq by simplify_pair_eq
      ; eauto.
      inversion H3 ; subst.
      destruct o. destruct H11 ; subst ; cbn in *.
      all: try congruence.
      rewrite /withinBounds in H9; solve_addr.
    - (* Success with equality *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      destruct ( decide (x2 = a) ) ; subst ; simplify_map_eq.
    - (* Success with non-equality *)
      iApply "Hφ".
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      destruct ( decide (x2 = a) ) ; subst ; simplify_map_eq.
      rewrite (insert_commute _ (i, PC) (i, r2)) ; simplify_pair_eq.
      rewrite insert_insert.
      rewrite (insert_commute _ (i, r2) (i, PC)) ; simplify_pair_eq.
      rewrite insert_insert.
      inversion H9 as [? [ contra _]].
      match goal with
      | h: context[ ?m !! ?r = Some _ ] |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq : m !! r = Some ( WCap RWX x0 x1 a ))
            by (simplify_map_eq by simplify_pair_eq ; reflexivity)
          ; rewrite h in Heq ; simplify_eq
      end.
      iDestruct (regs_of_map_3 with "[$Hregs]") as "(HPC & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_1.
      iFrame.
  Qed.

  Lemma wp_cas_fail_PC
    E i r2 r3
    pc_b pc_e pc_a pc_a'
    instr cond newv v
    :
    decodeInstrW instr = CAS PC r2 r3 →
    isCorrectPC (WCap RX pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →


    {{{ ▷ (i, PC) ↦ᵣ WCap RX pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ instr
        ∗ ▷ (i, r2) ↦ᵣ cond
        ∗ ▷ (i, r3) ↦ᵣ newv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, FailedV);
          (i, PC) ↦ᵣ WCap RX pc_b pc_e pc_a
          ∗ pc_a ↦ₐ instr
          ∗ (i, r2) ↦ᵣ cond
          ∗ (i, r3) ↦ᵣ newv }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & Hr2 & Hr3) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hr3") as ">[Hmap Hregs]".
    iDestruct "Hregs" as "[% [% %]]".
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".

    iApply (wp_Cas with "[$Hmap $Hmem]"); eauto
    ; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of.
      rewrite !set_map_union_L !set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all : by simplify_map_eq by simplify_pair_eq. }
    iModIntro.
    iIntros (regs' mem' retv) "[#Hspec [Hmem Hregs]]".
    iDestruct "Hspec" as %Hspec.

    inversion Hspec ; subst.
    - (* Failure *)
      destruct H10; try incrementPC_inv; simplify_map_eq by simplify_pair_eq
      ; eauto ; try congruence.
      destruct o.
      2: { inversion H3 ; subst.
           rewrite /withinBounds in H8 ; solve_addr. }
      iApply "Hφ".
      iDestruct (regs_of_map_3 with "[$Hregs]") as "(HPC & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_1.
      iFrame.
    - (* Success with equality - contradiction *)
      clear -H8.
      inversion H8 as [? [ contra _]].
      match goal with
      | h: context[ ?x = Some _ ] |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq : x = Some ( WCap RX pc_b pc_e pc_a ))
            by (simplify_map_eq by simplify_pair_eq ; reflexivity)
          ; rewrite h in Heq ; simplify_eq
      end.
    - (* Success with non-equality - contradiction *)
      clear -H8.
      inversion H8 as [? [ contra _]].
      match goal with
      | h: context[ ?x = Some _ ] |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq : x = Some ( WCap RX pc_b pc_e pc_a ))
            by (simplify_map_eq by simplify_pair_eq ; reflexivity)
          ; rewrite h in Heq ; simplify_eq
      end.
  Qed.


  Lemma wp_cas_success_eq
    E i r1 r2 r3
    pc_p pc_b pc_e pc_a pc_a'
    instr p b e a oldv newv
    :
   decodeInstrW instr = CAS r1 r2 r3 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   (pc_a + 1)%a = Some pc_a' →
   writeAllowed p = true → withinBounds b e a = true →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ instr
        ∗ ▷ (i, r1) ↦ᵣ (WCap p b e a)
        ∗ ▷ a ↦ₐ oldv
        ∗ ▷ (i, r2) ↦ᵣ oldv
        ∗ ▷ (i, r3) ↦ᵣ newv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ instr
        ∗ (i, r1) ↦ᵣ (WCap p b e a)
        ∗ a ↦ₐ newv
        ∗ (i, r2) ↦ᵣ oldv
        ∗ (i, r3) ↦ᵣ newv }}}.
   Proof.
     intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hloc & >Hr2 & >Hr3) Hφ".
     iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap Hregs]".
     iDestruct "Hregs" as "[% [% [% [% [% %]]]]]".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Hloc") as "[Hmem %]"; auto.

    iApply (wp_Cas with "[$Hmap $Hmem]"); eauto
    ; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of.
      rewrite !set_map_union_L !set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all : by simplify_map_eq by simplify_pair_eq. }
    iModIntro.
    iIntros (regs' mem' retv) "[#Hspec [Hmem Hregs]]".
    iDestruct "Hspec" as %Hspec.
    inversion Hspec as [ _ _ Hfail | | ] ; subst.
    - (* Failure - contradiction *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: congruence.
    - (* Success with equality *)
      iApply "Hφ".
      (* destruct H4 as [Hrr2 _]. *)
      incrementPC_inv.
      inversion H14 ; subst ; simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r2)) ; simplify_pair_eq.
      rewrite insert_insert.
      rewrite (insert_commute _ (i, r2) (i, PC)) ; simplify_pair_eq.
      rewrite (insert_commute _ (i, r2) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert.
      rewrite (insert_commute _ x2 a0) ; simplify_pair_eq ; last eassumption.
      rewrite insert_insert.
      iDestruct (regs_of_map_4 with "[$Hregs]") as "(HPC & Hr1 & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_2ne ;
        last (apply not_eq_sym ; eassumption).
      iDestruct "Hmem" as "[? ?]".
      iFrame.
    - (* Success with non-equality - contradiction *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      rewrite (insert_commute _ (i, PC) (i, r2)) ; simplify_pair_eq.
      rewrite insert_insert.
      rewrite (insert_commute _ (i, r2) (i, PC)) ; simplify_pair_eq.
      rewrite (insert_commute _ (i, r2) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert.

      iDestruct (regs_of_map_4 with "[$Hregs]") as "(HPC & Hr1 & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_2ne ; last eassumption.
      iDestruct "Hmem" as "[Hx2 Ha]".
      rename x into pc_p
      ; rename x0 into pc_b
      ; rename x1 into pc_e
      ; rename x2 into pc_a.
      inversion H14 ; subst ; simplify_map_eq by simplify_pair_eq.
   Qed.

  Lemma wp_cas_success_neq
    E i r1 r2 r3
    pc_p pc_b pc_e pc_a pc_a'
    instr p b e a oldv cond newv
    :
   decodeInstrW instr = CAS r1 r2 r3 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   oldv ≠ cond ->
   (pc_a + 1)%a = Some pc_a' →
   writeAllowed p = true → withinBounds b e a = true →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ instr
        ∗ ▷ (i, r1) ↦ᵣ (WCap p b e a)
        ∗ ▷ a ↦ₐ oldv
        ∗ ▷ (i, r2) ↦ᵣ cond
        ∗ ▷ (i, r3) ↦ᵣ newv }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ instr
        ∗ (i, r1) ↦ᵣ (WCap p b e a)
        ∗ a ↦ₐ oldv
        ∗ (i, r2) ↦ᵣ oldv
        ∗ (i, r3) ↦ᵣ newv }}}.
   Proof.
     intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hloc & >Hr2 & >Hr3) Hφ".
     iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap Hregs]".
     iDestruct "Hregs" as "[% [% [% [% [% %]]]]]".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Hloc") as "[Hmem %]"; auto.

    iApply (wp_Cas with "[$Hmap $Hmem]"); eauto
    ; simplify_map_eq by simplify_pair_eq; eauto.
    { rewrite /regs_of_core /regs_of.
      rewrite !set_map_union_L !set_map_singleton_L dom_insert_L.
      set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all : by simplify_map_eq by simplify_pair_eq. }
    iModIntro.
    iIntros (regs' mem' retv) "[#Hspec [Hmem Hregs]]".
    iDestruct "Hspec" as %Hspec.
    inversion Hspec as [ _ _ Hfail | | ] ; subst.
    - (* Failure - contradiction *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: congruence.
    - (* Success with equality *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      rename x into pc_p
      ; rename x0 into pc_b
      ; rename x1 into pc_e
      ; rename x2 into pc_a.
      inversion H15 ; subst ; simplify_map_eq by simplify_pair_eq.
    - (* Success with non-equality - contradiction *)
      incrementPC_inv.
      simplify_map_eq by simplify_pair_eq.
      rename x into pc_p
      ; rename x0 into pc_b
      ; rename x1 into pc_e
      ; rename x2 into pc_a.
      inversion H15 ; subst ; simplify_map_eq by simplify_pair_eq.

      rewrite (insert_commute _ (i, PC) (i, r2)) ; simplify_pair_eq.
      rewrite insert_insert.
      rewrite (insert_commute _ (i, r2) (i, PC)) ; simplify_pair_eq.
      rewrite (insert_commute _ (i, r2) (i, r1)) ; simplify_pair_eq.
      rewrite insert_insert.

      iApply "Hφ".
      iDestruct (regs_of_map_4 with "[$Hregs]") as "(HPC & Hr1 & Hr2 & Hr3)"
      ; eauto.
      rewrite memMap_resource_2ne ; last eassumption.
      iDestruct "Hmem" as "[? ?]".
      iFrame.
   Qed.

End cap_lang_rules.
