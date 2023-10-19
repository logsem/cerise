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
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition reg_allows_load (regs : Reg) (r : RegName) p b e a  :=
    regs !! r = Some (WCap p b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure (regs: Reg) (r1 r2: RegName) (mem : gmap Addr Word) :=
  | Load_fail_const w:
      regs !! r2 = Some w ->
      is_cap w = false →
      Load_failure regs r1 r2 mem
  | Load_fail_bounds p b e a:
      regs !! r2 = Some (WCap p b e a) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p b e a loadv:
      regs !! r2 = Some (WCap p b e a) ->
      mem !! a = Some loadv →
      incrementPC (<[ r1 := loadv ]> regs) = None ->
      Load_failure regs r1 r2 mem
  .

  Inductive Load_spec
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (mem : gmap Addr Word) : cap_lang.val → Prop
  :=
  | Load_spec_success p b e a loadv :
    reg_allows_load regs r2 p b e a →
    mem !! a = Some loadv →
    incrementPC
      (<[ r1 := loadv ]> regs) = Some regs' ->
    Load_spec regs r1 r2 regs' mem NextIV

  | Load_spec_failure :
    Load_failure regs r1 r2 mem ->
    Load_spec regs r1 r2 regs' mem FailedV.

  Definition allow_load_map_or_true r (regs : Reg) (mem : gmap Addr Word):=
    ∃ p b e a, read_reg_inr regs r p b e a ∧
      if decide (reg_allows_load regs r p b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm) (b e a : Addr),
      allow_load_map_or_true r2 r mem0
      → r !! r2 = Some (WCap p b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : Word),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p b e a HaLoad Hr2v Hra Hwb.
    unfold allow_load_map_or_true, read_reg_inr in HaLoad.
    destruct HaLoad as (?&?&?&?& Hrinr & Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - exact Hmem.
    - contradiction Hrega. done.
  Qed.

  Lemma mem_eq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p b e a,
      mem = <[a:=w]> ∅
      → regs !! r2 = Some (WCap p b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 w p b e a Hmem Hrr2.
    exists p,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → regs !! r2 = Some (WCap p b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p b e a H4 Hrr2 Hreg2.
    exists p,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hreg2.
    - case_decide; last done.
      exists w'. simplify_map_eq. auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → regs !! r2 = Some (WCap p b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p b e a H4 Hrr2.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_load_map; eauto.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map; eauto. congruence.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : Word) (a0 : Addr)
      (mem0 : gmap Addr Word) (loadv : Word),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:=w]> ∅
       else mem0 = <[pc_a:=w]> (<[a0:=w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by simplify_map_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of (Load r1 r2) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 Hr2]]. by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]. by set_solver+. clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! pc_a)) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq,w)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) mem0 with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    rewrite /exec /= Hr2 /= in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (is_cap r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a capability *)
       assert (c = Failed ∧ σ2 = {| reg := reg ; mem := mem0 ; etable := etable ; enumcur := enumcur |}) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v ; by simplify_pair_eq.
       }
        iFailWP "Hφ" Load_fail_const.
     }
     destruct r2v as [ | [p b e a | ] | ]; try inversion Hr2v. clear Hr2v.

    destruct (readAllowed p && withinBounds b e a) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_fail_bounds.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    pose proof (allow_load_implies_loadv r2 mem regs p b e a) as (loadv & Hmema); auto.

    assert (is_Some (dfracs !! a)) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! a = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) mem0 a loadv with "Hm Hmem" ) as %Hma' ; eauto.

    rewrite Hma' /= in Hstep.
    destruct (incrementPC (<[ r1 := loadv ]> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ r1 := loadv]> reg) = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          by rewrite lookup_insert_is_Some'; eauto.
            by apply insert_mono; eauto. }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" Load_fail_invalid_PC.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ mem0) in Hregs'
      as (p1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_spec_success; auto.
    * split; eauto.
    * exact Hmema.
    * unfold incrementPC. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
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

  Lemma wp_load_success_alt E r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap p b e a
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt E r1 pc_p pc_b pc_e pc_a w w' p b e a pc_a' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame.
  Qed.



End cap_lang_rules.
