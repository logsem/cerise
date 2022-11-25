From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base stdpp_extra.

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

  Definition reg_allows_load (regs : Reg) (i : CoreN) (r : RegName) p b e a  :=
    regs !! (i, r) = Some (WCap p b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure (i : CoreN) (regs: Reg) (r1 r2: RegName) (mem : gmap Addr Word) :=
  | Load_fail_const z:
      regs !! (i, r2) = Some (WInt z) ->
      Load_failure i regs r1 r2 mem
  | Load_fail_bounds p b e a:
      regs !! (i, r2) = Some (WCap p b e a) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      Load_failure i regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p b e a loadv:
      regs !! (i, r2) = Some (WCap p b e a) ->
      mem !! a = Some loadv →
      incrementPC (<[ (i, r1) := loadv ]> regs) i = None ->
      Load_failure i regs r1 r2 mem
  .

  Inductive Load_spec
    (i : CoreN)
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (mem : gmap Addr Word) : cap_lang.val → Prop
  :=
  | Load_spec_success p b e a loadv :
    reg_allows_load regs i r2 p b e a →
    mem !! a = Some loadv →
    incrementPC
      (<[ (i, r1) := loadv ]> regs) i = Some regs' ->
    Load_spec i regs r1 r2 regs' mem (i, NextIV)

  | Load_spec_failure :
    Load_failure i regs r1 r2 mem ->
    Load_spec i regs r1 r2 regs' mem (i, FailedV).

  Definition allow_load_map_or_true (i : CoreN) r (regs : Reg) (mem : gmap Addr Word):=
    ∃ p b e a, read_reg_inr regs i r p b e a ∧
      if decide (reg_allows_load regs i r p b e a) then
        ∃ w, mem !! a = Some w 
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (i : CoreN) (r2 : RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm) (b e a : Addr),
      allow_load_map_or_true i r2 r mem0
      → r !! (i, r2) = Some (WCap p b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : Word),
          mem0 !! a = Some loadv.
  Proof.
    intros i r2 mem0 r p b e a HaLoad Hr2v Hra Hwb.
    unfold allow_load_map_or_true in HaLoad.
    destruct HaLoad as (?&?&?&?&[Hrr | Hrl]&Hmem).
    - assert (Hrr' := Hrr). rewrite Hrr in Hr2v; inversion Hr2v; subst.
      case_decide as HAL.
      * auto.
      * unfold reg_allows_load in HAL.
        destruct HAL; auto.
    - destruct Hrl as [z Hrl]. by congruence.
  Qed.

  Lemma mem_eq_implies_allow_load_map:
    ∀ (i : CoreN) (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p b e a,
      mem = <[a:=w]> ∅
      → regs !! (i, r2) = Some (WCap p b e a)
      → allow_load_map_or_true i r2 regs mem.
  Proof.
    intros i regs mem r2 w p b e a Hmem Hrr2.
    exists p,b,e,a; split.
    - left. by simplify_map_eq by simplify_pair_eq.
    - case_decide; last done.
      exists w. simplify_map_eq by simplify_pair_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (i : CoreN) (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → regs !! (i, r2) = Some (WCap p b e a)
      → allow_load_map_or_true i r2 regs mem.
  Proof.
    intros i regs mem r2 pc_a w w' p b e a H4 Hrr2.
    exists p,b,e,a; split.
    - left. by simplify_map_eq by simplify_pair_eq.
    - case_decide; last done.
      exists w'. simplify_map_eq by simplify_pair_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (i : CoreN) (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → regs !! (i, r2) = Some (WCap p b e a)
      → allow_load_map_or_true i r2 regs mem.
  Proof.
    intros i regs mem r2 pc_a w w' p b e a H4 Hrr2.
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
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by simplify_map_eq by simplify_pair_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq by simplify_pair_eq.
  Qed.

  (* a more general version of load to work also with any fraction and persistent points tos *)
  Lemma gen_mem_valid_inSepM_general:
    ∀ mem0 (m : Mem) (a : Addr) (w : Word) dq,
      mem0 !! a = Some (dq,w) →
      gen_heap_interp m
                   -∗ ([∗ map] a↦dqw ∈ mem0, mapsto a dqw.1 dqw.2)
                   -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (mem0 m a w dq Hmem_pc) "Hm Hmem".
    iDestruct (big_sepM_delete _ _ a with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Definition prod_op {A B : Type} :=
    λ (o1 : option A) (o2 : option B), match o1 with
             | Some b => match o2 with
                        | Some c => Some (b,c)
                        | None => None
                        end
             | None => None
             end.

  Definition prod_merge {A B C : Type} `{Countable A} : gmap A B → gmap A C → gmap A (B * C) :=
    λ m1 m2, merge prod_op m1 m2.

  Lemma wp_load_general Ep i
     pc_p pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of_core (Load r1 r2) i ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true i r2 regs mem →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     (i, Instr Executable) @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec i regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of_core in Hri.
    feed destruct (Hri i r2) as [r2v [Hr'2 Hr2]]. by set_solver+.
    feed destruct (Hri i r1) as [r1v [Hr'1 _]]. by set_solver+. clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! pc_a)) as [dq Hdq].
    { apply elem_of_gmap_dom. rewrite -Hdomeq. apply elem_of_gmap_dom;eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq,w)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) m with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.

    unfold exec in Hstep; simpl in Hstep. rewrite Hr2 in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
    destruct r2v as  [| p b e a ] eqn:Hr2v.
    { (* Failure: r2 is not a capability *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      iFailWP "Hφ" Load_fail_const.
    }

    cbn in Hstep.
    destruct (readAllowed p && withinBounds b e a) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_fail_bounds.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    pose proof (allow_load_implies_loadv i r2 mem regs p b e a) as (loadv & Hmema); auto.

    assert (is_Some (dfracs !! a)) as [dq' Hdq'].
    { apply elem_of_gmap_dom. rewrite -Hdomeq. apply elem_of_gmap_dom;eauto. }
    assert (prod_merge dfracs mem !! a = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) m a loadv with "Hm Hmem" ) as %Hma' ; eauto.

    rewrite Hma' /= in Hstep.
    destruct (incrementPC (<[ (i, r1) := loadv ]> regs) i) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ (i, r1) := loadv]> r) i = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          by rewrite lookup_insert_is_Some'; eauto.
            eapply (@insert_mono (prod (@CoreN CP) RegName)); eauto. apply finmap_reg.
      }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" Load_fail_invalid_PC.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ i m) in Hregs'
      as (p1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC.
    2 : eapply (@insert_mono (prod (@CoreN CP) RegName)) ; eauto ; apply finmap_reg.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ (i, r1)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_spec_success; auto.
    * split; eauto.
    * exact Hmema.
    * unfold incrementPC. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

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
          destruct (create_gmap_default (elements (dom mem)) dq !! a)
          ; auto. rewrite H2;auto. cbn. destruct (mem !! a) ; auto.
        }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a)
          ; auto. rewrite H2;auto. cbn. destruct (mem !! a) ; auto. }
        iApply big_sepM_insert. auto.
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma wp_load Ep i
     pc_p pc_b pc_e pc_a
     r1 r2 w mem regs dq :
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
   regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
   regs_of_core (Load r1 r2) i ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true i r2 regs mem →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     (i, Instr Executable) @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec i regs r1 r2 regs' mem retv⌝ ∗
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

  Lemma wp_load_success E i r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ w''
          ∗ ▷ (i, r2) ↦ᵣ WCap p b e a
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ{dq'} w') }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ (if (eqb_addr a pc_a) then w else w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (i, r2) ↦ᵣ WCap p b e a
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq by simplify_pair_eq. }
    { eapply mem_implies_allow_load_map; eauto.
      by simplify_map_eq by simplify_pair_eq. }
    { destruct (a =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H5 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H6) as Hloadv; eauto.
       simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, r1) (i, PC)) ; simplify_pair_eq.
       rewrite insert_insert ; simplify_pair_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_notinstr E i r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ w''
          ∗ ▷ (i, r2) ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ (i, r2) ↦ᵣ WCap p b e a
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

  Lemma wp_load_success_frominstr E i r1 r2 pc_p pc_b pc_e pc_a w w'' p b e pc_a' dq :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ w''
          ∗ ▷ (i, r2) ↦ᵣ WCap p b e pc_a }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ w
             ∗ pc_a ↦ₐ{dq} w
             ∗ (i, r2) ↦ᵣ WCap p b e pc_a }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same E i r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ WCap p b e a
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} w') }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ (if (a =? pc_a)%a then w else w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq by simplify_pair_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq by simplify_pair_eq. }
    { destruct (a =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H4) as Hloadv; eauto.
       simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, r1) (i, PC)) ; simplify_pair_eq.
       rewrite insert_insert ; simplify_pair_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  Lemma wp_load_success_same_notinstr E i r1 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ w'
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

  Lemma wp_load_success_same_frominstr E i r1 pc_p pc_b pc_e pc_a w p b e pc_a' dq :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ WCap p b e pc_a }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ (i, r1) ↦ᵣ w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E i r2 pc_p pc_b pc_e pc_a w
        p b e a p' b' e' a' a'' :
    decodeInstrW w = Load PC r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ (i, r2) ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ WCap p' b' e' a' }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap p' b' e' a''
             ∗ pc_a ↦ₐ w
             ∗ (i, r2) ↦ᵣ WCap p b e a
             ∗ a ↦ₐ WCap p' b' e' a' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto.
      by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
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

  Lemma wp_load_success_fromPC E i r1 pc_p pc_b pc_e pc_a pc_a' w w'' dq :
    decodeInstrW w = Load r1 PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ (i, r1) ↦ᵣ w'' }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ pc_a ↦ₐ{dq} w
             ∗ (i, r1) ↦ᵣ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' φ)
            "(>HPC & >Hi & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq by simplify_pair_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq by simplify_pair_eq.
       rewrite -memMap_resource_1_dq.
       incrementPC_inv.
       simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, r1)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, r1) (i, PC)) ; simplify_pair_eq.
       rewrite insert_insert ; simplify_pair_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
       destruct o; apply Is_true_false_2 in H3. all: try congruence. done.
     }
  Qed.

End cap_lang_rules.
