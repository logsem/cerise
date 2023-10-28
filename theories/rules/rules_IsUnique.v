From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.


  Definition overlap_lwords (lw1 lw2 : LWord) : Prop :=
    (overlap_word (lword_get_word lw1) (lword_get_word lw2)) = true.

  (* For all addresses in the given region, update the version of the address *)
  Definition update_version (lmem : LMem) (region : list Addr) (old_v new_v : Version)
    : option LMem :=
    foldl
      (fun (opt_lmem' : option LMem) (a : Addr) =>
         lmem' ← opt_lmem';
         lw ← lmem' !! (a, old_v);
         Some (<[(a, new_v) := lw ]> lmem'))
      (Some lmem)
      region.

  (* Forall addresses a in the region, we update with v', if it exists a max_version mv st. *)
  (* 1. lmem !! (a, mv) = lw  *)
  (* 2. ∀ v. (∃ lw',  lmem !! (a, v) = lw') → v ≤ mv *)
  (* 3. lmem' = <[ (a, v') = lw ]> lmem *)

  (* Definition get_max_version (lmem : LMem) (a : Addr) : Version := *)
 (*   map_fold *)
  (*     (fun (la : LAddr) (_ : LWord) (max_version : Version) => *)
  (*        if ((laddr_get_addr la) =? a)%a *)
  (*        then max (laddr_get_version la) max_version *)
  (*        else max_version) *)
  (*     0 *)
  (*     lmem. *)

  (* TODO we don't need to get the max_version of an address, because *)
  (* we already know, by construction, that we have the current view of the region *)
  (* and that all addresses in the region also have the current version *)

  Inductive IsUnique_fail (lregs : LReg) (lmem : LMem) (dst src : RegName): Prop :=
  | IsUnique_fail_cap (lwsrc: LWord) :
    lregs !! src = Some lwsrc ->
    is_log_cap lwsrc = false →
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_true (lwsrc: LWord) p b e a v:
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := LCap p b e a (v+1) ]> lregs)) = None ->
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_false (lwsrc: LWord):
    lregs !! src = Some lwsrc ->
    incrementLPC (<[ dst := LInt 1 ]> lregs) = None ->
    IsUnique_fail lregs lmem dst src.

  Inductive IsUnique_spec
    (lregs: LReg) (lmem : LMem) (dst src : RegName)
    (lregs': LReg) (lmem' : LMem) : cap_lang.val → Prop :=

  | IsUnique_success_true (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    (* check if the words overlap only if the versions matches *)
    Forall
      (fun '(la, lw) => (laddr_get_version la) = v -> not (overlap_lwords lwsrc lw))
      (map_to_list lmem) ->
    (* we update the region of memory with the new version *)
    update_version lmem (finz.seq_between b e) v (v + 1) = Some lmem' ->

    incrementLPC (<[ dst := LInt 1 ]> (<[ src := LCap p b e a (v+1) ]> lregs)) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_false (lwsrc: LWord) p b e a v :

    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    (* it exists a word in the memory that overlaps somewhere in the memory *)
    Exists
      (fun '(la, lw) => (laddr_get_version la) = v -> overlap_lwords lwsrc lw)
      (map_to_list lmem) ->
    incrementLPC (<[ dst := LInt 0 ]> lregs) = Some lregs' ->
    lmem' = lmem ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_failure :
    lregs = lregs' ->
    lmem = lmem' ->
    IsUnique_fail lregs lmem dst src ->
    IsUnique_spec lregs lmem dst src lregs' lmem' FailedV
  .

  (* TODO @Bastien *)

  Definition allow_access_map_or_true (r : RegName) (lregs : LReg) (lmem : LMem) : Prop :=
    exists p b e a v, read_reg_inr lregs r p b e a v
                 ∧ if decide (lregs !! r = Some (LCap p b e a v))
                   then Forall (fun a' => exists lw, lmem !! (a',v) = Some lw) (finz.seq_between b e)
                   else True.

  Lemma insert_reg_lreg_strip (lregs : LReg) (r : RegName) (lw : LWord) :
    lregs !! r = Some lw ->
    <[ r := lword_get_word lw ]> (lreg_strip lregs) = lreg_strip lregs.
  Proof.
    intros Hr.
    rewrite -/lreg_strip -fmap_insert insert_id //.
  Qed.

  Lemma insert_cap_lreg_strip (lregs : LReg) (r : RegName)
     (p : Perm) (a b e : Addr) (v : Version) :
    lregs !! r = Some (LCap p b e a v) ->
    <[ r := WCap p b e a ]> (lreg_strip lregs) = lreg_strip lregs.
  Proof.
    intros Hr.
    replace (WCap p b e a) with (lword_get_word (LCap p b e a v)) by done.
    rewrite -fmap_insert insert_id //=.
  Qed.

  Lemma sweep_true_spec reg mem lr lm cur_map r p b e a v:
    state_phys_log_corresponds reg mem lr lm cur_map ->
    sweep r reg mem = true ->
    reg !! r = Some (WCap p b e a) ->
    Forall
      (λ '(la, lw), laddr_get_version la = v → ¬ overlap_lwords (LCap p b e a v) lw)
      (map_to_list lm).
    Admitted.

  Lemma sweep_false_spec reg mem lr lm cur_map r p b e a v:
    state_phys_log_corresponds reg mem lr lm cur_map ->
    sweep r reg mem = false ->
    reg !! r = Some (WCap p b e a) ->
    Exists
      (fun '(la, lw) => (laddr_get_version la) = v -> overlap_lwords (LCap p b e a v) lw)
      (map_to_list lm).
  Admitted.

  Lemma submseteq_incl `{A : Type} (l1 l2 : list A) :
    l1 ⊆+ l2 -> incl l1 l2.
  Proof.
    intros Hsubset ; induction Hsubset. Admitted.

  Lemma wp_isunique Ep
    pc_p pc_b pc_e pc_a pc_v pca_v
    (dst src : RegName) lw lmem lregs :
    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsUnique dst src) ⊆ dom lregs →
    lmem !! (pc_a, pca_v) = Some lw →
    allow_access_map_or_true src lregs lmem →

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ IsUnique_spec lregs lmem dst src lregs' lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaAccess φ) "(>Hmem & >Hmap) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.

    (* Derive necessary register values in r *)
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri dst) as [ldstv [Hldst' Hldst]]. by set_solver+.
    odestruct (Hri src) as [lsrcv [Hlsrc' Hlsrc]]. by set_solver+.

    (* Derive necessary memory *)
    iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hmem.
    iDestruct (gen_mem_valid_inSepM lmem lm with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto; eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_corresponds_reg ; eauto ; cbn ; eauto.
    2: eapply state_phys_corresponds_mem ; eauto; cbn ; eauto.


    set (srcv := lword_get_word lsrcv).
    assert ( reg !! src = Some srcv ) as Hsrc
    by (eapply state_phys_log_reg_get_word ; eauto).
    rewrite /exec /= Hsrc /= in Hstep.

    (* Start the different cases now *)
    destruct (is_log_cap lsrcv) eqn:Hlsrcv; cycle 1.
    { (* Fail : not a capability *) admit.

    }
    subst srcv; cbn in *.
    destruct_lword lsrcv; cbn in * ; try congruence. clear Hlsrcv.
    destruct (sweep src reg mem) as [|] eqn:Hsweep ; cbn in Hstep.

    - (* sweep is true *)

    (* Derive spec of sweep that returns true -> no overlap *)
    eapply sweep_true_spec in Hsweep; eauto.
    apply map_to_list_submseteq, submseteq_incl in Hmem.
    eapply incl_Forall with (l2 := (map_to_list lmem)) in Hsweep ; eauto.

    destruct (incrementLPC (<[ dst := LInt 1 ]>
                            (<[ src := LCap p b e a (v+1)]> lregs)))
      as  [ lregs' |] eqn:Hlregs'
    ; pose proof Hlregs' as H'lregs'
    ; cycle 1.
    + (* Failure: the PC could not be incremented correctly *)
      apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'.
      eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hlregs'.
      2: {
        rewrite /lreg_strip lookup_fmap.
        apply fmap_is_Some.
        destruct (decide (dst = PC)) ;  destruct (decide (src = PC)) ; simplify_map_eq; auto.
      }
      2: apply map_fmap_mono
      ; apply (insert_mono _ ( <[src:=LCap p b e a (v + 1)]> lr))
      ; apply insert_mono ; eauto.
      simplify_pair_eq.
      replace ((λ lw : LWord, lword_get_word lw) <$> (<[dst:=LInt 1]> (<[src:=LCap p b e a (v + 1)]> lr)))
        with (<[dst:= WInt 1]> reg)
        in Hlregs'
      ; cycle 1.
      { destruct HLinv as [[Hstrips Hcurreg] _].
        rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
        erewrite insert_cap_lreg_strip; eauto.
      }

      rewrite Hlregs' in Hstep. inversion Hstep.
      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, cur_map; iFrame; auto
        | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_invalid_PC_true
        ].
    + (* PC has been incremented correctly *)

    rewrite /update_reg /= in Hstep.
    eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
          as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->)
    ; simplify_map_eq.
    assert (dst <> PC) as Hdst by (intro ; simplify_map_eq).
    eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
    2: apply map_fmap_mono
    ; apply (insert_mono _ ( <[src:=LCap p b e a (v + 1)]> lr))
    ; apply insert_mono ; eauto.
    replace ((λ lw, lword_get_word lw) <$>
               <[dst:=LInt 1]> (<[src:=LCap p b e a (v + 1)]> lr))
        with (<[dst:=WInt 1]> reg) in HuPC.
    2: { destruct HLinv as [[Hstrips Hcurreg] _]
         ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=
         ; erewrite insert_cap_lreg_strip ; eauto.
    }
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep
    ; simplify_map_eq.

    destruct (decide (src = PC)); simplify_map_eq.
    * (* src = PC *)
    rewrite (insert_commute _ dst PC) //= insert_insert insert_commute //= in H'lregs'.
    (* we update the registers with their new value *)
    iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
    ; first by simplify_map_eq.
    (* we update the version of the memory region *)
    (* TODO *)

    iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem".
    2: {
      iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto.
      admit. (* TODO we need to have it in the hypothesis before *)
    }

    iExists _, lm, cur_map; iFrame; auto
    ; iPureIntro; econstructor; eauto
    ; destruct HLinv as [[Hstrips Hcur_reg] [Hdom Hroot]]
    ; cbn in *.
    split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=.
    admit. (* TODO we need to do the upgrade before, for b1 e1 *)
    split; eauto.

    * (* src <> PC *)
      (* TODO also need to destruct on (dst = src) *)
    iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
    ; first by simplify_map_eq.
    iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem".
    (* 2: { *)
    (*   iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto. *)
    (*   admit. admit. admit. *)
    (* } *)
    admit. admit.

    - (* sweep = false *)

    (* TODO Derive spec of sweep that returns false -> there is an overlap *)
    (* eapply sweep_false_spec in Hsweep; eauto. *)
    (* apply map_to_list_submseteq, submseteq_incl in Hmem. *)
    (* eapply incl_Exists with (l2 := (map_to_list lmem)) in Hsweep ; eauto. *)


   Admitted.

End cap_lang_rules.
