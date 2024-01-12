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
    incrementLPC (<[ dst := LInt 0 ]> lregs) = None ->
    IsUnique_fail lregs lmem dst src.

  Definition update_version_word_region (lmem : LMem) (lwsrc : LWord)
    (v : Version) : option LMem. Admitted.

  Inductive IsUnique_spec
    (lregs: LReg) (lmem : LMem) (dst src : RegName)
    (lregs': LReg) (lmem' : LMem) : cap_lang.val → Prop :=

  | IsUnique_success_true (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    unique_in_machineL lmem lregs src lwsrc ->

    (* we update the region of memory with the new version *)
    update_version_word_region lmem lwsrc (v+1) = Some lmem' →

    incrementLPC (<[ dst := LInt 1 ]> (<[ src := LCap p b e a (v+1) ]> lregs)) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_false (lwsrc: LWord) p b e a v :

    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    (* NOTE
       =not (unique_in_machineL lmem lregs src lwsrc)=
       might not be true,
       because we only have a local view of lmem,
       and the overlapping word might be somewhere in the lmemory
       outside of our local view.

       TODO
       Do we want to capture that, it exists an overlapping word ?
       I'd argue that we don't really care,
       because the important part is to know
       when the sweep is true (and get the guarantee that it is true).
       When the sweep is false,
       then we just don't get any guarantee from it
       (and the program will just discard)
     *)
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

  Lemma allow_access_implies_memmap:
    ∀ (r : RegName) (lmem : LMem) (lregs : LReg) (p : Perm) (b e a : Addr) v,
      allow_access_map_or_true r lregs lmem
      → lregs !! r = Some (LCap p b e a v)
      → Forall ( fun a => exists lw, lmem !! (a,v) = Some lw) (finz.seq_between b e).
  Proof.
    intros r lmem lregs p b e a v HaAccess Hrv.
    unfold allow_access_map_or_true, read_reg_inr in HaAccess.
    destruct HaAccess as (?&?&?&?&?& Hrinr & Hmem).
    rewrite Hrv in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - exact Hmem.
    - contradiction Hrega.
  Qed.

  (* TODO property desired about update_version_word_region *)
  Lemma update_cur_version_region_implies_next_version
    (lm lm' : LMem) (cur_map cur_map': VMap)
    (p : Perm) (b e a : Addr) (v : Version) :
    is_cur_word (LCap p b e a v) cur_map ->
    update_cur_version_region lm cur_map (finz.seq_between b e) = Some (lm', cur_map') ->
    update_version_word_region lm (LCap p b e a v) (v + 1) = Some lm'.
  Proof.
  Admitted.

  (* TODO maybe we can have a more general way to update the resources *)
  Lemma gen_heap_lmem_version_update :
    ∀ (lm lmem lm' lmem': LMem) (cur_map cur_map': VMap)
      (b e : Addr) ( v : Version ),
    update_cur_version_region lm cur_map (finz.seq_between b e) = Some (lm', cur_map') ->
    update_cur_version_region lmem cur_map (finz.seq_between b e) = Some (lmem', cur_map') ->
    Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) (finz.seq_between b e) ->
    Forall (λ a : Addr, cur_map !! a = Some v) (finz.seq_between b e) ->
    gen_heap_interp lm
    -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
    ==∗ gen_heap_interp lm'
      ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
  Proof.
    iIntros
      (lm lmem lm' lmem' cur_map cur_map' b e v Hupd_lm Hupd_lmem
         HmemMap HcurMap)
        "Hgen Hmem".
  Admitted.


  (* NOTE/TODO: Sum up.
     For the case where is_unique succeed, the specification gives us that,
    - the given word is unique in the machine (both registers and memory)
      with the predicate =unique_in_machineL lregs lmem lwsrc src v=

    - the new memory and register file has an updated version of the word/addresses
      with the predicates
      + update_version lmem (finz.seq_between b e) v (v + 1) = Some lmem'
      + incrementLPC (<[ dst := LInt 1 ]> (<[ src := LCap p b e a (v+1) ]> lregs)) = Some lregs'

    In particular, what is necessary is to prove that, lmem' and lreg' still hold the
    WP invariant (link between logical and physical world). The main glue between everything
    is the =cur_map : VMap=, which records what is the current version of an address.

    One thing to do then is to update the current_view with a new version number.
    However, when upgrading the version number, it cancels all of the others versions
    of the addresses/words. From =unique_in_machineL=, we know that it will actually cancel
    nothing else.
   *)

  (** NOTE Proof strategy:

    We only care when the sweep is true.
    1. From the operational 'sweep phm phr src = true',
       the specification states that there's no overlap in the *physical* machine,
       'unique_in_machine phm phr src wsrc'

    2. In combination with the 'phys_log_correspondance',
       we get an equivalent for the *logical machine*,
       'unique_in_machineL lm lr src lwsrc'.

    2a. We define 'unique_in_machineL' by looking only at
        the last version of each laddress.
        'phys_log_correspondance' states that,
        the physical memory corresponds
        to the logical view for the current view of each address.
        It also states that,
        the current view of a logical address
        is actually the max version in the lmemory.

    2b. Thanks to 2a,
        under the 'phys_log_correspondance' hypothesis,
        we know that the current view of the lmemory
        corresponds to the laddresses with the max version number.
        We can then reason equivalently with
        the 2 interpretation of
        "the current view" (easier to reason about)
        VS "last version number" (requires to know the current view map)

    3. From 'unique_in_machineL lmem lregs src lwsrc',
       we know that we can safely update the lmemory region in lmem
       corresponding to 'lwsrc'.

    4. Because the lmem had been updated,
       we can also update the heap resources;
       for the memory and the registers.

    5. It is finally possible to re-establish
       'phys_log_correspondance
        phr phm (updated lregs) (updated lmem) (updated cur_map)',
        which, one might notice, only changes the version number.
   *)

  Set Nested Proofs Allowed.
  Lemma wp_isunique Ep
    pc_p pc_b pc_e pc_a pc_v
    (dst src : RegName) lw lmem lregs :
    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsUnique dst src) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
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
    iSplitR.
    by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto; eapply step_exec_inv in Hstep; eauto.
    2: eapply state_phys_corresponds_reg ; eauto ; cbn ; eauto.
    2: eapply state_phys_corresponds_mem_PC ; eauto; cbn ; eauto.

    set (srcv := lword_get_word lsrcv).
    assert ( reg !! src = Some srcv ) as Hsrc
        by (eapply state_phys_log_reg_get_word ; eauto).
    rewrite /exec /= Hsrc /= in Hstep.

    (* Start the different cases now *)

    (* src contains a capability *)
    destruct (is_log_cap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *.
    { (* Fail : not a capability *)
      destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.
      all: simplify_map_eq.
      all: (iSplitR "Hφ Hmap Hmem"
            ; [ iExists lr, lm, cur_map; iFrame; auto
              | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_cap
           ]).
    }
    destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.

    pose proof
      (allow_access_implies_memmap src lmem lregs p b e a v HaAccess Hlsrc')
      as HmemMap ; auto.

    (* sweep success or sweep fail *)
    destruct (sweep mem reg src) as [|] eqn:Hsweep ; cbn in Hstep.
    - (* sweep is true *)
      eapply sweep_true_specL in Hsweep; eauto.

      destruct (incrementLPC (<[ dst := LInt 1 ]>
                                (<[ src := LCap p b e a (v+1)]> lregs)))
        as  [ lregs' |] eqn:Hlregs'
      ; pose proof Hlregs' as H'lregs'
      ; cycle 1.
      { (* Failure: the PC could not be incremented correctly *)
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
      }

      (* PC has been incremented correctly *)
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
      rewrite HuPC in Hstep; clear HuPC.
      inversion Hstep; clear Hstep ; simplify_map_eq.

      (* we destruct the cases when the registers are equals *)
      destruct (decide (src = PC)); simplify_map_eq ; cycle 1.
      * (* src <> PC *)
        destruct (decide (src = dst)) ; simplify_map_eq ; cycle 1.
        ** (* src <> dst *)
          iMod ((gen_heap_update_inSepM _ _ src (LCap p b e a (v + 1))) with "Hr Hmap")
            as "[Hr Hmap]"; eauto.
          iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto ; first by simplify_map_eq.
          iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto ; first by simplify_map_eq.

          pose proof
            (state_phys_log_cap_all_current _ _ _ _ _ _ _ _ _ _ _ HLinv Hlsrc)
          as HcurMap.

          assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).

          destruct (update_cur_version_word_region lmem cur_map (LCap p b e a v))
            as [[lmem' cur_map']|] eqn:Hupd_lm
          ; rewrite /update_cur_version_word_region /= in Hupd_lm
          ; cycle 1.
          {
            exfalso.
            apply eq_None_not_Some in Hupd_lm.
            apply Hupd_lm.
            eapply update_cur_version_region_Some; eauto.
          }

          pose proof Hupd_lm as Hupd_lmem.
          eapply update_cur_version_region_mono in Hupd_lmem ; eauto.
          destruct Hupd_lmem as (lm' & Hupd_lmem & Hmem').

          iMod ((gen_heap_lmem_version_update lm lmem lm' lmem' ) with "Hm Hmem")
            as "[Hm Hmem]"; eauto.

          assert (update_version_word_region lmem (LCap p b e a v) (v + 1) = Some lmem').
          {
            eapply update_cur_version_region_implies_next_version; eauto.
            destruct HLinv as [Hinv_reg _].
            eapply lreg_read_iscur; eauto.
          }

          assert (unique_in_machineL lmem lregs src (LCap p b e a v)).
          {
            eapply unique_in_machineL_mono; eauto.
            rewrite /lmem_last_version_subseteq.
            admit. (* TODO it might not be true... *)
          }

          iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
          ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto].
          iExists _, lm', cur_map'; iFrame; auto
          ; iPureIntro; econstructor; eauto
          ; destruct HLinv as [Hreg_inv Hmem_inv]
          ; cbn in *.
          {
            rewrite (insert_commute _ _ src) // (insert_commute _ _ src) //.
            eapply lookup_weaken in HPC'' ; eauto.
            eapply update_cur_version_reg_phys_log_cor_updates_src
              with (phm := mem) ; eauto.
            2: by rewrite lookup_insert_ne // lookup_insert_ne //.
            2: {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
              eapply not_overlap_word_leaL with (a2' := a1); eauto.
              eapply (unique_in_machineL_not_overlap_word _ _ src PC); eauto.

              eapply unique_in_machineL_insert_reg; eauto
              ; try by simplify_map_eq.
            }
            split; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
            by cbn.
            apply is_cur_word_lea with (a := a1).
            eapply lreg_read_iscur; eauto.
          }
          {
            eapply update_cur_version_region_preserves_mem_phyc_cor; eauto.
            eapply unique_in_machine_no_accessL ; eauto.
            eapply lreg_read_iscur; eauto.
          }

        ** (* src = dst *) admit.

      * (* src = PC *)
        rewrite (insert_commute _ dst PC) //= insert_insert insert_commute //= in H'lregs'.
        (* we update the registers with their new value *)
        destruct (decide (dst = PC)) ; simplify_map_eq.
        (* dst ≠ PC *)
        iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
        iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
        ; first by simplify_map_eq.

        (* iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
        (* ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto]. *)

        admit.


    - (* sweep = false *)

      destruct (incrementLPC (<[ dst := LInt 0 ]> lregs))
        as  [ lregs' |] eqn:Hlregs'
      ; pose proof Hlregs' as H'lregs'
      ; cycle 1.
      {  (* Failure: the PC could not be incremented correctly *)
        apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'.
        eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hlregs'.
        2: {
          rewrite /lreg_strip lookup_fmap.
          apply fmap_is_Some.
          destruct (decide (dst = PC)) ; simplify_map_eq; auto.
        }
        2: apply map_fmap_mono ; apply insert_mono ; eauto.
        replace ((λ lw : LWord, lword_get_word lw) <$> (<[dst:=LInt 0]> lr))
          with (<[dst:= WInt 0]> reg)
          in Hlregs'
        ; cycle 1.
        { destruct HLinv as [[Hstrips Hcurreg] _].
          rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
        }

        rewrite Hlregs' in Hstep. inversion Hstep.
        iSplitR "Hφ Hmap Hmem"
        ; [ iExists lr, lm, cur_map; iFrame; auto
          | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_invalid_PC_false
          ].
      }

      (* PC has been incremented correctly *)
      rewrite /update_reg /= in Hstep.
      eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
          as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->)
      ; simplify_map_eq.
      assert (dst <> PC) as Hdst by (intro ; simplify_map_eq).
      eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
      2: apply map_fmap_mono ; apply insert_mono ; eauto.
      replace ((λ lw, lword_get_word lw) <$> <[dst:=LInt 0]> lr)
        with (<[dst:=WInt 0]> reg) in HuPC.
      2: { destruct HLinv as [[Hstrips Hcurreg] _]
           ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
      }
      rewrite HuPC in Hstep; clear HuPC.
      inversion Hstep; clear Hstep ; simplify_map_eq.

      iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
      ; first by simplify_map_eq.

      iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
      ; [| iApply "Hφ" ; iFrame; iPureIntro; eapply IsUnique_success_false ; eauto].

      iExists _, lm, cur_map; iFrame; auto
      ; iPureIntro; econstructor; eauto
      ; destruct HLinv as [[Hstrips Hcur_reg] [Hdom Hroot]]
      ; cbn in *
      ; [|split;eauto]
      .
      split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=.
      apply map_Forall_insert_2 ; [|by apply map_Forall_insert_2; cbn].
      rewrite HPC in HPC'' ; simplify_eq.
      eapply is_cur_word_cap_change; eauto.
  Admitted.

  (* TODO derive a valid version of the rule:
     Because I don't know the whole content of the memory (only a local view),
     any sucessful IsUnique wp-rule can have 2 outcomes:
     either the sweep success or the sweep fails.

    Importantly, we cannot derive any sweep success rule, because we would need
    the entire footprint of the registers/memory.
   *)

End cap_lang_rules.
