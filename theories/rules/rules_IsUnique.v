From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.
From cap_machine.proofmode Require Export region register_tactics.

Section cap_lang_rules.
  Context `{HmemG : memG Σ, HregG : regG Σ}.
  Context `{Hparam : MachineParameters}.
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
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword lwsrc ]> lregs)) = None ->
    IsUnique_fail lregs lmem dst src

  | IsUnique_fail_invalid_PC_false (lwsrc: LWord):
    lregs !! src = Some lwsrc ->
    incrementLPC (<[ dst := LInt 0 ]> lregs) = None ->
    IsUnique_fail lregs lmem dst src.

  Inductive IsUnique_spec
    (lregs: LReg) (lmem : LMem) (dst src : RegName)
    (lregs': LReg) (lmem' : LMem) : cap_lang.val → Prop :=

  | IsUnique_success_true (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    (* we update the region of memory with the new version *)
    is_valid_updated_lmemory lmem (finz.seq_between b e) v lmem' ->
    incrementLPC (<[ dst := LInt 1 ]> (<[ src := next_version_lword lwsrc ]> lregs)) = Some lregs' ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_success_false (lwsrc: LWord) p b e a v :
    lregs !! src = Some lwsrc ->
    get_lcap lwsrc = Some (LSCap p b e a v) ->
    incrementLPC (<[ dst := LInt 0 ]> lregs) = Some lregs' ->
    lmem' = lmem ->
    IsUnique_spec lregs lmem dst src lregs' lmem' NextIV

  | IsUnique_failure :
    lregs = lregs' ->
    lmem = lmem' ->
    IsUnique_fail lregs lmem dst src ->
    IsUnique_spec lregs lmem dst src lregs' lmem' FailedV
  .

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
        phr phm (updated lregs) (updated lmem) (updated vmap)',
        which, one might notice, the version number changes.
   *)

  (* Helper lemma to avoid proof duplication *)
  Lemma mem_phys_log_update
    (reg : Reg) (mem : Mem)
    (lr : LReg) (lm lm' : LMem) (vmap vmap' : VMap)
    (src : RegName) (p : Perm) (b e a : Addr) (v : Version) (lw : LWord) :
    get_lcap lw = Some (LSCap p b e a v) ->
    (* necessary for lreg_res_iscur *)
    reg_phys_log_corresponds reg lr vmap ->
    (* necessary for unique_in_machine_no_accessL *)
    lr !! src = Some lw ->
    unique_in_machineL lm lr src lw ->

    (* necessary for update_cur_version... *)
    NoDup (finz.seq_between b e) ->
    update_cur_version_region_local lm vmap (finz.seq_between b e)
    = (lm', vmap') ->
    mem_phys_log_corresponds mem lm vmap ->
    mem_phys_log_corresponds mem lm' vmap'.
  Proof.
    intros.
    eapply update_cur_version_region_local_preserves_mem_phyc_cor; eauto.
    eapply unique_in_machine_no_accessL ; eauto.
    eapply lreg_corresponds_read_iscur; eauto.
  Qed.

  (** NOTE What should be captured:

    --- ownership over the whole region  ---
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v)
        ∗ dst        ↦ᵣ _
        ∗ (b, v)     ↦ₐ lwb
        ∗ (b+1, v)   ↦ₐ lwb'
    }}}
    ->
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v+1)
        ∗ dst        ↦ᵣ LInt 1
        ∗ (b, v)     ↦ₐ lwb
        ∗ (b+1, v)   ↦ₐ lwb'

        ∗ (b, v+1)   ↦ₐ lwb
        ∗ (b+1, v+1) ↦ₐ lwb'
    }}}

    --- ownership over part of the region  ---
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v)
        ∗ dst        ↦ᵣ _
        ∗ (b, v)     ↦ₐ lwb
    }}}
    ->
    {{{ (pc_a, pc_v) ↦ₐ IsUnique dst src
        ∗ src        ↦ᵣ (p,b,b+2,_,v+1)
        ∗ dst        ↦ᵣ LInt 1
        ∗ (b, v)     ↦ₐ lwb

        ∗ (b, v+1)   ↦ₐ lwb
        ∗ (∃ lwb', (b+1, v+1) ↦ₐ lwb')
                             ;; note that =not (overlap lwb' (p,b,b+2,_,v))=
                             ;; if it's interesting in any way
    }}}

   *)

  Lemma wp_isunique Ep
    pc_p pc_b pc_e pc_a pc_v
    (dst src : RegName) lw lmem lregs :
    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (IsUnique dst src) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    (* allow_access_map_or_true src lregs lmem → *)

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' lmem' retv, RET retv;
          ⌜ IsUnique_spec lregs lmem dst src lregs' lmem' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem', la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc φ) "(>Hmem & >Hmap) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap) "(Hr & Hm & %HLinv)"; simpl in HLinv.

    (* Derive necessary register values in r *)
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri dst) as [ldstv [Hldst' Hldst] ]; first by set_solver+.
    odestruct (Hri src) as [lsrcv [Hlsrc' Hlsrc] ]; first by set_solver+.

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
    2: rewrite -/((lword_get_word (LCap pc_p pc_b pc_e pc_a pc_v)))
    ; eapply state_corresponds_reg_get_word ; eauto.
    2: eapply state_corresponds_mem_correct_PC ; eauto; cbn ; eauto.

    set (srcv := lword_get_word lsrcv).
    assert ( reg !! src = Some srcv ) as Hsrc
        by (eapply state_corresponds_reg_get_word ; eauto).
    rewrite /exec /= Hsrc /= in Hstep.

    (* Start the different cases now *)

    (* src contains a capability *)
    destruct (is_lcap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *.
    { (* Fail : not a capability *)
      destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.
      all: simplify_map_eq.
      all: (iSplitR "Hφ Hmap Hmem"
            ; [ iExists lr, lm, vmap; iFrame; auto
              | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_cap
           ]).
    }

    destruct (get_is_lcap_inv lsrcv Hlsrcv) as (p & b & e & a & v & Hget_lsrcv).


    (* sweep success or sweep fail *)
    destruct (sweep mem reg src) as [|] eqn:Hsweep ; cbn in Hstep.
    - (* sweep is true *)
      eapply sweep_true_specL in Hsweep; eauto.

      destruct (incrementLPC (<[ dst := LInt 1 ]>
                                (<[ src := next_version_lword lsrcv]> lregs)))
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
        ; apply (insert_mono _ ( <[src:= next_version_lword lsrcv]> lr))
        ; apply insert_mono ; eauto.
        simplify_pair_eq.
        replace ((λ lw : LWord, lword_get_word lw) <$>
                   (<[dst:=LInt 1]> (<[src:= next_version_lword lsrcv]> lr)))
          with (<[dst:= WInt 1]> reg)
          in Hlregs'
        ; cycle 1.
        { destruct HLinv as [ [Hstrips Hcurreg] _].
          rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
          rewrite lword_get_word_next_version insert_lcap_lreg_strip; eauto.
        }
        rewrite Hlregs' in Hstep.
        match goal with
        | Hstep :
          match ?x with _ => _ end = (_,_) |- _ =>
            replace x with (None : option Conf) in Hstep
              by (destruct_lword lsrcv ; eauto)
        end.
        destruct_lword lsrcv ; cbn in * ; try congruence ; inversion Hstep.
        all: (iSplitR "Hφ Hmap Hmem"
              ; [ iExists lr, lm, vmap; iFrame; auto
                | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_invalid_PC_true
             ]).
      }

      (* PC has been incremented correctly *)
      rewrite /update_reg /= in Hstep.
      eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
          as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->)
      ; simplify_map_eq.
      assert (dst <> PC) as Hdst by (intro ; simplify_map_eq).
      eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC.
      2: apply map_fmap_mono
      ; apply (insert_mono _ ( <[src:= next_version_lword lsrcv]> lr))
      ; apply insert_mono ; eauto.
      replace ((λ lw, lword_get_word lw) <$>
               <[dst:=LInt 1]> (<[src:= next_version_lword lsrcv]> lr))
        with (<[dst:=WInt 1]> reg) in HuPC.
      2: { destruct HLinv as [ [Hstrips Hcurreg] _]
           ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=
           ; rewrite lword_get_word_next_version insert_lcap_lreg_strip; eauto.
      }
      rewrite HuPC in Hstep; clear HuPC.
      inversion Hstep; clear Hstep ; simplify_map_eq.
      match goal with
      | Hstep : match ?x with _ => _ end = (_,_) |- _ =>
          match goal with
          | Hstep' : context f [ Some (?a,?b) ] |- _ =>
          replace x with (Some (a,b)) in H0
                by (destruct_lword lsrcv ; cbn in * ; try congruence)
          end
      end.

      (* update version number of memory points-to *)
      assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).

      pose proof
        (state_corresponds_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ HLinv Hget_lsrcv Hlsrc)
        as HcurMap.
      pose proof
        (state_corresponds_last_version_lword_region _ _ _ _ _ _ _ _ _ _ _ _  HLinv Hget_lsrcv Hlsrc)
        as HmemMap_maxv.
      pose proof
        (state_corresponds_access_lword_region _ _ _ _ _ _ _ _ _ _ _ _ HLinv Hget_lsrcv Hlsrc)
        as HmemMap.

      destruct (update_cur_version_word_region_global lmem lm vmap lsrcv)
        as [lmem' vmap_mem'] eqn:Hupd_lmem
      ; rewrite /update_cur_version_word_region_global Hget_lsrcv /= in Hupd_lmem.
      destruct (update_cur_version_word_region_local lm vmap lsrcv)
        as [lm' vmap_m'] eqn:Hupd_lm
      ; rewrite /update_cur_version_word_region_local Hget_lsrcv /= in Hupd_lm.
      iMod ((gen_heap_lmem_version_update lm lmem lm' lmem' ) with "Hm Hmem")
        as "[Hm Hmem]"; eauto.

      (* we destruct the cases when the registers are equals *)
      destruct (decide (src = PC)); cycle 1.
      * (* src <> PC *)
        destruct (decide (src = dst)) ; simplify_map_eq ; cycle 1.
        ** (* src <> dst *)
          iMod ((gen_heap_update_inSepM _ _ src (next_version_lword lsrcv)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto.
          iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto ; first by simplify_map_eq.
          iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto ; first by simplify_map_eq.

          iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
          ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto].
          iExists _, lm', vmap_m'; iFrame; auto
          ; iPureIntro; econstructor; eauto
          ; destruct HLinv as [Hreg_inv Hmem_inv]
          ; cbn in *.
          {
            rewrite (insert_commute _ _ src) // (insert_commute _ _ src) //.
            eapply lookup_weaken in HPC'' ; eauto.
            replace reg with (<[ src := lword_get_word (next_version_lword lsrcv) ]> reg).
            2: { rewrite insert_id //= lword_get_word_next_version //=. }
            do 2 (rewrite (insert_commute _ _ src) //).

            eapply update_cur_version_reg_phys_log_cor_updates_src with
            (phm := mem); eauto; cycle 1.
            eapply update_cur_version_region_local_update_lword ; eauto.
            eapply lreg_corresponds_read_iscur; eauto.
            by rewrite lookup_insert_ne // lookup_insert_ne //.
            {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
              eapply not_overlap_word_leaL with (a2' := a_pc1)
              ; cycle 4
              ; first eapply (unique_in_machineL_not_overlap_word _ _ src PC); eauto.
              eapply unique_in_machineL_insert_reg; eauto.
              by destruct_lword lsrcv ; cbn; intro.
            }
            split; eauto.
            eapply lreg_corresponds_insert_respects; eauto.
            eapply lreg_corresponds_insert_respects; eauto.
            by cbn.
            apply is_cur_lword_lea with (a := a1).
            eapply lreg_corresponds_read_iscur; eauto.
          }
          { eapply mem_phys_log_update ; eauto. }
          { eapply update_cur_version_region_global_valid; eauto. }

        ** (* src = dst *)
          iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto.
          iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap")
            as "[Hr Hmap]"; eauto ; first by simplify_map_eq.

          iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
          ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto].
          3: { rewrite insert_insert in H'lregs'.
               rewrite insert_insert. done.
          }
          2: eapply update_cur_version_region_global_valid; eauto.

          iExists _, lm', vmap_m'; iFrame; auto
          ; iPureIntro; econstructor; eauto
          ; destruct HLinv as [Hreg_inv Hmem_inv]
          ; cbn in *.
          {
            rewrite (insert_commute _ _ dst) // (insert_commute _ _ dst) //.
            assert (HPC' := lookup_weaken _ _ _ _ HPC'' Hregs).

            eapply update_cur_version_reg_phys_log_cor_updates_src
              with (phm := mem) ; eauto; cycle 1.
            done.
            by rewrite lookup_insert_ne // lookup_insert_ne //.
            {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
              eapply not_overlap_word_leaL with (a2' := a_pc1)
              ; cycle 4
              ; first eapply (unique_in_machineL_not_overlap_word _ lr dst); eauto.
            }
            split; eauto.
            eapply lreg_corresponds_insert_respects; eauto.
            apply is_cur_lword_lea with (a := a1).
            eapply lreg_corresponds_read_iscur; eauto.
          }
          { eapply mem_phys_log_update ; eauto. }

      * (* src = PC *)
        simplify_map_eq.
        rewrite (insert_commute _ dst PC) //= insert_insert insert_commute //= in H'lregs'.
        (* we update the registers with their new value *)
        destruct (decide (dst = PC)) ; simplify_map_eq.
        (* dst ≠ PC *)
        iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
        iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
        ; first by simplify_map_eq.

        iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
        ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto].
        iExists _, lm', vmap_m'; iFrame; auto
        ; iPureIntro; econstructor; eauto
        ; destruct HLinv as [Hreg_inv Hmem_inv]
        ; cbn in *.
        {
            eapply update_cur_version_reg_phys_log_cor_updates_src with
            (phm := mem) (lwsrc := (LCap p1 b1 e1 a1 v) ); eauto; cycle 1.
            rewrite -/((next_version_lword (LCap p1 b1 e1 a_pc1 v))).
            eapply update_cur_version_region_local_update_lword ; eauto.
            apply is_cur_lword_lea with (a := a1).
            eapply lreg_corresponds_read_iscur; eauto.
            by rewrite lookup_insert_ne // lookup_insert_ne //.
            {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
            }
            split; eauto.
            eapply lreg_corresponds_insert_respects; eauto.
            by cbn.
          }
        { eapply mem_phys_log_update; [ | eauto | | eauto |..]; eauto. }
        { eapply update_cur_version_region_global_valid; eauto. }

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
        { destruct HLinv as [ [Hstrips Hcurreg] _].
          rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
        }

        rewrite Hlregs' in Hstep.
        match goal with
        | Hstep :
          match ?x with _ => _ end = (_,_) |- _ =>
            replace x with (None : option Conf) in Hstep
              by (destruct_lword lsrcv ; eauto)
        end.
        inversion Hstep.
        iSplitR "Hφ Hmap Hmem"
        ; [ iExists lr, lm, vmap; iFrame; auto
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
      2: { destruct HLinv as [ [Hstrips Hcurreg] _]
           ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
      }
      rewrite HuPC in Hstep; clear HuPC.
      inversion Hstep; clear Hstep ; simplify_map_eq.
      match goal with
      | Hstep : match ?x with _ => _ end = (_,_) |- _ =>
          match goal with
          | Hstep' : context f [ Some (?a,?b) ] |- _ =>
          replace x with (Some (a,b)) in H0
                by (destruct_lword lsrcv ; cbn in * ; try congruence)
          end
      end ; simplify_map_eq.

      iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto
      ; first by simplify_map_eq.

      iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
      ; [| iApply "Hφ" ; iFrame; iPureIntro; eapply IsUnique_success_false ; eauto].

      iExists _, lm, vmap; iFrame; auto
      ; iPureIntro; econstructor; eauto
      ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ]
      ; cbn in *
      ; [|split;eauto]
      .
      split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=.
      apply map_Forall_insert_2 ; [|by apply map_Forall_insert_2; cbn].
      rewrite HPC in HPC'' ; simplify_eq.
      eapply is_cur_word_change with (lw := (LCap p1 b1 e1 a1 v1)); eauto.
  Qed.

  (* Because I don't know the whole content of the memory (only a local view),
     any sucessful IsUnique wp-rule can have 2 outcomes:
     either the sweep success or the sweep fails.

    Importantly, we cannot derive any sweep success rule, because we would need
    the entire footprint of the registers/memory.
   *)

  Lemma wp_isunique_success
    (Ep : coPset)
    (pc_p : Perm) (pc_b pc_e pc_a pc_a' : Addr) (pc_v : Version)
    (lw : LWord)
    (p : Perm) (b e a : Addr) (v : Version)
    (lwdst : LWord) (lws : list LWord)
    (dst src : RegName) :

    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    pc_a ∉ finz.seq_between b e -> (* TODO is that necessary ? Or can I derive it ? *)
    (pc_a + 1)%a = Some pc_a' →
    length lws = finz.dist b e -> (* TODO change into =length (finz.seq_between b e)= *)

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ dst ↦ᵣ lwdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ lws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ dst ↦ᵣ LInt 1
        ∗ src ↦ᵣ LCap p b e a (v+1)
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]]
        ∗ [[ b , e ]] ↦ₐ{ (v+1) } [[ lws ]] )
           ∨
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ dst ↦ᵣ LInt 0
          ∗ src ↦ᵣ LCap p b e a v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ [[ b , e ]] ↦ₐ{ v } [[ lws ]] )
        }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca_notin Hpca Hlen_lws φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a & >Hmap) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hrmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_cons (λ _ la lw, la ↦ₐ lw)%I (pc_a, pc_v) lw with "[Hpc_a Hmap]")
      as "Hmmap"; iFrame.
    iDestruct (big_sepL2_to_big_sepM  with "Hmmap") as "Hmmap".
    { apply NoDup_cons ; split; [| apply NoDup_logical_region].
      intro Hcontra.
      apply elem_of_list_fmap in Hcontra.
      destruct Hcontra as (? & ? & ?) ; simplify_eq.
    }
    iApply (wp_isunique with "[$Hrmap Hmmap]"); eauto ; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as
      [ ? ? ? ? ? ? Hlwsrc Hlwsrc' Hupd Hincr_PC
      | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hincr_PC Hmem'
      | ? ? Hfail]
    ; cycle 2.
    - (* Fail : contradiction *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto; solve_addr.
    - (* Success true *)
      iApply "Hφ"; iLeft.

      (* Registers *)
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca.
      { eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq. }

      assert (
          (list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws))
            ⊆ mem') as Hmem'_be.
      {

        eapply is_valid_updated_lmemory_preserves_lmem_incl; eauto.
        { apply finz_seq_between_NoDup. }
        { by rewrite finz_seq_between_length. }
        {
          eapply is_valid_updated_lmemory_insert; eauto.
          eapply finz_seq_between_NoDup.
          { apply not_elem_of_list_to_map_1; cbn.
            intro Hcontra.
            rewrite fst_zip in Hcontra ; eauto; last (rewrite map_length finz_seq_between_length ; lia).
            apply elem_of_list_fmap in Hcontra.
            destruct Hcontra as (? & ? & ?); simplify_eq; lia.
          }
          { clear -Hlen_lws.
            eapply Forall_forall; intros a Ha.
            apply not_elem_of_list_to_map_1; cbn.
            intro Hcontra.
            rewrite fst_zip in Hcontra ; eauto; last (rewrite map_length finz_seq_between_length ; lia).
            apply elem_of_list_fmap in Hcontra.
            destruct Hcontra as (? & ? & ?); simplify_eq; lia.
          }
        }
      }
      assert (
          (list_to_map (zip (map (λ a : Addr, (a, v0+1)) (finz.seq_between b0 e0)) lws))
            ⊆ mem') as Hmem'_be_next
      .
      {
        (* TODO extract as a lemma *)
        eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
        assert (v' = v0+1 /\ (a' ∈ (finz.seq_between b0 e0))) as [? Ha'_in_be]; simplify_eq.
        { eapply list_to_map_zip_inv; eauto.
          apply finz_seq_between_NoDup.
          by rewrite finz_seq_between_length.
        }

        destruct Hupd.
        assert (
            (update_version_region_local
              (<[(pc_a, pc_v):=lw]>
                 (list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws)))
              (finz.seq_between b0 e0) v0) !! (a', v0 + 1) = Some lw'
          ).
        { rewrite update_version_region_local_preserves_lmem_next; eauto.

          { rewrite lookup_insert_ne //=; last (intro ; set_solver).
            erewrite list_to_map_zip_version; eauto.
            eapply finz_seq_between_NoDup.
            by rewrite finz_seq_between_length.
          }
          { eapply finz_seq_between_NoDup. }
          { rewrite lookup_insert_ne //=; last (intro ; set_solver).
            apply not_elem_of_list_to_map_1; cbn.
            intro Hcontra.
            rewrite fst_zip in Hcontra ; eauto; last (rewrite map_length finz_seq_between_length ; lia).
            apply elem_of_list_fmap in Hcontra.
            destruct Hcontra as (? & ? & ?); simplify_eq; lia.
          }
        }
        eapply lookup_weaken ; eauto.
      }

      rewrite -(insert_id mem' (pc_a, pc_v) lw); auto.
      iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame.

      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be; eauto.
      2: {
        clear -Hpca_notin Hlen_lws.
        eapply not_elem_of_list_to_map_1.
        intros Hcontra.
        rewrite fst_zip in Hcontra.
        2: { rewrite map_length finz_seq_between_length ; lia.  }
        apply elem_of_list_fmap in Hcontra.
        by destruct Hcontra as (? & ? & ?); simplify_eq.
      }

      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be).
      iSplitL "Hrange".
      {
        iApply big_sepM_to_big_sepL2; last iFrame.
        eapply NoDup_logical_region.
        by rewrite map_length finz_seq_between_length.
      }

      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next; eauto.
      2: {
        clear -Hpca_notin Hlen_lws.
        eapply not_elem_of_list_to_map_1.
        intros Hcontra.
        rewrite fst_zip in Hcontra.
        2: { rewrite map_length finz_seq_between_length ; lia.  }
        apply elem_of_list_fmap in Hcontra.
        by destruct Hcontra as (? & ? & ?); simplify_eq.
      }

      eapply delete_subseteq_list_r
        with (m3 := list_to_map (zip (map (λ a : Addr, (a, v0)) (finz.seq_between b0 e0)) lws))
        in Hmem'_be_next; eauto.
      2: { eapply update_logical_memory_region_disjoint.
           by rewrite finz_seq_between_length.
      }

      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be_next); iClear "Hmmap".
      iApply big_sepM_to_big_sepL2; last iFrame.
      eapply NoDup_logical_region.
      by rewrite map_length finz_seq_between_length.

    - (* Success false *)
      iApply "Hφ"; iRight.
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.
      iDestruct (big_sepM_insert with "Hmmap") as "[Hpc_a Hmmap]".
      { apply not_elem_of_list_to_map.
        rewrite fst_zip; [|rewrite map_length finz_seq_between_length; lia].
        intros Hcontra.
        apply elem_of_list_fmap_2 in Hcontra.
        destruct Hcontra as (? & Ha & ?); simplify_eq.
      }
      iFrame.
      iApply (big_sepM_to_big_sepL2 with "Hmmap").
      { apply NoDup_logical_region. }
      { by rewrite map_length finz_seq_between_length. }
  Qed.


  Lemma wp_isunique_success'
    (Ep : coPset)
    (pc_p : Perm) (pc_b pc_e pc_a pc_a' : Addr) (pc_v : Version)
    (lw : LWord)
    (p : Perm) (b e a : Addr) (v : Version)
    (lwdst : LWord)
    (dst src : RegName) :

    decodeInstrWL lw = IsUnique dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    pc_a ∉ finz.seq_between b e -> (* TODO is that necessary ? Or can I derive it ? *)
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ dst ↦ᵣ lwdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ dst ↦ᵣ LInt 1
        ∗ src ↦ᵣ LCap p b e a (v+1)
        ∗ (pc_a, pc_v) ↦ₐ lw
        ∗ (∃ lws , [[ b , e ]] ↦ₐ{ (v+1) } [[ lws ]] ))
           ∨
        ( PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ dst ↦ᵣ LInt 0
          ∗ src ↦ᵣ LCap p b e a v
          ∗ (pc_a, pc_v) ↦ₐ lw )
        }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca_notin Hpca φ) "(>HPC & >Hsrc & >Hdst & >Hpc_a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hrmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmmap".
    iApply (wp_isunique with "[$Hrmap Hmmap]"); eauto ; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }

    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmmap & Hrmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as
      [ ? ? ? ? ? ? Hlwsrc Hlwsrc' Hupd Hincr_PC
      | ? ? ? ? ? ? Hlwsrc Hlwsrc' Hincr_PC Hmem'
      | ? ? Hfail]
    ; cycle 2.
    - (* Fail : contradiction *)
      destruct Hfail; try incrementLPC_inv; simplify_map_eq; eauto; solve_addr.
    - (* Success true *)
      iApply "Hφ"; iLeft.

      (* Registers *)
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca.
      { eapply is_valid_updated_lmemory_notin_preserves_lmem; eauto; by simplify_map_eq. }

      assert (
          exists lws,
            length lws = length (finz.seq_between b0 e0) /\
            (list_to_map (zip (map (λ a : Addr, (a, v0+1)) (finz.seq_between b0 e0)) lws))
              ⊆ mem') as (lws & Hlen_lws & Hmem'_be_next).
      {
        destruct Hupd as [_ Hupd].
        eapply Forall_is_Some_list ; auto.
        apply finz_seq_between_NoDup.
      }

      rewrite -(insert_id mem' (pc_a, pc_v) lw); auto.
      iDestruct (big_sepM_insert_delete with "Hmmap") as "[HPC Hmmap]"; iFrame.

      eapply delete_subseteq_r with (k := ((pc_a, pc_v) : LAddr)) in Hmem'_be_next; eauto.
      2: {
        clear -Hpca_notin Hlen_lws.
        eapply not_elem_of_list_to_map_1.
        intros Hcontra.
        rewrite fst_zip in Hcontra.
        2: { rewrite map_length ; lia.  }
        apply elem_of_list_fmap in Hcontra.
        by destruct Hcontra as (? & ? & ?); simplify_eq.
      }
      iExists lws.

      iDestruct (big_sepM_insert_difference with "Hmmap") as "[Hrange Hmmap]"
      ; first (eapply Hmem'_be_next); iClear "Hmmap".
      iApply big_sepM_to_big_sepL2; last iFrame.
      eapply NoDup_logical_region.
      by rewrite map_length.

    - (* Success false *)
      iApply "Hφ"; iRight.
      rewrite /incrementLPC in Hincr_PC; simplify_map_eq.
      iExtractList "Hrmap" [PC; dst; src] as ["HPC"; "Hdst"; "Hsrc"].
      iClear "Hrmap".
      iFrame.
      iDestruct (big_sepM_insert with "Hmmap") as "[Hpc_a Hmmap]"
      ; first by simplify_map_eq.
      iFrame.
  Qed.

  (* TODO merge wp_opt from Dominique's branch and use it *)
  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
