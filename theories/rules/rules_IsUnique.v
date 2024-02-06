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

  (* Definition read_reg_inr' (lregs : LReg) (r : RegName) ot p b e a v := *)
  (*   match lregs !! r with *)
  (*     | Some (LCap p' b' e' a' v') *)
  (*       => (LCap p' b' e' a' v') = LCap p b e a v *)
  (*     | Some (LSealedCap ot' p' b' e' a' v') *)
  (*       => (LSealedCap ot' p' b' e' a' v') = (LSealedCap ot p b e a v) *)
  (*     | Some _ => True *)
  (*     | None => False end. *)

  (* TODO @Bastien rename *)
  (* Definition allow_access_map_or_true (r : RegName) (lregs : LReg) (lmem : LMem) : Prop := *)
  (*   exists ot p b e a v, read_reg_inr' lregs r ot p b e a v *)
  (*                ∧ if decide (lregs !! r = Some (LCap p b e a v) \/ lregs !! r = Some (LSealedCap ot p b e a v)) *)
  (*                  then Forall (fun a' => exists lw, lmem !! (a',v) = Some lw) (finz.seq_between b e) *)
  (*                  else True. *)

  (* Lemma allow_access_implies_memmap: *)
  (*   ∀ (r : RegName) (lmem : LMem) (lregs : LReg) (ot : OType) (p : Perm) (b e a : Addr) (v : Version), *)
  (*     allow_access_map_or_true r lregs lmem *)
  (*     → (lregs !! r = Some (LCap p b e a v) \/ lregs !! r = Some (LSealedCap ot p b e a v)) *)
  (*     (* TODO this is too strong, because it forbids the possibility *)
  (*        to update a word, even if we own part of the points-to. *)
  (*        Do we really need to own all the points-to of the region ? *)
  (*        I don't think so.... We just don't get the updated version... *)
  (*        I think ? *) *)
  (*     → Forall ( fun a => exists lw, lmem !! (a,v) = Some lw) (finz.seq_between b e). *)
  (* Proof. *)
  (*   intros r lmem lregs ot p b e a v HaAccess Hrv. *)
  (*   rewrite /allow_access_map_or_true /read_reg_inr' in HaAccess. *)
  (*   destruct HaAccess as (?&?&?&?&?&?& Hrinr & Hmem). *)
  (*   destruct Hrv as [Hrv | Hrv]. *)
  (*   all: rewrite Hrv in Hrinr; inversion Hrinr; subst. *)
  (*   all: case_decide as Hrega; [exact Hmem | contradiction Hrega]. *)
  (*   all: simplify_map_eq; (try by left) ; (try by right). *)
  (* Qed. *)

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
        which, one might notice, the version number changes.
   *)


  (* Helper lemma to avoid proof duplication *)
  Lemma mem_phys_log_update
    (reg : Reg) (mem : Mem)
    (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap)
    (src : RegName) (p : Perm) (b e a : Addr) (v : Version) :
    (* necessary for lreg_res_iscur *)
    reg_phys_log_corresponds reg lr cur_map ->
    (* necessary for unique_in_machine_no_accessL *)
    lr !! src = Some (LCap p b e a v) ->
    unique_in_machineL lm lr src (LCap p b e a v) ->

    (* necessary for update_cur_version... *)
    NoDup (finz.seq_between b e) ->
    update_cur_version_region_local lm cur_map (finz.seq_between b e)
    = (lm', cur_map') ->
    mem_phys_log_corresponds mem lm cur_map ->
    mem_phys_log_corresponds mem lm' cur_map'.
  Proof.
    intros.
    eapply update_cur_version_region_local_preserves_mem_phyc_cor; eauto.
    eapply unique_in_machine_no_accessL ; eauto.
    eapply lreg_read_iscur; eauto.
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
        ∗ (b+1, v+1) ↦ₐ lwb' ;; lwb' should be under an existential ? ...
                             ;; and note that =not (overlap lwb' (p,b,b+2,_,v))=
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
    iDestruct "Hσ1" as (lr lm cur_map) "(Hr & Hm & %HLinv)"; simpl in HLinv.

    (* Derive necessary register values in r *)
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have Hregs_pc := lookup_weaken _ _ _ _ HPC Hregs.
    specialize (indom_lregs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri dst) as [ldstv [Hldst' Hldst] ]. by set_solver+.
    odestruct (Hri src) as [lsrcv [Hlsrc' Hlsrc] ]. by set_solver+.

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
    destruct (is_lcap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *.
    { (* Fail : not a capability *)
      destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.
      all: simplify_map_eq.
      all: (iSplitR "Hφ Hmap Hmem"
            ; [ iExists lr, lm, cur_map; iFrame; auto
              | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_cap
           ]).
    }
    destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.

    { (* Case cap *)

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
        { destruct HLinv as [ [Hstrips Hcurreg] _].
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
      2: { destruct HLinv as [ [Hstrips Hcurreg] _]
           ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=
           ; erewrite insert_cap_lreg_strip ; eauto.
      }
      rewrite HuPC in Hstep; clear HuPC.
      inversion Hstep; clear Hstep ; simplify_map_eq.

      (* update version number of memory points-to *)
      assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup).

      pose proof
        (state_phys_log_cap_all_current _ _ _ _ _ _ _ _ _ _ _ HLinv Hlsrc)
        as HcurMap.
      pose proof
        (state_phys_log_last_version _ _ _ _ _ _ _ _ _ _ _ HLinv Hlsrc)
        as HmemMap_maxv.
      assert (Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) (finz.seq_between b e))
               as HmemMap.
      admit. (* TODO lemma, from HLinv and Hlsrc*)

      destruct (update_cur_version_word_region_global lmem lm cur_map (LCap p b e a v))
        as [lmem' vmap_mem'] eqn:Hupd_lmem
      ; rewrite /update_cur_version_word_region_local /= in Hupd_lmem.
      destruct (update_cur_version_word_region_local lm cur_map (LCap p b e a v))
        as [lm' vmap_m'] eqn:Hupd_lm
      ; rewrite /update_cur_version_word_region_local /= in Hupd_lm.

      iMod ((gen_heap_lmem_version_update lm lmem lm' lmem' ) with "Hm Hmem")
        as "[Hm Hmem]"; eauto.

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

          iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
          ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto].
          iExists _, lm', vmap_m'; iFrame; auto
          ; iPureIntro; econstructor; eauto
          ; destruct HLinv as [Hreg_inv Hmem_inv]
          ; cbn in *.
          {
            rewrite (insert_commute _ _ src) // (insert_commute _ _ src) //.
            eapply lookup_weaken in HPC'' ; eauto.
            replace reg with (<[ src := WCap p b e a ]> reg).
            2: { rewrite insert_id;auto. }
            do 2 (rewrite (insert_commute _ _ src) //).

            eapply update_cur_version_reg_phys_log_cor_updates_src with
            (phm := mem).
            eapply update_cur_version_region_local_update_lcap ; eauto.
            eapply lreg_read_iscur; eauto.
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
            eauto.
          }
          { eapply mem_phys_log_update ; eauto. }
          {

            Set Nested Proofs Allowed.
            Lemma update_cur_version_region_global_valid
              (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (v : Version) :
              NoDup la ->
              lmem ⊆ lm ->
              Forall (λ a0 : Addr, cur_map !! a0 = Some v) la ->
              Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
              Forall (λ a0 : Addr, lm !! (a0, v + 1) = None) la ->
              update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map') ->
              is_valid_updated_lmemory lmem la v lmem'.
            Proof.
              move: lmem lm lmem' cur_map cur_map' v.
              induction la as [|a la IHla]
              ; intros * HNoDup Hlmem_incl HcurMap HmemMap HmaxMap Hupd.
              - cbn in *; simplify_map_eq.
                split; cbn.
                set_solver.
                by apply Forall_nil.
              - rewrite NoDup_cons in HNoDup
                ; destruct HNoDup as [Ha_notin_la HNoDup_la].

                rewrite Forall_cons in HmemMap
                ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
                rewrite Forall_cons in HcurMap
                ; destruct HcurMap as [ Hcur_v HcurMap].
                rewrite Forall_cons in HmaxMap
                ; destruct HmaxMap as [ Hmax_v HmaxMap].

                apply update_cur_version_region_global_cons in Hupd
                ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).

                assert ( is_valid_updated_lmemory lmem la v lmem0) as Hvalid
                  by (eapply IHla ; eauto).
                (* destruct Hvalid. *)

                split.
                + cbn.
                  rewrite -/(update_version_region_local lmem la v).
                    destruct Hvalid as [Hupd' _].
                    assert (cur_map0 !! a = Some v) as Hcur0
                        by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).

                    Lemma update_cur_version_addr_global_notin_preserves_lmem
                      (lmem lm lmem' : LMem) (vmap vmap' : VMap)
                      (a a': Addr) (v :Version) (opt_lw : option LWord):
                      a ≠ a' ->
                      update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
                      lmem !! (a, v) = opt_lw ->
                      lmem' !! (a, v) = opt_lw.
                    Proof.
                      intros Hneq Hupd Hlmem.
                      rewrite /update_cur_version_addr_global in Hupd.
                      destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
                      destruct (lm !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
                      simplify_eq.
                      rewrite /update_lmemory_lword; simplify_eq.
                      rewrite lookup_insert_ne //=; intro ; simplify_eq; lia.
                    Qed.

                    Lemma update_cur_version_region_global_notin_preserves_lmem
                      (lmem lm lmem' : LMem) (vmap vmap' : VMap)
                      (la : list Addr) (a : Addr) (v :Version) (opt_lw : option LWord):
                      a ∉ la ->
                      update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
                      lmem !! (a, v) = opt_lw ->
                      lmem' !! (a, v) = opt_lw.
                    Proof.
                      move: lmem lm lmem' vmap vmap' a v opt_lw.
                      induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hlmem
                      ; first (by cbn in * ; simplify_map_eq).

                      rewrite not_elem_of_cons in Ha_notin_la
                      ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

                      apply update_cur_version_region_global_cons in Hupd
                      ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).

                      eapply update_cur_version_addr_global_notin_preserves_lmem
                        in Hupd0; eauto.
                    Qed.

                    Lemma update_cur_version_addr_global_preserves_content_lmem
                      (lmem lm lmem' : LMem) (vmap vmap' : VMap)
                      (a a': Addr) (v :Version) (opt_lw : option LWord):
                      update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
                      vmap !! a = Some v ->
                      lmem !! (a, v) = opt_lw ->
                      lmem' !! (a, v) = opt_lw.
                    Proof.
                      intros Hupd Hcur Hlmem.
                      rewrite /update_cur_version_addr_global in Hupd.
                      destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
                      destruct (lm !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
                      simplify_eq.
                      destruct (decide (a = a')) ; rewrite /update_lmemory_lword; simplify_eq.
                      rewrite lookup_insert_ne //=; intro ; simplify_eq; lia.
                      rewrite lookup_insert_ne //=; intro ; simplify_eq; lia.
                    Qed.

                    Lemma update_cur_version_region_global_preserves_content_lmem
                      (lmem lm lmem' : LMem) (vmap vmap' : VMap)
                      (la : list Addr) (a : Addr) (v :Version) (opt_lw : option LWord):
                      a ∉ la ->
                      update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
                      vmap !! a = Some v ->
                      lmem !! (a, v) = opt_lw ->
                      lmem' !! (a, v) = opt_lw.
                    Proof.
                      move: lmem lm lmem' vmap vmap' a v opt_lw.
                      induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hcur Hlmem
                      ; first (by cbn in * ; simplify_map_eq).

                      rewrite not_elem_of_cons in Ha_notin_la
                      ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

                      apply update_cur_version_region_global_cons in Hupd
                      ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).

                      eapply update_cur_version_addr_global_preserves_content_lmem
                        in Hupd0; eauto.
                      eapply update_cur_version_region_global_notin_preserves_cur_1; eauto.
                    Qed.

                    Lemma update_lmemory_lword_incl
                      (lmem : LMem) (a : Addr) (v : Version) (lw : LWord) :
                      lmem !! (a, v + 1) = None ->
                      (lmem ⊆ update_lmemory_lword lmem a v lw).
                    Proof.
                      intro Hmaxv.
                      rewrite /update_lmemory_lword.
                      apply insert_subseteq_r; eauto.
                    Qed.

                    Lemma update_cur_version_addr_global_incl_lmem
                      (lmem lm lmem': LMem) (vmap vmap' : VMap) (a : Addr) (v : Version) :
                      vmap !! a = Some v ->
                      lmem !! (a, v+1) = None ->
                      update_cur_version_addr_global lmem lm vmap a = (lmem', vmap') ->
                      lmem ⊆ lmem'.
                    Proof.
                      intros Hcur Hmaxv Hupd.
                      rewrite /update_cur_version_addr_global in Hupd.
                      rewrite Hcur in Hupd.
                      destruct (lm !! (a,v)) as [lwa|] eqn:Hlwa ; simplify_map_eq; last set_solver.
                      eapply update_lmemory_lword_incl ; eauto.
                    Qed.

                    (* Lemma update_version_addr_local_subseteq *)
                    (*   (lmem lm lmem0 lmem' : LMem) (cur_map0 cur_map': VMap) *)
                    (*   (a : Addr) (v : Version) (lwa : LWord) : *)
                    (*   lmem ⊆ lmem0 -> *)
                    (*   (* lmem !! (a, v) = Some lwa -> *) *)
                    (*   (* lm !! (a, v) = Some lwa -> *) *)
                    (*   cur_map0 !! a = Some v -> *)
                    (*   lmem0 !! (a, v + 1) = None -> *)
                    (*   update_cur_version_addr_global lmem0 lm cur_map0 a = (lmem', cur_map') -> *)
                    (*   update_version_addr_local lmem a v ⊆ lmem'. *)
                    (* Proof. *)
                    (*   intros Hlmem_incl Hlmem_a Hlm_a Hcur Hmaxv Hupd. *)
                    (*   rewrite /update_version_addr_local. *)
                    (*   assert (lmem ⊆ lmem') as Hlmem_incl''. *)
                    (*   { *)
                    (*     assert (lmem0 ⊆ lmem') as Hlmem0_incl *)
                    (*         by (eapply update_cur_version_addr_global_incl_lmem; eauto). *)
                    (*     apply (map_subseteq_spec lmem lmem'). *)
                    (*     intros [a' v'] lw Ha'. *)
                    (*     eapply lookup_weaken in Ha'; last (by eapply Hlmem_incl). *)
                    (*     by eapply lookup_weaken in Ha'; last (by eapply Hlmem0_incl). *)
                    (*   } *)
                    (*   rewrite Hlmem_a. *)
                    (*   (* destruct (lmem !! (a, v)) as [lw|] eqn:Hlwa; last assumption. *) *)
                    (*   rewrite /update_lmemory_lword. *)
                    (*   eapply insert_subseteq_l; last assumption. *)
                    (*   (* TODO should be a theorem *) *)
                    (*   rewrite /update_cur_version_addr_global in Hupd. *)
                    (*   rewrite Hcur in Hupd. *)
                    (*   rewrite Hlm_a in Hupd. *)

                    (*   (* destruct (lm !!(a, v)) eqn:H; simplify_map_eq. *) *)
                    (*   (* rewrite /update_lmemory_lword. *) *)
                    (*   (* rewrite /update_lmemory_lword in Hlmem_incl''. *) *)


                    (*   (* (* eapply lookup_weaken in Hlwa; last (by eapply Hlmem_incl'). *) *) *)
                    (*   (* (* rewrite Hlwa in Hupd; simplify_eq. *) *) *)
                    (*   (* rewrite /update_lmemory_lword. *) *)
                    (*   (* by simplify_map_eq. *) *)
                    (* Admitted. *)

                    (* assert (lmem0 !! (a, v+1) = None) as Hmax0_v. *)
                    (* admit. *)

                    (* assert (update_version_addr_local lmem0 a v ⊆ lmem'). *)
                    (* admit. *)
                    rewrite /update_version_addr_local.
                    assert (update_version_region_local lmem la v ⊆ lmem').
                    {
                      assert (update_version_region_local lmem la v ⊆ lmem0).
                      {


                        Lemma update_cur_version_addr_global_local
                          (lmem lm lmem' : LMem) (vmap vmap' : VMap)
                          (a : Addr) (v : Version) :
                          lmem ⊆ lm ->
                          lm !! (a, v + 1) = None ->
                          is_Some (lm !! (a, v)) ->
                          vmap !! a = Some v ->
                          update_cur_version_addr_global lmem lm vmap a = (lmem', vmap') ->
                          update_version_addr_local lmem a v ⊆ lmem'.
                        Proof.
                          intros Hlmem_incl Hmaxv [lw Hlw_a] Hcur Hupd.
                          rewrite /update_cur_version_addr_global Hcur Hlw_a in Hupd
                          ; simplify_eq.
                          rewrite /update_version_addr_local.
                          destruct (lmem !! (a, v)) eqn:?.
                          rewrite /update_lmemory_lword.
                          by eapply lookup_weaken in Heqo ; eauto ; rewrite Heqo in Hlw_a ; simplify_map_eq.
                          rewrite /update_lmemory_lword.
                          eapply lookup_weaken_None in Hmaxv; eauto.
                          eapply insert_subseteq_r; eauto.
                        Qed.

                      Lemma update_version_region_local_inv
                        (lmem : LMem) (la : list Addr) (a : Addr) (v : Version) (lw : LWord) :
                        a ∉ la ->
                        update_version_region_local lmem la v !! (a, v) = Some lw ->
                        lmem !! (a, v) = Some lw
                      .
                        Proof.
                          move: lmem a v lw.
                          induction la as [|a' la IHla] ; intros * Ha_notin_la Hupd
                          ; first (cbn in *; eauto).

                          apply not_elem_of_cons in Ha_notin_la
                          ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

                          rewrite /update_version_region_local /= in Hupd.
                          rewrite -/(update_version_region_local lmem la v) in Hupd.
                          eapply IHla ; eauto.


                          Lemma update_version_addr_local_lookup_neq
                            (lmem : LMem) (a a' : Addr) (v v': Version) :
                            a ≠ a' ->
                            update_version_addr_local lmem a v !! (a', v') = lmem !! (a', v')
                          .
                          Proof.
                            intros Hneq.
                            rewrite /update_version_addr_local.
                            destruct (lmem !! (a,v)); auto.
                            rewrite /update_lmemory_lword.
                            rewrite lookup_insert_ne //=; by intro ; simplify_eq.
                          Qed.
                          rewrite update_version_addr_local_lookup_neq in Hupd; eauto.
                        Qed.

                        Lemma update_cur_version_region_global_local
                          (lmem lm lmem' : LMem)
                          (vmap vmap' : VMap)
                          (la : list Addr)
                          (v : Version) :
                          NoDup la ->
                          lmem ⊆ lm ->
                          Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
                          Forall (λ a0 : Addr, vmap !! a0 = Some v) la ->
                          Forall (λ a0 : Addr, (lm !! (a0, v +1) = None)) la ->
                          update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
                          update_version_region_local lmem la v ⊆ lmem'.
                        Proof.
                          move: lmem lm lmem' vmap vmap' v.
                          induction la as [|a la IHla]
                          ; intros * HNoDup Hlmem_incl HmemMap HcurMap HmaxMap Hupd
                          ; first ( cbn in * ; simplify_map_eq ; by set_solver ).

                          apply NoDup_cons in HNoDup
                          ; destruct HNoDup as [Ha_notin_la HNoDup_la].
                          rewrite Forall_cons in HmemMap
                          ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
                          rewrite Forall_cons in HcurMap
                          ; destruct HcurMap as [ Hcur_v HcurMap].
                          rewrite Forall_cons in HmaxMap
                          ; destruct HmaxMap as [ Hmax_v HmaxMap].

                          apply update_cur_version_region_global_cons in Hupd
                          ; destruct Hupd as (lmem0 & vmap_mem0 & Hupd & Hupd0).

                          cbn.
                          rewrite -/(update_version_region_local lmem la v).
                          pose proof Hupd0 as Hupd0'.
                          eapply update_cur_version_addr_global_local in Hupd0 ; eauto.
                          3:{
                            eapply update_cur_version_region_global_notin_preserves_cur_1; eauto.
                          }
                          2:{
                            apply map_subseteq_spec.
                            intros a' lwa' Hlwa'.
                            assert (lmem !! a' = Some lwa').
                            admit. (* by inversion of Hupd *)
                            eapply lookup_weaken ; eauto.

                          }
                          assert ((update_version_region_local lmem la v) ⊆ lmem0).
                          { eapply IHla ; eauto. }
                          rewrite /update_version_addr_local.
                          assert (update_version_region_local lmem la v ⊆ lmem').
                          { rewrite /update_version_addr_local in Hupd0.
                            destruct (lmem0 !! (a, v)) eqn:?.
                            - rewrite /update_lmemory_lword in Hupd0.
                              eapply map_subseteq_spec.
                              intros a' lwa' Hlwa'.
                              assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
                                  (eapply lookup_weaken in Hlwa'; [|eassumption] ; by eauto).
                              assert (<[(a, v + 1):=l]> lmem0 !! (a,v) = Some l).
                              { rewrite lookup_insert_ne //=; intro ; simplify_eq; lia. }
                              destruct (decide (a' = (a,v))); simplify_map_eq.
                              + eapply update_version_region_local_inv in Hlwa' ; eauto.
                                eapply lookup_weaken in Hlwa'; last eapply Hlmem_incl.
                                rewrite Hlwa in Hlwa'; simplify_eq.
                                rewrite Hlmem0_a' in Heqo; simplify_eq.
                                eapply lookup_weaken; eauto.
                              + eapply lookup_weaken; [|eapply Hupd0]; eauto.
                                assert (lmem !! (a, v+1) = None ) by (eapply lookup_weaken_None; eauto).
                                assert (lmem0 !! (a, v+1) = None ).
                                {
                                  eapply update_cur_version_region_global_notin_preserves_lmem ;
                                    eauto.
                                }
                                assert (a' ≠ (a, v+1)).
                                { intro ; simplify_map_eq. rewrite H2 in Hlmem0_a' ; done. }
                                by simplify_map_eq.
                            - eapply map_subseteq_spec.
                              intros a' lwa' Hlwa'.
                              assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
                                  (eapply lookup_weaken in Hlwa'; [|eassumption] ; by eauto).
                              eapply lookup_weaken ; eauto.
                          }
                          destruct (update_version_region_local lmem la v !! (a, v)) eqn:?; auto.
                          { rewrite /update_lmemory_lword.
                            eapply insert_subseteq_l; auto.
                            eapply update_version_region_local_inv in Heqo ; eauto.
                            eapply lookup_weaken in Hlmem_incl ; eauto.
                            rewrite Hlmem_incl in Hlwa; simplify_map_eq.

                            eapply update_cur_version_region_global_preserves_content_lmem
                              in Heqo; eauto.
                            eapply update_cur_version_region_global_notin_preserves_cur_1
                              in Hcur_v; eauto.

                            rewrite /update_cur_version_addr_global in Hupd0'.
                            rewrite Hcur_v /= Hlmem_incl /= in Hupd0'.
                            simplify_eq.
                            by rewrite /update_lmemory_lword; simplify_map_eq.
                           }
                          Admitted.


                        eapply update_cur_version_region_global_local; eauto.
                      }
                      assert ( lmem0 ⊆ lmem').
                      { rewrite /update_cur_version_addr_global in Hupd0.
                        rewrite Hcur0 Hlwa in Hupd0; simplify_eq.
                        eapply update_lmemory_lword_incl.
                        eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
                        eapply lookup_weaken_None ; eauto.
                      }
                      rewrite map_subseteq_spec.
                      intros a' lw' Hlw'.
                      eapply lookup_weaken in H ; eauto.
                      eapply lookup_weaken in H0 ; eauto.
                    }
                    destruct (update_version_region_local lmem la v !! (a, v)) eqn:?; auto.
                    rewrite /update_lmemory_lword.
                    eapply insert_subseteq_l; auto.
                    assert (lmem !! (a,v) = Some l).
                    {
                        eapply update_version_region_local_inv; eauto.
                    }
                    assert (lmem0 !! (a,v) = Some l)
                    by (eapply update_cur_version_region_global_preserves_content_lmem; eauto).
                    eapply lookup_weaken in H0; eauto.
                    rewrite H0 in Hlwa ; simplify_map_eq.
                    rewrite /update_cur_version_addr_global in Hupd0.
                    rewrite Hcur0 in Hupd0.
                    rewrite H0 in Hupd0.
                    simplify_map_eq.
                    rewrite /update_lmemory_lword. by simplify_map_eq.

                    (* rewrite /update(* _version_region_local in Heqo. *) *)
                  (*   admit. *)
                  (*   ; last assumption. *)
                  (*   apply *)
                  (*   (* TODO should be OK to prove *) *)

                  (*   eapply *)
                  (*     (update_version_addr_local_subseteq *)
                  (*        (update_version_region_local lmem la v) *)
                  (*        lm lmem0 lmem' *)
                  (*        cur_map0 cur_map' *)
                  (*        a v); eauto. *)
                  (*   rewrite /update_version_region_local. *)
                  (*   rewrite /update_version_region_local. *)
                  (*   auto. Shelve. *)
                  (*   auto. *)
                  (*   3: eapply Hcur0. *)
                  (*   3: eapply Hmax0_v. *)
                  (*   eauto. *)
                  (*   eauto. *)
                  (*   2: eauto. *)
                  (*   eauto. *)
                  (*   (* TODO =update_version_region_local_subseteq=, *)
                  (*      i.e., should come from Hlmem_incl and Hupd *)
                  (*    *) *)
                  (*   Admitted. *)
                  (* admit. (* TODO, no *)t obvious *)
                + apply Forall_cons.
                  split.
                  * eapply update_cur_version_region_global_notin_preserves_cur_1 in Hcur_v ; eauto.
                    rewrite /update_cur_version_addr_global in Hupd0.
                    rewrite Hcur_v /= Hlwa in Hupd0 ; simplify_eq.
                    by rewrite /update_lmemory_lword ; simplify_map_eq.
                  * apply Forall_forall.
                    intros a' Ha'_in_la.
                    destruct Hvalid as [_ Hsome].
                    apply elem_of_list_lookup in Ha'_in_la.
                    destruct Ha'_in_la as [? Ha'].
                    eapply Forall_lookup in Hsome ; eauto.
                    destruct Hsome as [lwa0 Hlwa0].
                    exists lwa0.
                    admit. (* TODO not obvious *)

                    (*         Lemma update_cur_version_addr_global_preserves_content_lmem: *)
                    (*           ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) *)
                    (*             (v : Version) (lw : LWord), *)
                    (*             lmem ⊆ lm -> *)
                    (*             update_cur_version_addr_global lmem lm cur_map a' = (lmem', cur_map') -> *)
                    (*             lmem !! (a, v) = Some lw → *)
                    (*             lmem' !! (a, v) = Some lw. *)
                    (*         Proof. *)
                    (*           move=> lmem lm lmem' cur_map cur_map' a a' v lw Hlmem_incl Hupd Hlmem_a. *)
                    (*           rewrite /update_cur_version_addr_global /update_lmemory_lword in Hupd. *)
                    (*           destruct (cur_map !! a') as [va'|]; last by simplify_eq. *)
                    (*           destruct ( decide (a = a')) as [?|Hneq] ; simplify_map_eq. *)
                    (*           - eapply lookup_weaken in Hlmem_incl ; eauto. *)
                    (*             destruct (decide (v = va')) ; simplify_map_eq. *)
                    (*             + rewrite lookup_insert_ne //=. intro ; simplify_pair_eq; lia. *)
                    (*             + admit. *)
                    (*           - destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; last by *)
                    (*               simplify_eq. *)
                    (*             rewrite lookup_insert_ne //=. intro ; simplify_pair_eq; lia. *)
                    (*         Admitted. *)
                    (*         eapply update_cur_version_addr_global_preserves_content_lmem. *)
                    (*         3: eauto. 2: eauto. *)
                    (*                  in Hlwa0. *)
                    (* . *)
                    Admitted.
            eapply update_cur_version_region_global_valid; eauto.
          }

        ** (* src = dst *)
          admit.
    (*       iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
    (*         as "[Hr Hmap]"; eauto. *)
    (*       iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
    (*         as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)

    (*       iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
    (*       ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto]. *)
    (*       2: { rewrite insert_insert in H'lregs'. *)
    (*            rewrite insert_insert. done. *)
    (*       } *)
    (*       iExists _, lm', cur_map'; iFrame; auto *)
    (*       ; iPureIntro; econstructor; eauto *)
    (*       ; destruct HLinv as [Hreg_inv Hmem_inv] *)
    (*       ; cbn in *. *)
    (*       { *)
    (*         rewrite (insert_commute _ _ dst) // (insert_commute _ _ dst) //. *)
    (*         assert (HPC' := lookup_weaken _ _ _ _ HPC'' Hregs). *)

    (*         eapply update_cur_version_reg_phys_log_cor_updates_src *)
    (*           with (phm := mem) ; eauto. *)
    (*         done. *)
    (*         2: by rewrite lookup_insert_ne // lookup_insert_ne //. *)
    (*         2: { *)
    (*           eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
    (*           eapply not_overlap_word_leaL with (a2' := a1); eauto. *)
    (*           eapply (unique_in_machineL_not_overlap_word _ lr dst); eauto. *)
    (*         } *)
    (*         split; eauto. *)
    (*         eapply lreg_insert_respects_corresponds; eauto. *)
    (*         apply is_cur_word_lea with (a := a1). *)
    (*         eapply lreg_read_iscur; eauto. *)
    (*       } *)
    (*       { eapply mem_phys_log_update ; eauto. } *)

      * (* src = PC *)
        admit.
    (*     rewrite (insert_commute _ dst PC) //= insert_insert insert_commute //= in H'lregs'. *)
    (*     (* we update the registers with their new value *) *)
    (*     destruct (decide (dst = PC)) ; simplify_map_eq. *)
    (*     (* dst ≠ PC *) *)
    (*     iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
    (*     iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto *)
    (*     ; first by simplify_map_eq. *)

    (*     iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
    (*     ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto]. *)
    (*     iExists _, lm', cur_map'; iFrame; auto *)
    (*     ; iPureIntro; econstructor; eauto *)
    (*     ; destruct HLinv as [Hreg_inv Hmem_inv] *)
    (*     ; cbn in *. *)
    (*     { *)
    (*         eapply update_cur_version_reg_phys_log_cor_updates_src with *)
    (*         (phm := mem). *)
    (*         eapply update_cur_version_region_update_lcap ; eauto. *)
    (*         apply is_cur_word_lea with (a := a1). *)
    (*         eapply lreg_read_iscur; eauto. *)
    (*         2: by rewrite lookup_insert_ne // lookup_insert_ne //. *)
    (*         2: { *)
    (*           eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
    (*         } *)
    (*         split; eauto. *)
    (*         eapply lreg_insert_respects_corresponds; eauto. *)
    (*         by cbn. *)
    (*         eapply Hupd_lmem. *)
    (*       } *)
    (*     { eapply mem_phys_log_update ; eauto. } *)

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
      2: { destruct HLinv as [ [Hstrips Hcurreg] _]
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
      ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ]
      ; cbn in *
      ; [|split;eauto]
      .
      split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=.
      apply map_Forall_insert_2 ; [|by apply map_Forall_insert_2; cbn].
      rewrite HPC in HPC'' ; simplify_eq.
      eapply is_cur_word_cap_change; eauto.
      Unshelve. all: eauto.
      }
      {
        admit.
    (*     opose proof *)
    (*       (allow_access_implies_memmap src lmem lregs o p b e a v HaAccess _) *)
    (*       as HmemMap ; auto. *)

    (*     (* sweep success or sweep fail *) *)
    (*     destruct (sweep mem reg src) as [|] eqn:Hsweep ; cbn in Hstep. *)
    (*     - (* sweep is true *) *)
    (*       eapply sweep_true_specL in Hsweep; eauto. *)

    (*       destruct (incrementLPC (<[ dst := LInt 1 ]> *)
    (*                                 (<[ src := LSealedCap o p b e a (v + 1)]> lregs))) *)
    (*         as  [ lregs' |] eqn:Hlregs' *)
    (*       ; pose proof Hlregs' as H'lregs' *)
    (*       ; cycle 1. *)
    (*       { (* Failure: the PC could not be incremented correctly *) *)
    (*         apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'. *)
    (*         eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hlregs'. *)
    (*         2: { *)
    (*           rewrite /lreg_strip lookup_fmap. *)
    (*           apply fmap_is_Some. *)
    (*           destruct (decide (dst = PC)) ;  destruct (decide (src = PC)) ; simplify_map_eq; auto. *)
    (*         } *)
    (*         2: apply map_fmap_mono *)
    (*         ; apply (insert_mono _ ( <[src:=LSealedCap o p b e a (v + 1)]> lr)) *)
    (*         ; apply insert_mono ; eauto. *)
    (*         simplify_pair_eq. *)
    (*         replace ((λ lw : LWord, lword_get_word lw) <$> (<[dst:=LInt 1]> (<[src:=LSealedCap o p b e a (v + 1)]> lr))) *)
    (*           with (<[dst:= WInt 1]> reg) *)
    (*           in Hlregs' *)
    (*         ; cycle 1. *)
    (*         { destruct HLinv as [ [Hstrips Hcurreg] _]. *)
    (*           rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=. *)
    (*           rewrite -/(lword_get_word (LSealedCap o p b e a v)). *)
    (*           erewrite insert_reg_lreg_strip; eauto. *)
    (*         } *)
    (*         rewrite Hlregs' in Hstep. inversion Hstep. *)
    (*         iSplitR "Hφ Hmap Hmem" *)
    (*         ; [ iExists lr, lm, cur_map; iFrame; auto *)
    (*           | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_invalid_PC_true *)
    (*           ]. *)
    (*       } *)

    (*       (* PC has been incremented correctly *) *)
    (*       rewrite /update_reg /= in Hstep. *)
    (*       eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs' *)
    (*           as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->) *)
    (*       ; simplify_map_eq. *)
    (*       assert (dst <> PC) as Hdst by (intro ; simplify_map_eq). *)
    (*       assert (src <> PC) as Hsrc_neq_pc by (intro ; simplify_map_eq). *)
    (*       eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC. *)
    (*       2: apply map_fmap_mono *)
    (*       ; apply (insert_mono _ ( <[src:=LSealedCap o p b e a (v + 1)]> lr)) *)
    (*       ; apply insert_mono ; eauto. *)
    (*       replace ((λ lw, lword_get_word lw) <$> *)
    (*                <[dst:=LInt 1]> (<[src:=LSealedCap o p b e a (v + 1)]> lr)) *)
    (*         with (<[dst:=WInt 1]> reg) in HuPC. *)
    (*       2: { destruct HLinv as [ [Hstrips Hcurreg] _] *)
    (*            ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=. *)
    (*            rewrite -/(lword_get_word (LSealedCap o p b e a v)). *)
    (*            erewrite insert_reg_lreg_strip; eauto. *)
    (*       } *)
    (*       rewrite HuPC in Hstep; clear HuPC. *)
    (*       inversion Hstep; clear Hstep ; simplify_map_eq. *)

    (*       (* update version number of memory points-to *) *)
    (*       assert (HNoDup : NoDup (finz.seq_between b e)) by (apply finz_seq_between_NoDup). *)

    (*       Set Nested Proofs Allowed. *)
    (*       Lemma state_phys_log_scap_all_current *)
    (*         (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap) *)
    (*         (src : RegName) (o : OType) (p : Perm) (b e a : Addr) (v : Version) : *)
    (*         state_phys_log_corresponds phr phm lr lm cur_map -> *)
    (*         lr !! src = Some (LSealedCap o p b e a v) -> *)
    (*         Forall (λ a0 : Addr, cur_map !! a0 = Some v) (finz.seq_between b e). *)
    (*       Proof. *)
    (*         move=> [ [_ Hreg_current] Hmem_inv] Hlr_src. *)
    (*         pose proof (map_Forall_lookup_1 _ _ _ _ Hreg_current Hlr_src) as Hcur_src. *)
    (*         cbn in *. *)
    (*         by eapply Forall_forall. *)
    (*       Qed. *)

    (*       Lemma state_phys_log_last_version_s *)
    (*         (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap) *)
    (*         (src : RegName) (o : OType) (p : Perm) (b e a : Addr) (v : Version) : *)
    (*         state_phys_log_corresponds phr phm lr lm cur_map -> *)
    (*         lr !! src = Some (LSealedCap o p b e a v) -> *)
    (*         Forall (λ a0 : Addr, lm !! (a0, v+1) = None) (finz.seq_between b e). *)
    (*       Proof. *)
    (*         move=> [ [_ Hreg_current] Hmem_inv] Hlr_src. *)
    (*         pose proof (map_Forall_lookup_1 _ _ _ _ Hreg_current Hlr_src) as Hcur_src. *)
    (*         cbn in *. *)
    (*         apply Forall_forall. *)
    (*         intros a0 Ha0_inbounds. *)
    (*         apply Hcur_src in Ha0_inbounds. *)
    (*         assert (is_cur_addr (a0, v) cur_map) as Hcur_a0 by done. *)

    (*         destruct (lm !! (a0, v + 1)) eqn:Hv'. 2: done. *)
    (*         destruct Hmem_inv as [Hroot Hcur]. *)
    (*         eapply map_Forall_lookup_1 in Hroot; eauto. *)
    (*         destruct Hroot as (cur_v & Hcur_v & cur & Hsome & Hmaxv). *)
    (*         cbn in *. *)

    (*         eapply map_Forall_lookup_1 in Hcur; eauto. *)
    (*         destruct Hcur as (lw & Hlm & _) ; cbn in *. *)
    (*         eapply is_cur_addr_same in Hcur_a0; eauto; simplify_eq. *)
    (*         lia. *)
    (*       Qed. *)

    (*       pose proof *)
    (*         (state_phys_log_scap_all_current _ _ _ _ _ _ _ _ _ _ _ _ HLinv Hlsrc) *)
    (*         as HcurMap. *)
    (*       pose proof *)
    (*         (state_phys_log_last_version_s _ _ _ _ _ _ _ _ _ _ _ _ HLinv Hlsrc) *)
    (*         as HmemMap_maxv. *)

    (*       destruct (update_cur_version_word_region lmem cur_map (LCap p b e a v)) *)
    (*         as [ [lmem' cur_map']|] eqn:Hupd_lm *)
    (*       ; rewrite /update_cur_version_word_region /= in Hupd_lm *)
    (*       ; cycle 1. *)
    (*       { *)
    (*         exfalso. *)
    (*         apply eq_None_not_Some in Hupd_lm. *)
    (*         apply Hupd_lm. *)
    (*         eapply update_cur_version_region_Some; eauto. *)
    (*       } *)

    (*       pose proof Hupd_lm as Hupd_lmem. *)
    (*       eapply update_cur_version_region_mono in Hupd_lmem ; eauto. *)
    (*       destruct Hupd_lmem as (lm' & Hupd_lmem & Hmem'). *)

    (*       iMod ((gen_heap_lmem_version_update lm lmem lm' lmem' ) with "Hm Hmem") *)
    (*         as "[Hm Hmem]"; eauto. *)

    (*       assert (update_version_word_region lmem (LSealedCap o p b e a v) = Some lmem'). *)
    (*       { *)
    (*         Lemma update_cur_version_region_implies_next_version_s *)
    (*           (lm lm' : LMem) (cur_map cur_map': VMap) *)
    (*           (o : OType) (p : Perm) (b e a : Addr) (v : Version) : *)
    (*           is_cur_word (LSealedCap o p b e a v) cur_map -> *)
    (*           update_cur_version_region lm cur_map (finz.seq_between b e) = Some (lm', cur_map') -> *)
    (*           update_version_word_region lm (LSealedCap o p b e a v) = Some lm'. *)
    (*         Proof. *)
    (*           intros Hcur_word Hupd. *)
    (*           eapply update_cur_version_region_implies_next_version_gen; eauto. *)
    (*           apply finz_seq_between_NoDup. *)
    (*         Qed. *)
    (*         eapply update_cur_version_region_implies_next_version_s; eauto. *)
    (*         destruct HLinv as [Hinv_reg _]. *)
    (*         eapply lreg_read_iscur; eauto. *)
    (*       } *)

    (*       destruct (decide (src = dst)) ; simplify_map_eq ; cycle 1. *)
    (*       * (* src <> dst *) *)
    (*           iMod ((gen_heap_update_inSepM _ _ src (LSealedCap o p b e a (v + 1))) with "Hr Hmap") *)
    (*             as "[Hr Hmap]"; eauto. *)
    (*           iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
    (*             as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)
    (*           iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
    (*             as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)

    (*           iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
    (*           ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto]. *)
    (*           iExists _, lm', cur_map'; iFrame; auto *)
    (*           ; iPureIntro; econstructor; eauto *)
    (*           ; destruct HLinv as [Hreg_inv Hmem_inv] *)
    (*           ; cbn in *. *)
    (*           { *)
    (*             rewrite (insert_commute _ _ src) // (insert_commute _ _ src) //. *)
    (*             eapply lookup_weaken in HPC'' ; eauto. *)
    (*             replace reg with (<[ src := WSealed o (SCap p b e a) ]> reg). *)
    (*             2: { rewrite insert_id;auto. } *)
    (*             do 2 (rewrite (insert_commute _ _ src) //). *)

    (*             Lemma update_cur_version_reg_phys_log_cor_updates_src_s *)
    (*               (phr : Reg) (phm : Mem) (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap) *)
    (*               (src : RegName) (o : OType) (p : Perm) (b e a : Addr) ( v : Version ) (lw : LWord) : *)
    (*               is_cur_word lw cur_map' -> *)
    (*               state_phys_log_corresponds phr phm lr lm cur_map -> *)
    (*               lr !! src = Some (LSealedCap o p b e a v) -> *)
    (*               unique_in_machineL lm lr src (LSealedCap o p b e a v) -> *)
    (*               update_cur_version_region lm cur_map (finz.seq_between b e) *)
    (*               = Some (lm', cur_map') -> *)
    (*               reg_phys_log_corresponds (<[src:= (lword_get_word lw)]> phr) (<[src:= lw]> lr) cur_map'. *)
    (*             Proof. *)
    (*               move=> Hcur_lw [Hreg_inv Hmem_inv] Hlr_src Hunique Hupd. *)
    (*               split. *)
    (*               - rewrite /lreg_strip fmap_insert /= -/(lreg_strip lr). *)
    (*                 by replace phr with (lreg_strip lr) by (by destruct Hreg_inv as [? _]). *)
    (*               - rewrite -insert_delete_insert. *)
    (*                 eapply lreg_insert_respects_corresponds with (phr := (delete src phr)). *)
    (*                 2: { by cbn. } *)
    (*                 destruct Hreg_inv as [Hstrip Hcur_reg]. *)
    (*                 split. *)
    (*                 + by rewrite /lreg_strip fmap_delete -/(lreg_strip lr) Hstrip. *)
    (*                 + apply map_Forall_lookup_2. *)
    (*                   intros r lw' Hr. *)
    (*                   destruct (decide (r = src)); subst. *)
    (*                   rewrite lookup_delete in Hr; congruence. *)
    (*                   rewrite lookup_delete_ne in Hr; eauto. *)
    (*                   apply Hunique in Hlr_src. destruct Hlr_src as [Hunique_reg _]. *)
    (*                   rewrite /unique_in_registersL in Hunique_reg. *)
    (*                   eapply map_Forall_lookup_1 in Hunique_reg ; eauto. *)
    (*                   rewrite decide_False in Hunique_reg; auto. *)
    (*                   eapply map_Forall_lookup_1 in Hcur_reg ; eauto. *)
    (*                   eapply update_cur_version_notin_is_cur_word ; eauto. *)
    (*                   Unshelve. all: auto. *)
    (*             Qed. *)

    (*             eapply update_cur_version_reg_phys_log_cor_updates_src_s with *)
    (*               (phm := mem). *)
    (*             Lemma update_cur_version_region_update_lscap *)
    (*               (lm lm' : LMem) (cur_map cur_map' : VMap) *)
    (*               (o : OType) (p : Perm) (b e a : Addr) (v : Version) : *)
    (*               update_cur_version_region lm cur_map (finz.seq_between b e) = Some (lm', cur_map') -> *)
    (*               is_cur_word (LSealedCap o p b e a v) cur_map -> *)
    (*               is_cur_word (LSealedCap o p b e a (v + 1)) cur_map'. *)
    (*             Proof. *)
    (*               move=> Hupd Hcur. *)
    (*               rewrite -/(update_version_lword (LSealedCap o p b e a v)). *)
    (*               eapply update_cur_version_word_region_update_lword; cbn ; eauto. *)
    (*             Qed. *)

    (*             eapply update_cur_version_region_update_lscap; eauto. *)
    (*             eapply lreg_read_iscur; eauto. *)
    (*             2: by rewrite lookup_insert_ne // lookup_insert_ne //. *)
    (*             2: { *)
    (*               eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
    (*               Lemma not_overlap_word_leaL *)
    (*                 (lw : LWord) (p : Perm) (b e a a' : Addr) (v : Version) : *)
    (*                 ¬ overlap_wordL lw (LCap p b e a v) -> *)
    (*                 ¬ overlap_wordL lw (LCap p b e a' v). *)
    (*               Proof. *)
    (*                 move=> Hno_overlap Hoverlap. *)
    (*                 apply Hno_overlap. *)
    (*                 rewrite /overlap_wordL ; rewrite /overlap_wordL in Hoverlap *)
    (*                 ; cbn in *; done. *)
    (*               Qed. *)

    (*               eapply not_overlap_word_leaL with (a' := a1); eauto. *)
    (*               eapply (unique_in_machineL_not_overlap_word _ _ src PC); eauto. *)

    (*               eapply unique_in_machineL_insert_reg; eauto *)
    (*               ; try by simplify_map_eq. *)
    (*             } *)
    (*             split; eauto. *)
    (*             eapply lreg_insert_respects_corresponds; eauto. *)
    (*             eapply lreg_insert_respects_corresponds; eauto. *)
    (*             by cbn. *)
    (*             apply is_cur_word_lea with (a := a1). *)
    (*             eapply lreg_read_iscur; eauto. *)
    (*             eauto. *)
    (*           } *)
    (*           { *)
    (*             Lemma mem_phys_log_update_s *)
    (*               (reg : Reg) (mem : Mem) *)
    (*               (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap) *)
    (*               (src : RegName) (o : OType) (p : Perm) (b e a : Addr) (v : Version) : *)
    (*               (* necessary for lreg_res_iscur *) *)
    (*               reg_phys_log_corresponds reg lr cur_map -> *)
    (*               (* necessary for unique_in_machine_no_accessL *) *)
    (*               lr !! src = Some (LSealedCap o p b e a v) -> *)
    (*               unique_in_machineL lm lr src (LSealedCap o p b e a v) -> *)

    (*               (* necessary for update_cur_version... *) *)
    (*               NoDup (finz.seq_between b e) -> *)
    (*               update_cur_version_region lm cur_map (finz.seq_between b e) *)
    (*               = Some (lm', cur_map') -> *)
    (*               mem_phys_log_corresponds mem lm cur_map -> *)
    (*               mem_phys_log_corresponds mem lm' cur_map'. *)
    (*             Proof. *)
    (*               intros. *)
    (*               eapply update_cur_version_region_preserves_mem_phyc_cor; eauto. *)

    (*               Lemma unique_in_machine_no_accessL_s *)
    (*                 (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap) (src : RegName) *)
    (*                 (o : OType) (p : Perm) (b e a : Addr) ( v : Version ) : *)
    (*                 mem_phys_log_corresponds phm lm cur_map -> *)
    (*                 lr !! src = Some (LSealedCap o p b e a v) -> *)
    (*                 is_cur_word (LSealedCap o p b e a v) cur_map -> *)
    (*                 unique_in_machineL lm lr src (LSealedCap o p b e a v) -> *)
    (*                 Forall *)
    (*                   (λ a' : Addr, lmem_not_access_addrL lm cur_map a') *)
    (*                   (finz.seq_between b e). *)
    (*               Proof. *)
    (*                 move=> Hmem_inv Hlr_src His_cur Hunique. *)
    (*                 apply Forall_forall. *)
    (*                 move=> a' Ha'. *)
    (*                 pose proof (is_cur_word_lea cur_map p b e a a' v His_cur) as His_cur'. *)
    (*                 assert (Hcur_a': is_cur_addr (a',v) cur_map). *)
    (*                 { eapply (cur_lword_cur_addr _ _ b e) ; eauto; cycle 1. *)
    (*                   apply withinBounds_true_iff. *)
    (*                   apply elem_of_finz_seq_between in Ha'. *)
    (*                   solve_addr. *)
    (*                   rewrite /is_lword_version //=. *)
    (*                 } *)

    (*                 rewrite /unique_in_machineL in Hunique. *)
    (*                 specialize (Hunique Hlr_src). *)
    (*                 destruct Hunique as [Hunique_reg Hunique_mem]. *)
    (*                 eapply map_Forall_impl ; first eapply Hunique_mem. *)
    (*                 move=> [a0 v0] lw0 Hlast_v Hcur_v0. *)
    (*                 eapply no_overlap_word_no_access_addrL ; eauto. *)
    (*                 eapply Hlast_v. *)
    (*                 eapply mem_phys_log_cur_addr_last_version_1; eauto. *)
    (*                 Unshelve. all: auto. *)
    (*               Qed. *)

    (*               eapply unique_in_machine_no_accessL_s ; eauto. *)
    (*               eapply lreg_read_iscur; eauto. *)
    (*             Qed. *)

    (*             eapply mem_phys_log_update_s ; eauto. } *)

    (*         * (* src = dst *) *)
    (*           iMod ((gen_heap_update_inSepM _ _ dst (LInt 1)) with "Hr Hmap") *)
    (*             as "[Hr Hmap]"; eauto. *)
    (*           iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap") *)
    (*             as "[Hr Hmap]"; eauto ; first by simplify_map_eq. *)

    (*           iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
    (*           ; [| iApply "Hφ" ; iFrame; iPureIntro; econstructor; eauto]. *)
    (*           2: { rewrite insert_insert in H'lregs'. *)
    (*                rewrite insert_insert. done. *)
    (*           } *)
    (*           iExists _, lm', cur_map'; iFrame; auto *)
    (*           ; iPureIntro; econstructor; eauto *)
    (*           ; destruct HLinv as [Hreg_inv Hmem_inv] *)
    (*           ; cbn in *. *)
    (*           { *)
    (*             rewrite (insert_commute _ _ dst) // (insert_commute _ _ dst) //. *)
    (*             assert (HPC' := lookup_weaken _ _ _ _ HPC'' Hregs). *)

    (*             eapply update_cur_version_reg_phys_log_cor_updates_src_s *)
    (*               with (phm := mem) ; eauto. *)
    (*             done. *)
    (*             2: by rewrite lookup_insert_ne // lookup_insert_ne //. *)
    (*             2: { *)
    (*               eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq. *)
    (*               eapply not_overlap_word_leaL with (a' := a1); eauto. *)
    (*               eapply (unique_in_machineL_not_overlap_word _ lr dst); eauto. *)
    (*             } *)
    (*             split; eauto. *)
    (*             eapply lreg_insert_respects_corresponds; eauto. *)
    (*             apply is_cur_word_lea with (a := a1). *)
    (*             eapply lreg_read_iscur; eauto. *)
    (*           } *)
    (*           { eapply mem_phys_log_update_s ; eauto. } *)

    (*     - (* sweep = false *) *)

    (*       destruct (incrementLPC (<[ dst := LInt 0 ]> lregs)) *)
    (*         as  [ lregs' |] eqn:Hlregs' *)
    (*       ; pose proof Hlregs' as H'lregs' *)
    (*       ; cycle 1. *)
    (*       {  (* Failure: the PC could not be incremented correctly *) *)
    (*         apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'. *)
    (*         eapply updatePC_fail_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in Hlregs'. *)
    (*         2: { *)
    (*           rewrite /lreg_strip lookup_fmap. *)
    (*           apply fmap_is_Some. *)
    (*           destruct (decide (dst = PC)) ; simplify_map_eq; auto. *)
    (*         } *)
    (*         2: apply map_fmap_mono ; apply insert_mono ; eauto. *)
    (*         replace ((λ lw : LWord, lword_get_word lw) <$> (<[dst:=LInt 0]> lr)) *)
    (*           with (<[dst:= WInt 0]> reg) *)
    (*           in Hlregs' *)
    (*         ; cycle 1. *)
    (*         { destruct HLinv as [ [Hstrips Hcurreg] _]. *)
    (*           rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=. *)
    (*         } *)

    (*         rewrite Hlregs' in Hstep. inversion Hstep. *)
    (*         iSplitR "Hφ Hmap Hmem" *)
    (*         ; [ iExists lr, lm, cur_map; iFrame; auto *)
    (*           | iApply "Hφ" ; iFrame ; iFailCore IsUnique_fail_invalid_PC_false *)
    (*           ]. *)
    (*       } *)

    (*       (* PC has been incremented correctly *) *)
    (*       rewrite /update_reg /= in Hstep. *)
    (*       eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs' *)
    (*           as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->) *)
    (*       ; simplify_map_eq. *)
    (*       assert (dst <> PC) as Hdst by (intro ; simplify_map_eq). *)
    (*       eapply updatePC_success_incl with (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC. *)
    (*       2: apply map_fmap_mono ; apply insert_mono ; eauto. *)
    (*       replace ((λ lw, lword_get_word lw) <$> <[dst:=LInt 0]> lr) *)
    (*         with (<[dst:=WInt 0]> reg) in HuPC. *)
    (*       2: { destruct HLinv as [ [Hstrips Hcurreg] _] *)
    (*            ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=. *)
    (*       } *)
    (*       rewrite HuPC in Hstep; clear HuPC. *)
    (*       inversion Hstep; clear Hstep ; simplify_map_eq. *)

    (*       iMod ((gen_heap_update_inSepM _ _ dst ) with "Hr Hmap") as "[Hr Hmap]"; eauto. *)
    (*       iMod ((gen_heap_update_inSepM _ _ PC ) with "Hr Hmap") as "[Hr Hmap]"; eauto *)
    (*       ; first by simplify_map_eq. *)

    (*       iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem" *)
    (*       ; [| iApply "Hφ" ; iFrame; iPureIntro; eapply IsUnique_success_false ; eauto]. *)

    (*       iExists _, lm, cur_map; iFrame; auto *)
    (*       ; iPureIntro; econstructor; eauto *)
    (*       ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ] *)
    (*       ; cbn in * *)
    (*       ; [|split;eauto] *)
    (*       . *)
    (*       split; first by rewrite -Hstrips /lreg_strip !fmap_insert /=. *)
    (*       apply map_Forall_insert_2 ; [|by apply map_Forall_insert_2; cbn]. *)
    (*       rewrite HPC in HPC'' ; simplify_eq. *)
    (*       eapply is_cur_word_cap_change; eauto. *)
    (*       Unshelve. all: eauto. *)
      }
  Admitted.

  (* Because I don't know the whole content of the memory (only a local view),
     any sucessful IsUnique wp-rule can have 2 outcomes:
     either the sweep success or the sweep fails.

    Importantly, we cannot derive any sweep success rule, because we would need
    the entire footprint of the registers/memory.
   *)

  (* Lemma update_version_word_region_cons_no_access_gen *)
  (*   (lm lm' : LMem) (a : Addr) (la : list Addr) (v v' : Version) (lw : LWord): *)
  (*   NoDup la -> *)
  (*   a ∉ la -> *)
  (*   foldr *)
  (*     (λ (a : Addr) (upd_opt : option LMem), *)
  (*       upd_opt ≫= (λ lmem', update_version_addr lmem' a v') *)
  (*     ) *)
  (*     (Some (<[(a,v):=lw]> lm)) *)
  (*     la = Some lm' *)
  (*   -> ∃ lm'', *)
  (*       foldr *)
  (*         (λ (a : Addr) (upd_opt : option LMem), *)
  (*           upd_opt ≫= (λ lmem', update_version_addr lmem' a v') *)
  (*         ) *)
  (*         (Some lm) la = Some lm'' *)
  (*       ∧ lm' = <[(a,v):=lw]> lm''. *)
  (* Proof. *)
  (*   move: lm lm' a v v' lw. *)
  (*   induction la as [|a la Hla]; intros ? ? a' * HNoDup Ha'_notin_la Hupd *)
  (*   ; cbn in * ; simplify_eq. *)
  (*   - eexists ; split ; eauto. *)
  (*   - apply NoDup_cons in HNoDup *)
  (*     ; destruct HNoDup as [Ha_notin_la HNoDup]. *)

  (*     apply not_elem_of_cons in Ha'_notin_la *)
  (*     ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la]. *)

  (*     apply bind_Some in Hupd. *)
  (*     destruct Hupd as (lm0 & Hupd & Hlm'). *)
  (*     rewrite /update_version_addr in Hlm'. *)
  (*     destruct (lm0 !! (a, v')) as [lw0|] eqn:Heq_lm0 *)
  (*     ; cbn in * ; simplify_eq. *)

  (*     eapply Hla in Hupd; eauto. *)
  (*     destruct Hupd as (lm0' & Hupd & ->). *)
  (*     exists (<[(a, v' + 1):=lw0]> lm0'). *)
  (*     split; simplify_map_eq ; eauto. *)
  (*     + rewrite /update_version_addr. *)
  (*       rewrite lookup_insert_ne in Heq_lm0 ; [|intro ; simplify_eq]. *)
  (*       by rewrite Heq_lm0; cbn. *)
  (*     + rewrite insert_commute //. intro ; simplify_eq. *)
  (* Qed. *)

  (* Lemma update_version_word_region_cons_no_access *)
  (*   (lm lm' : LMem) (la : LAddr) (lw lwsrc : LWord) : *)
  (*   update_version_word_region (<[ la := lw ]> lm) lwsrc = Some lm' -> *)
  (*   ¬ (word_access_addrL (laddr_get_addr la) lwsrc) -> *)
  (*   exists lm'', (update_version_word_region lm lwsrc) = Some lm'' *)
  (*           /\ lm' = <[ la := lw ]> lm''. *)
  (* Proof. *)
  (*   intros Hupd Hno_access. *)
  (*   destruct la as [a' v']. *)
  (*   rewrite /update_version_word_region in Hupd. *)
  (*   destruct_lword lwsrc ; try (by simplify_map_eq ; eexists ; eauto). *)
  (*   all: eapply update_version_word_region_cons_no_access_gen in Hupd; *)
  (*     [| apply finz_seq_between_NoDup *)
  (*     | cbn in *; intros Hcontra ; apply elem_of_finz_seq_between in Hcontra; done]. *)
  (*   all: destruct Hupd as (lm'' & Hupd & ->). *)
  (*   all: exists lm''; split ; eauto. *)
  (* Qed. *)

  (* Lemma update_version_word_preserves_lword *)
  (*   (lm lmem : LMem) (la : list Addr) (a : Addr) (v : Version) (lw lw' : LWord) *)
  (*   : *)
  (*   foldr *)
  (*     (λ (a : Addr) (upd_opt : option LMem), *)
  (*       upd_opt ≫= (λ lmem', update_version_addr lmem' a v)) *)
  (*     (Some (<[(a, v):= lw]> lmem)) la = *)
  (*     Some lm -> *)
  (*   lm !! (a, v) = Some lw' -> *)
  (*   lw = lw'. *)
  (* Proof. *)
  (*   move: lm lmem a v lw lw'. *)
  (*   induction la as [| a la Hla] ; intros * Hupd Hlookup *)
  (*   ; cbn in * ; simplify_map_eq ; first done. *)
  (*   apply bind_Some in Hupd. *)
  (*   destruct Hupd as (lm0 & Hupd & Hlm). *)
  (*   rewrite /update_version_addr in Hlm. *)
  (*   destruct (lm0 !! (a,v)) as [lw0|] eqn:Heq_lm0; cbn in * ; simplify_eq. *)

  (*   eapply Hla in Hupd; eauto. *)
  (*   rewrite lookup_insert_ne // in Hlookup. *)
  (*   intro ; simplify_eq; lia. *)
  (* Qed. *)

  (* Lemma update_version_word_region_insert *)
  (*   (lm lmem : LMem) (la : list Addr) (a : Addr) (v : Version) (w : LWord) : *)
  (*   a ∉ la -> *)
  (*   foldr *)
  (*     (λ (a : Addr) (upd_opt : option LMem), *)
  (*       upd_opt ≫= (λ lmem', update_version_addr lmem' a v)) *)
  (*     (Some (<[(a, v):=w]> lmem)) *)
  (*     la = Some lm -> *)
  (*   exists lm', *)
  (*     foldr *)
  (*       (λ (a : Addr) (upd_opt : option LMem), *)
  (*         upd_opt ≫= (λ lmem', update_version_addr lmem' a v)) *)
  (*       (Some lmem) *)
  (*       la = Some lm' *)
  (*     /\ lm = <[(a, v):=w]> lm'. *)
  (* Proof. *)
  (*   move: lm lmem a v w. *)
  (*   induction la as [|a la Hla] ; intros * Hnot_in Hupd; cbn in * *)
  (*   ; simplify_map_eq; first set_solver. *)

  (*   apply not_elem_of_cons in Hnot_in; destruct Hnot_in as [Hneq Hnot_in]. *)

  (*   apply bind_Some in Hupd. *)
  (*   destruct Hupd as ( lm' & Hupd & Hlm ). *)
  (*   rewrite /update_version_addr in Hlm. *)
  (*   destruct (lm' !! (a, v)) as [lw|] eqn:Heq_lm; cbn in * ; simplify_eq. *)
  (*   eapply Hla in Hupd; auto. *)
  (*   destruct Hupd as ( lm0 & Hupd & -> ). *)

  (*   exists (<[(a, v + 1):=lw]> lm0). *)
  (*   split ; cycle 1. *)
  (*   rewrite insert_commute //=; intro ; simplify_eq. *)

  (*   apply bind_Some. *)
  (*   exists (<[(a, v):=lw]> lm0). *)
  (*   rewrite lookup_insert_ne in Heq_lm ; [| intro ; simplify_eq ; lia]. *)
  (*   rewrite /update_version_addr. *)
  (*   split; cycle 1; simplify_map_eq ; rewrite (insert_id _ (a,v)); auto. *)
  (* Qed. *)

  (* Lemma update_version_word_region_access_region_gen *)
  (*   (lm : LMem) (lws : list LWord) (v : Version) (la : list Addr) : *)
  (*   NoDup la -> *)
  (*   length lws = length la -> *)
  (*   foldr *)
  (*     (λ (a : Addr) (upd_opt : option LMem), *)
  (*       upd_opt ≫= (λ lmem', update_version_addr lmem' a v)) *)
  (*     (Some (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws))) *)
  (*     la = Some lm -> *)
  (*   lm = (list_to_map *)
  (*           ((zip (map (λ a : Addr, (a, v+1)) la) lws) *)
  (*              ++ (zip (map (λ a : Addr, (a, v)) la) lws)) *)
  (*        ). *)
  (* Proof. *)
  (*   move: lm lws v. *)
  (*   induction la as [| a la Hla]; intros * HNoDup Hlen_eq Hupd *)
  (*   ; cbn in * ; simplify_map_eq; first done. *)
  (*   apply NoDup_cons in HNoDup; destruct HNoDup as [Ha_notin_la HNoDup]. *)
  (*   destruct lws; cbn in * ; try congruence. *)
  (*   injection Hlen_eq; clear Hlen_eq ; intro Hlen_eq. *)

  (*   apply bind_Some in Hupd. *)
  (*   destruct Hupd as ( lm' & Hupd & Hlm ). *)
  (*   rewrite /update_version_addr in Hlm. *)
  (*   destruct (lm' !! (a, v)) as [lw|] eqn:Heq_lm; cbn in * ; simplify_eq. *)

  (*   replace l with lw by (symmetry ; eapply update_version_word_preserves_lword; eauto). *)
  (*   apply update_version_word_region_insert in Hupd; auto. *)
  (*   destruct Hupd as (lm0 & Hupd & ->). *)
  (*   simplify_map_eq. *)

  (*   eapply Hla in Hupd; eauto. *)
  (*   simplify_map_eq. *)
  (*   rewrite !list_to_map_app. *)
  (*   rewrite list_to_map_cons. *)
  (*   rewrite insert_union_r; first done. *)

  (*   apply not_elem_of_list_to_map_1 ; cbn. *)
  (*   rewrite fst_zip; [|rewrite map_length; lia]. *)
  (*   intro Hcontra. *)
  (*   apply elem_of_list_fmap in Hcontra. *)
  (*   destruct Hcontra as (a0 & Hcontra & _). *)
  (*   simplify_eq; lia. *)
  (* Qed. *)

  (* Lemma update_version_word_region_access_region *)
  (*   (lm lm' : LMem) (lwsrc : LWord) (lws : list LWord) *)
  (*   (p : Perm) (b e a : Addr) (v : Version) : *)
  (*   length lws = length (finz.seq_between b e) -> *)
  (*   get_lcap lwsrc = Some (LSCap p b e a v) -> *)
  (*   update_version_word_region *)
  (*     (list_to_map (zip (map (λ a : Addr, (a, v)) (finz.seq_between b e)) lws)) *)
  (*     lwsrc = Some lm' -> *)
  (*   lm' = *)
  (*     (list_to_map *)
  (*        ((zip (map (λ a : Addr, (a, v+1)) (finz.seq_between b e)) lws) *)
  (*        ++ (zip (map (λ a : Addr, (a, v)) (finz.seq_between b e)) lws))). *)
  (* Proof. *)
  (*   intros Hlen_lws Hlwsrc Hupd. *)
  (*   rewrite /update_version_word_region in Hupd. *)
  (*   destruct_lword lwsrc ; cbn in * ; simplify_eq. *)
  (*   all: eapply update_version_word_region_access_region_gen; eauto *)
  (*   ; apply finz_seq_between_NoDup. *)
  (* Qed. *)

  (* (* TODO better name because it means nothing *) *)
  (* Lemma logical_region_reachable *)
  (*   (la : list Addr) *)
  (*   (pc_a a : Addr) (lws : list LWord) *)
  (*   (pc_v v : Version) (lw : LWord) : *)
  (*   NoDup la -> *)
  (*   pc_a ∉ la -> *)
  (*   length lws = length la -> *)
  (*   a ∈ la -> *)
  (*   ∃ lw0, *)
  (*     (<[(pc_a, pc_v):=lw]> *)
  (*        (list_to_map (zip (map (λ a0 : Addr, (a0, v)) la) lws)) : LMem) *)
  (*       !! (a, v) = Some lw0. *)
  (* Proof. *)
  (*   move: pc_a a lws pc_v v lw. *)
  (*   induction la as [|a la Hla] *)
  (*   ; intros * HNoDup Hpca_notin_la Hlen Ha_in_la *)
  (*   ; cbn in * ; simplify_map_eq ; first set_solver. *)

  (*   apply not_elem_of_cons in Hpca_notin_la. *)
  (*   destruct Hpca_notin_la as [Hpca_neq_a Hpca_notin_la]. *)
  (*   destruct lws; cbn in * ; try congruence. *)
  (*   injection Hlen; clear Hlen ; intro Hlen. *)
  (*   apply NoDup_cons in HNoDup. *)
  (*   destruct HNoDup as [Ha_notin_la HNoDup]. *)

  (*   apply elem_of_cons in Ha_in_la. *)
  (*   destruct Ha_in_la as [-> | Ha_in_la]. *)
  (*   - exists l. by rewrite lookup_insert_ne; [| intro ; simplify_eq] ; simplify_map_eq. *)
  (*   - pose proof (Hla _ _ _ pc_v v lw HNoDup Hpca_notin_la Hlen Ha_in_la) as IH. *)
  (*     destruct IH as (lw0 & IH). *)
  (*     exists lw0. *)
  (*     rewrite insert_commute; [| intro ; simplify_eq]. *)
  (*     rewrite lookup_insert_ne ; [|intro ; simplify_eq]. *)
  (*     done. *)
  (* Qed. *)

  (* TODO move region.v *)
  Lemma NoDup_logical_region (b e : Addr) (v : Version) :
    NoDup (map (λ a0 : Addr, (a0, v)) (finz.seq_between b e)).
  Proof.
    apply NoDup_fmap.
    { by intros x y Heq ; simplify_eq. }
    { apply finz_seq_between_NoDup. }
  Qed.

  (* TODO move region.v *)
  Lemma update_logical_memory_region_disjoint
    (la : list Addr) (v : Version) (lws : list LWord):
    length la = length lws ->
    (list_to_map (zip (map (λ a : Addr, (a, v + 1)) la) lws) : LMem)
      ##ₘ list_to_map (zip (map (λ a : Addr, (a, v)) la) lws).
  Proof.
    intros Hlen.
    apply map_disjoint_list_to_map_zip_l ; [rewrite map_length; lia|].
    apply Forall_forall.
    intros a Ha.
    apply not_elem_of_list_to_map.
    rewrite fst_zip; [|rewrite map_length; lia].
    intros Ha'.
    apply elem_of_list_fmap_2 in Ha, Ha'.
    destruct Ha as (? & Ha & ?).
    destruct Ha' as (? & Ha' & ?). simplify_eq; lia.
  Qed.

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
    length lws = finz.dist b e ->

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

      destruct Hupd as [Hcompatibility Hupdated].
      (** TODO a few lemmas required:
          (1) mem ⊆ (update_version_region_local mem _ _),
              which allows us to recover to what was previously known
          (2) a ∈ la ->
              ((a,v), lw) ∈ mem ->
              ((a,v+1), lw) ∈ (update_version_region_local mem la v),
              which means that if an address that has been updated is known beforehand,
              then it's value is the same after the update

          (1) should solve the 2 first pred
          (2) should solve the last pred
       *)

      assert ( mem' !! (pc_a, pc_v) = Some lw ) as Hmem'_pca.
      admit. (* TODO is_valid_updated_lmemory_ne_access *)

      admit.

      (* apply update_version_word_region_cons_no_access in Hupd. *)
      (* 2:{ simplify_map_eq; cbn. *)
      (*     intro Hcontra. *)
      (*     apply elem_of_finz_seq_between in Hcontra. solve_addr. *)
      (* } *)
      (* destruct Hupd as (mem'' & Hupd & ->). *)

      (* eapply update_version_word_region_access_region in Hupd *)
      (* ; eauto; simplify_map_eq ; eauto; [| by rewrite finz_seq_between_length]. *)


      (* iDestruct (big_sepM_insert with "Hmmap") as "[Hpc_a Hmmap]". *)
      (* { apply not_elem_of_list_to_map. *)
      (*   rewrite fmap_app. *)
      (*   do 2 (rewrite fst_zip; [|rewrite map_length finz_seq_between_length; lia]). *)
      (*   apply not_elem_of_app. *)
      (*   split. *)
      (*   all:intros Hcontra. *)
      (*   all:apply elem_of_list_fmap_2 in Hcontra. *)
      (*   all:destruct Hcontra as (? & Ha & ?); simplify_eq. *)
      (* } *)
      (* iFrame. *)
      (* rewrite list_to_map_app. *)
      (* iDestruct (big_sepM_union with "Hmmap") as "[Hmmap_new Hmmap_old]". *)
      (* { apply update_logical_memory_region_disjoint. *)
      (*   by rewrite finz_seq_between_length. *)
      (* } *)
      (* iSplitL "Hmmap_old". *)
      (* + iApply (big_sepM_to_big_sepL2 with "Hmmap_old"). *)
      (*   { apply NoDup_logical_region. } *)
      (*   { by rewrite map_length finz_seq_between_length. } *)
      (* + iApply (big_sepM_to_big_sepL2 with "Hmmap_new"). *)
      (*   { apply NoDup_logical_region. } *)
      (*   { by rewrite map_length finz_seq_between_length. } *)

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
  Admitted.

  (* TODO wp_rule in the other extreme case, where we have no points-to
     for the tested word *)

  (* TODO factor out the general proof for lcap and lsealedcap... *)

  (* TODO merge wp_opt from Dominique's branch and use it *)
  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
