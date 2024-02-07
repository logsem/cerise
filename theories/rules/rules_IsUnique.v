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
        phr phm (updated lregs) (updated lmem) (updated cur_map)',
        which, one might notice, the version number changes.
   *)

  (* Helper lemma to avoid proof duplication *)
  Lemma mem_phys_log_update
    (reg : Reg) (mem : Mem)
    (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap)
    (src : RegName) (p : Perm) (b e a : Addr) (v : Version) (lw : LWord) :
    get_lcap lw = Some (LSCap p b e a v) ->
    (* necessary for lreg_res_iscur *)
    reg_phys_log_corresponds reg lr cur_map ->
    (* necessary for unique_in_machine_no_accessL *)
    lr !! src = Some lw ->
    unique_in_machineL lm lr src lw ->

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

  (* TODO move *)
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

  (* TODO duplicate of update_cur_version_region_local_preserves_content_lmem *)
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

  Lemma update_cur_version_addr_global_notin_preserves_lmem_inv
    (lmem lm lmem' : LMem) (vmap vmap' : VMap)
    (a a' : Addr) (v : Version) (lw : LWord) :
    a' ≠ a ->
    update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
    lmem' !! (a,v) = Some lw ->
    lmem !! (a,v) = Some lw.
  Proof.
    intros Hneq Hupd Hlw.
    rewrite /update_cur_version_addr_global in Hupd.
    destruct (vmap !! a') eqn:? ; cbn in * ; simplify_map_eq ; last done.
    destruct (lm !! (a', v0)) eqn:? ; cbn in * ; simplify_map_eq
    ; last done.
    rewrite /update_lmemory_lword in Hlw.
    rewrite lookup_insert_ne /= in Hlw; eauto; intro ; simplify_eq.
  Qed.

  Lemma update_cur_version_region_global_notin_preserves_lmem_inv
    (lmem lm lmem' : LMem) (vmap vmap' : VMap)
    (la : list Addr) (a : Addr) (v : Version) (lw : LWord) :
    a ∉ la ->
    update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
    lmem' !! (a,v) = Some lw ->
    lmem !! (a,v) = Some lw.
  Proof.
    move: lmem lm lmem' vmap vmap' a v lw.
    induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hlw
    ; first (by cbn in * ; simplify_map_eq).

    apply not_elem_of_cons in Ha_notin_la
    ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

    apply update_cur_version_region_global_cons in Hupd
    ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
    eapply IHla; eauto.
    eapply update_cur_version_addr_global_notin_preserves_lmem_inv; eauto.
  Qed.

  Lemma update_cur_version_addr_global_notin_preserves_lm_inv
    (lmem lm lmem' : LMem) (vmap vmap' : VMap)
    (a a' : Addr) (v : Version) (lw : LWord) :
    a' ≠ a ->
    lmem ⊆ lm ->
    update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
    lmem' !! (a,v) = Some lw ->
    lm !! (a,v) = Some lw.
  Proof.
    intros Hneq Hlmem_incl Hupd Hlw.
    rewrite /update_cur_version_addr_global in Hupd.
    destruct (vmap !! a') eqn:? ; cbn in * ; simplify_map_eq
    ; last (eapply lookup_weaken ; eauto).
    destruct (lm !! (a', v0)) eqn:? ; cbn in * ; simplify_map_eq
    ; last (eapply lookup_weaken ; eauto).
    rewrite /update_lmemory_lword in Hlw.
    rewrite lookup_insert_ne /= in Hlw; eauto; [|intro ; simplify_eq].
    eapply lookup_weaken ; eauto.
  Qed.

  Lemma update_cur_version_region_global_notin_preserves_lm_inv
    (lmem lm lmem' : LMem) (vmap vmap' : VMap)
    (la : list Addr) (a : Addr) (v : Version) (lw : LWord) :
    a ∉ la ->
    lmem ⊆ lm ->
    update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
    lmem' !! (a,v) = Some lw ->
    lm !! (a,v) = Some lw.
  Proof.
    move: lmem lm lmem' vmap vmap' a v lw.
    induction la as [|a' la IHla]; intros * Ha_notin_la Hlmem_incl Hupd Hlw
    ; first (by cbn in * ; simplify_map_eq; eapply lookup_weaken ; eauto).

    apply not_elem_of_cons in Ha_notin_la
    ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

    apply update_cur_version_region_global_cons in Hupd
    ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
    eapply IHla; eauto.
    eapply update_cur_version_addr_global_notin_preserves_lmem_inv; eauto.
  Qed.

  Lemma update_cur_version_addr_local_notin_preserves_lmem_inv
    (lmem lmem' : LMem) (vmap vmap' : VMap)
    (a a' : Addr) (v : Version) (opt_lw : option LWord) :
    a' ≠ a ->
    update_cur_version_addr_local lmem vmap a' = (lmem', vmap') ->
    lmem' !! (a,v) = opt_lw ->
    lmem !! (a,v) = opt_lw.
  Proof.
    intros Hneq Hupd Hlw.
    rewrite /update_cur_version_addr_local in Hupd.
    destruct (vmap !! a') eqn:? ; cbn in * ; simplify_map_eq ; last done.
    destruct (lmem !! (a', v0)) eqn:? ; cbn in * ; simplify_map_eq
    ; last done.
    rewrite /update_lmemory_lword.
    rewrite lookup_insert_ne /=; eauto; intro ; simplify_eq.
  Qed.

  Lemma update_cur_version_region_local_notin_preserves_lmem_inv
    (lmem lmem' : LMem) (vmap vmap' : VMap)
    (la : list Addr) (a : Addr) (v : Version) (opt_lw : option LWord) :
    a ∉ la ->
    update_cur_version_region_local lmem vmap la = (lmem', vmap') ->
    lmem' !! (a,v) = opt_lw ->
    lmem !! (a,v) = opt_lw.
  Proof.
    move: lmem lmem' vmap vmap' a v opt_lw.
    induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hlw
    ; first (by cbn in * ; simplify_map_eq).

    apply not_elem_of_cons in Ha_notin_la
    ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

    apply update_cur_version_region_local_cons in Hupd
    ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
    eapply IHla; eauto.
    eapply update_cur_version_addr_local_notin_preserves_lmem_inv; eauto.
  Qed.

  Lemma update_version_region_local_notin_preserves_lmem
    (lmem : LMem) (la : list Addr) (a' : Addr) (v v': Version) :
    a' ∉ la ->
    update_version_region_local lmem la v !! (a', v') = lmem !! (a', v').
  Proof.
    move: lmem a' v v'.
    induction la as [|a la IHla] ; intros * Ha'_notin_la.
    - by cbn in *.
    - apply not_elem_of_cons in Ha'_notin_la
      ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local lmem la v)
          /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v))
        as [lwa|] eqn:Hlwa.
      + rewrite /update_lmemory_lword.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
        eapply IHla; eauto.
      + eapply IHla; eauto.
  Qed.

  Lemma update_version_region_local_preserves_lmem
    (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version) :
    update_version_region_local lmem la v !! (a', v) = lmem !! (a', v).
  Proof.
    move: lmem a' v.
    induction la as [|a la IHla] ; intros *.
    - by cbn in *.
    - rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
      rewrite /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v))
        as [lwa|] eqn:Hlwa.
      + rewrite /update_lmemory_lword.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
      + eapply IHla; eauto.
  Qed.

  Lemma update_version_region_local_inv_1
    (lmem : LMem) (la : list Addr) (a : Addr) (v v': Version):
    a ∉ la -> update_version_region_local lmem la v !! (a, v') = lmem !! (a, v').
  Proof.
    move: lmem a v v'.
    induction la as [|a' la IHla] ; intros * Ha_notin_la
    ; first (cbn in *; eauto).

    apply not_elem_of_cons in Ha_notin_la
    ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

    rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
    rewrite update_version_addr_local_lookup_neq; eauto.
  Qed.

  (* TODO refactor the proof *)
  Lemma update_version_region_local_inv_2
    (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version):
      a' ∈ la
      → update_version_region_local lmem la v !! (a', v) = lmem !! (a', v).
  Proof.
    move: lmem a' v.
    induction la as [|a la IHla]; intros * Hin.
    set_solver.
    rewrite elem_of_cons in Hin.
    rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
    destruct Hin ; simplify_map_eq.
    - destruct (decide (a ∈ la)) as [ Ha_in_la | Ha_notin_la ].
      + rewrite /update_version_addr_local.
        destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
        ++ rewrite /update_lmemory_lword.
           rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
           rewrite IHla; eauto.
        ++ rewrite IHla; eauto.
      + rewrite /update_version_addr_local.
        destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
        ++ rewrite /update_lmemory_lword.
           rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
           erewrite update_version_region_local_notin_preserves_lmem; eauto.
        ++ erewrite update_version_region_local_notin_preserves_lmem; eauto.
    - destruct (decide (a' = a)); simplify_eq.
      + rewrite /update_version_addr_local.
        destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
        ++ rewrite /update_lmemory_lword.
           rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
           erewrite update_version_region_local_preserves_lmem; eauto.
        ++ erewrite update_version_region_local_preserves_lmem; eauto.
      + rewrite /update_version_addr_local.
        destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
        ++ rewrite /update_lmemory_lword.
           rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
           rewrite IHla; eauto.
        ++ rewrite IHla; eauto.
  Qed.

  Lemma update_version_region_local_inv
    (lmem : LMem) (la : list Addr) (a : Addr) (v : Version):
    update_version_region_local lmem la v !! (a, v) = lmem !! (a, v).
  Proof.
    intros *.
    destruct (decide (a ∈ la)).
    - eapply update_version_region_local_inv_2 ; eauto.
    - eapply update_version_region_local_inv_1 ; eauto.
  Qed.

  (* TODO find name and refactor proof... *)
  Lemma inter_region_aaa
    (lmem lm lmem' lm' : LMem)
    (vmap_mem vmap_m vmap_mem' vmap_m' : VMap)
    (la : list Addr) (a' : Addr) (v va : Version)
    (lw : LWord) :
    NoDup la ->
    a' ∈ la ->
    lmem ⊆ lm ->
    vmap_mem ⊆ vmap_m ->
    Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
    Forall (λ a0 : Addr, vmap_m !! a0 = Some v) la ->
    Forall (λ a0 : Addr, lm !! (a0, v + 1) = None) la ->
    update_cur_version_region_global lmem lm vmap_mem la = (lmem', vmap_mem') ->
    update_cur_version_region_local lm vmap_m la = (lm', vmap_m') ->
    lmem' !! (a', va) = Some lw ->
    lm' !! (a', va) = Some lw.
  Proof.
    move: lmem lm lmem' lm' vmap_mem vmap_mem' vmap_m vmap_m' a' v va lw.
    induction la as [|a la IHla]
    ; intros * HNoDup Ha'_in_la Hlmem_incl Hvmap_incl
                 HmemMap HcurMap HmaxMap
                 Hupd_lmem Hupd_lm Hlw
    ; first (cbn in * ; simplify_map_eq; eapply lookup_weaken ; eauto).

    apply elem_of_cons in Ha'_in_la.
    apply NoDup_cons in HNoDup
    ; destruct HNoDup as [Ha_notin_la HNoDup].

    rewrite Forall_cons in HmemMap
    ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
    rewrite Forall_cons in HcurMap
    ; destruct HcurMap as [ Hcur_v HcurMap].
    rewrite Forall_cons in HmaxMap
    ; destruct HmaxMap as [ Hmax_v HmaxMap].

    apply update_cur_version_region_global_cons in Hupd_lmem
    ; destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

    apply update_cur_version_region_local_cons in Hupd_lm
    ; destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

    destruct Ha'_in_la as [-> | Ha'_in_la].
    - assert (vmap_m0 !! a = Some v) as Hvmap_m0_a
          by (eapply update_cur_version_region_local_notin_preserves_cur_1; eauto).
      assert (lm0 !! (a, v) = Some lwa) as Hlm0_a
          by (eapply update_cur_version_region_local_preserves_content_lmem ; eauto).
      rewrite /update_cur_version_addr_local in Hupd_lm0.
      rewrite Hvmap_m0_a Hlm0_a in Hupd_lm0; simplify_map_eq.
      rewrite /update_lmemory_lword.
      destruct (decide (va = v+1)); simplify_map_eq.
      { assert (lm !! (a, v) = Some lw) as Hlm_a.
        {

          eapply update_cur_version_region_local_notin_preserves_lmem_inv
          ; eauto.
          assert (lm !! (a, v) = Some lw) as Hlw'.
          {
            rewrite /update_cur_version_addr_global in Hupd_lmem0.
            destruct (vmap_mem0 !! a) as [va|] eqn:Hvmap_mem0_a.
            2: { simplify_map_eq.
                 eapply update_cur_version_region_global_notin_preserves_lm_inv
                   in Hlw; eauto.
                 by rewrite Hlw in Hmax_v.
            }
            eapply update_cur_version_region_global_notin_preserves_cur_2
              in Hvmap_mem0_a
            ; eauto.
            rewrite /is_cur_addr /= in Hvmap_mem0_a.
            eapply lookup_weaken in Hvmap_mem0_a ; eauto.
            rewrite Hvmap_mem0_a in Hcur_v ; simplify_eq.

            rewrite Hlwa in Hupd_lmem0; simplify_eq.
            rewrite /update_lmemory_lword in Hlw.
            by simplify_map_eq.
          }
          by rewrite Hlwa in Hlw' ; simplify_map_eq.

        }
        by rewrite Hlm_a in Hlwa ; simplify_eq.
      }
      {
        rewrite lookup_insert_ne /= ; eauto.
        2: (intro ; simplify_eq).
        clear IHla HmemMap HcurMap HmaxMap.
        - destruct (vmap_mem0 !! a) eqn:Hvmap_mem0_a.
          2: {
            rewrite /update_cur_version_addr_global in Hupd_lmem0.
            rewrite Hvmap_mem0_a in Hupd_lmem0; simplify_eq.
            eapply
              update_cur_version_region_global_notin_preserves_lm_inv
              in Hlw.
            2,3,4: eauto.
            eapply
              update_cur_version_region_local_preserves_content_lmem
              in Hlw ; eauto.
          }
          assert (v = v0) as ->.
          {
            eapply update_cur_version_region_global_notin_preserves_cur_2
              in Hvmap_mem0_a
            ; eauto.
            rewrite /is_cur_addr /= in Hvmap_mem0_a.
            eapply lookup_weaken in Hvmap_mem0_a ; eauto.
            by rewrite Hvmap_mem0_a in Hcur_v ; simplify_eq.
          }

          rewrite /update_cur_version_addr_global Hvmap_mem0_a Hlwa in Hupd_lmem0
          ; simplify_map_eq.
          rewrite /update_lmemory_lword in Hlw ; simplify_map_eq.
          rewrite lookup_insert_ne //= in Hlw; [| intro; simplify_eq ;lia].

          eapply update_cur_version_region_local_preserves_content_lmem
          ; eauto.

          eapply update_cur_version_region_global_notin_preserves_lmem_inv
            in Hlw. 2,3: eauto.
          eapply lookup_weaken; eauto.
      }

    - assert (a ≠ a') as Ha_neq_a' by set_solver.
      assert (lmem0 !! (a', va) = Some lw) as Hlmem0_a'.
      { eapply update_cur_version_addr_global_notin_preserves_lmem_inv
        ; eauto.
      }
      eapply update_cur_version_addr_local_preserves_content_lmem
      ; eauto.
  Qed.

  (* TODO refactor the proof *)
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


    destruct (update_cur_version_region_local lm vmap la)
      as [lm' vmap_m'] eqn:Hupd_lm.
    pose proof Hupd_lm as Hupd_lm'.
    eapply update_cur_version_inter in Hupd_lm; eauto.

    (* -------------------- *)
    assert (lm' !! (a, v + 1) = None)
      by (eapply update_cur_version_region_local_preserves_content_lmem; eauto).
    assert (lm' !! (a, v) = Some lwa) as Hlwa'
        by (eapply update_cur_version_region_local_preserves_content_lmem; eauto).
    eapply update_cur_version_addr_global_local in Hupd_lm; eauto.
    3:{
      eapply update_cur_version_region_global_notin_preserves_cur_1; eauto.
    }
    2:{
      apply map_subseteq_spec.
      intros [a0 va0] lwa0 Hlwa0.
      destruct (decide (a0 ∈ la)).
      {
        eapply inter_region_aaa; eauto.
      }
      { eapply update_cur_version_region_local_preserves_content_lmem; eauto.
        eapply update_cur_version_region_global_notin_preserves_lm_inv in Hlwa0; eauto.
      }
    }
    {
      assert ((update_version_region_local lmem la v) ⊆ lmem0).
      { eapply IHla ; eauto. }
      rewrite /update_version_addr_local.
      assert (update_version_region_local lmem la v ⊆ lmem').
      { rewrite /update_version_addr_local in Hupd0.
        destruct (lmem0 !! (a, v)) eqn:?.
        - rewrite /update_lmemory_lword in Hupd0.
          eapply map_subseteq_spec.
          intros a' lwa' Hlwa'0.
          assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
              (eapply lookup_weaken in Hlwa'0; [|eassumption] ; by eauto).
          assert (<[(a, v + 1):=l]> lmem0 !! (a,v) = Some l).
          { rewrite lookup_insert_ne //=; intro ; simplify_eq; lia. }
          destruct (decide (a' = (a,v))); simplify_map_eq.
          + rewrite update_version_region_local_inv in Hlwa'0 ; eauto.
            eapply lookup_weaken in Hlwa'0; last eapply Hlmem_incl.
            rewrite Hlwa in Hlwa'0; simplify_eq.
            rewrite Hlmem0_a' in Heqo; simplify_eq.
            eapply lookup_weaken; eauto.
            rewrite /update_cur_version_addr_global in Hupd0.
            assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
              by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
            rewrite Hvmap_mem0_a Hlwa in Hupd0; simplify_eq.
            by rewrite /update_lmemory_lword.
          + eapply lookup_weaken; eauto.
            assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
              by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
            eapply update_cur_version_addr_global_incl_lmem; eauto.
            eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
            eapply lookup_weaken_None; [eapply Hmax_v|]; eauto.
        - eapply map_subseteq_spec.
          intros a' lwa' Hlwa'0.
          assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
              (eapply lookup_weaken in Hlwa'0; [|eassumption] ; by eauto).
          eapply lookup_weaken ; eauto.
          rewrite /update_cur_version_addr_global in Hupd0.
          assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
              by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
          rewrite Hvmap_mem0_a Hlwa in Hupd0; simplify_eq.
          rewrite /update_lmemory_lword.
          eapply insert_subseteq_r; eauto.
          eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
          eapply lookup_weaken_None; [eapply Hmax_v|]; eauto.
      }
      destruct (update_version_region_local lmem la v !! (a, v)) eqn:?; auto.
      { rewrite /update_lmemory_lword.
        eapply insert_subseteq_l; auto.
        rewrite update_version_region_local_inv in Heqo ; eauto.
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
    }
  Qed.

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
      split.
      + cbn.
        rewrite -/(update_version_region_local lmem la v).
        destruct Hvalid as [Hupd' _].
        assert (cur_map0 !! a = Some v) as Hcur0
            by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
        rewrite /update_version_addr_local.
        assert (update_version_region_local lmem la v ⊆ lmem').
        {
          assert (update_version_region_local lmem la v ⊆ lmem0).
          {
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
          rewrite update_version_region_local_inv in Heqo; eauto.
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
          destruct ( (decide (a = a'))) as [| Ha'_neq_a]; simplify_map_eq.
          2: { eapply update_cur_version_addr_global_notin_preserves_lmem; eauto. }
          exfalso.
          eapply update_cur_version_region_global_notin_preserves_lmem_inv in Hlwa0; eauto.
          eapply lookup_weaken in Hlwa0 ; eauto.
          by rewrite Hlwa0 in Hmax_v.
  Qed.

  Lemma lword_get_word_update_version (lw : LWord):
    lword_get_word (update_version_lword lw) = lword_get_word lw.
  Proof.
    by destruct_lword lw; cbn.
  Qed.
  Lemma insert_lcap_lreg_strip
    (lregs : LReg) (r : RegName) (lw : LWord):
    is_lcap lw = true ->
    lregs !! r = Some lw ->
    <[ r := (lword_get_word lw) ]> (lreg_strip lregs) = lreg_strip lregs.
  Proof.
    intros Hlw Hr.
    rewrite -fmap_insert insert_id //=.
  Qed.
  Lemma is_lcap_update_version_lword (lw : LWord):
    is_lcap (update_version_lword lw) = is_lcap lw.
  Proof.
    by destruct_lword lw; cbn.
  Qed.

  Lemma get_is_lcap_inv (lw : LWord) :
    is_lcap lw = true -> exists p b e a v, get_lcap lw = Some (LSCap p b e a v).
  Proof.
    intros.
    destruct_lword lw ; cbn in * ; try (exfalso ; congruence).
    all: eexists _,_,_,_,_; eauto.
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

    destruct (get_is_lcap_inv lsrcv Hlsrcv) as (p & b & e & a & v & Hget_lsrcv).


    (* sweep success or sweep fail *)
    destruct (sweep mem reg src) as [|] eqn:Hsweep ; cbn in Hstep.
    - (* sweep is true *)
      eapply sweep_true_specL in Hsweep; eauto.

      destruct (incrementLPC (<[ dst := LInt 1 ]>
                                (<[ src := update_version_lword lsrcv]> lregs)))
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
        ; apply (insert_mono _ ( <[src:=update_version_lword lsrcv]> lr))
        ; apply insert_mono ; eauto.
        simplify_pair_eq.
        replace ((λ lw : LWord, lword_get_word lw) <$>
                   (<[dst:=LInt 1]> (<[src:=update_version_lword lsrcv]> lr)))
          with (<[dst:= WInt 1]> reg)
          in Hlregs'
        ; cycle 1.
        { destruct HLinv as [ [Hstrips Hcurreg] _].
          rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=.
          rewrite lword_get_word_update_version insert_lcap_lreg_strip; eauto.
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
              ; [ iExists lr, lm, cur_map; iFrame; auto
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
      ; apply (insert_mono _ ( <[src:=update_version_lword lsrcv]> lr))
      ; apply insert_mono ; eauto.
      replace ((λ lw, lword_get_word lw) <$>
               <[dst:=LInt 1]> (<[src:=update_version_lword lsrcv]> lr))
        with (<[dst:=WInt 1]> reg) in HuPC.
      2: { destruct HLinv as [ [Hstrips Hcurreg] _]
           ; rewrite -Hstrips !fmap_insert -/(lreg_strip lr) //=
           ; rewrite lword_get_word_update_version insert_lcap_lreg_strip; eauto.
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
        (state_phys_log_cap_all_current _ _ _ _ _ _ _ _ _ _ _ _ Hget_lsrcv HLinv Hlsrc)
        as HcurMap.
      pose proof
        (state_phys_log_last_version _ _ _ _ _ _ _ _ _ _ _ _ Hget_lsrcv HLinv Hlsrc)
        as HmemMap_maxv.
      pose proof
        (state_phys_log_access_word_region _ _ _ _ _ _ _ _ _ _ _ _ Hget_lsrcv HLinv Hlsrc)
        as HmemMap.

      destruct (update_cur_version_word_region_global lmem lm cur_map lsrcv)
        as [lmem' vmap_mem'] eqn:Hupd_lmem
      ; rewrite /update_cur_version_word_region_global Hget_lsrcv /= in Hupd_lmem.
      destruct (update_cur_version_word_region_local lm cur_map lsrcv)
        as [lm' vmap_m'] eqn:Hupd_lm
      ; rewrite /update_cur_version_word_region_local Hget_lsrcv /= in Hupd_lm.
      iMod ((gen_heap_lmem_version_update lm lmem lm' lmem' ) with "Hm Hmem")
        as "[Hm Hmem]"; eauto.

      (* we destruct the cases when the registers are equals *)
      destruct (decide (src = PC)); cycle 1.
      * (* src <> PC *)
        destruct (decide (src = dst)) ; simplify_map_eq ; cycle 1.
        ** (* src <> dst *)
          iMod ((gen_heap_update_inSepM _ _ src (update_version_lword lsrcv)) with "Hr Hmap")
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
            replace reg with (<[ src := lword_get_word (update_version_lword lsrcv) ]> reg).
            2: { rewrite insert_id //= lword_get_word_update_version //=. }
            do 2 (rewrite (insert_commute _ _ src) //).

            eapply update_cur_version_reg_phys_log_cor_updates_src with
            (phm := mem); eauto.
            eapply update_cur_version_region_local_update_lword ; eauto.
            eapply lreg_read_iscur; eauto.
            2: by rewrite lookup_insert_ne // lookup_insert_ne //.
            2: {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
              eapply not_overlap_word_leaL with (a2' := a_pc1)
              ; cycle 4
              ; first eapply (unique_in_machineL_not_overlap_word _ _ src PC); eauto.
              eapply unique_in_machineL_insert_reg; eauto.
              by destruct_lword lsrcv ; cbn; intro.
            }
            split; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
            by cbn.
            apply is_cur_word_lea with (a := a1).
            eapply lreg_read_iscur; eauto.
          }
          { eapply mem_phys_log_update ; eauto. }
          {
            eapply update_cur_version_region_global_valid; eauto.
          }

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
              with (phm := mem) ; eauto.
            done.
            2: by rewrite lookup_insert_ne // lookup_insert_ne //.
            2: {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
              eapply not_overlap_word_leaL with (a2' := a_pc1)
              ; cycle 4
              ; first eapply (unique_in_machineL_not_overlap_word _ lr dst); eauto.
            }
            split; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
            apply is_cur_word_lea with (a := a1).
            eapply lreg_read_iscur; eauto.
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
            (phm := mem) (lwsrc := (LCap p1 b1 e1 a1 v) ); eauto.
            rewrite -/((update_version_lword (LCap p1 b1 e1 a_pc1 v))).
            eapply update_cur_version_region_local_update_lword ; eauto.
            apply is_cur_word_lea with (a := a1).
            eapply lreg_read_iscur; eauto.
            2: by rewrite lookup_insert_ne // lookup_insert_ne //.
            2: {
              eapply unique_in_machineL_insert_reg; eauto ; try by simplify_map_eq.
            }
            split; eauto.
            eapply lreg_insert_respects_corresponds; eauto.
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

      iExists _, lm, cur_map; iFrame; auto
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

  Lemma is_valid_updated_lmemory_notin_preserves_lmem
    (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
    a' ∉ la ->
    is_valid_updated_lmemory lmem la v lmem' ->
    lmem !! (a', v') = Some lw ->
    lmem' !! (a', v') = Some lw.
  Proof.
    move: lmem lmem' a' v v' lw.

    induction la as [|a la IHla] ; intros * Ha'_notin_la [Hcompatibility Hupdated] Hlmem
    ; first (cbn in *; eapply lookup_weaken ; eauto).

    apply not_elem_of_cons in Ha'_notin_la
    ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].

    apply Forall_cons in Hupdated
    ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
      in Hcompatibility.

    rewrite map_subseteq_spec in Hcompatibility.
    apply Hcompatibility.

    rewrite /update_version_addr_local.
    + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
      * rewrite /update_lmemory_lword.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
        rewrite update_version_region_local_notin_preserves_lmem; eauto.
      * rewrite update_version_region_local_notin_preserves_lmem; eauto.
  Qed.

  Lemma is_valid_updated_lmemory_preserves_lmem
    (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
    is_valid_updated_lmemory lmem la v lmem' ->
    lmem !! (a', v) = Some lw ->
    lmem' !! (a', v) = Some lw.
  Proof.
    move: lmem lmem' a' v lw.

    induction la as [|a la IHla] ; intros * [Hcompatibility Hupdated] Hlmem
    ; first (cbn in *; eapply lookup_weaken ; eauto).

    apply Forall_cons in Hupdated
    ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
      in Hcompatibility.

    rewrite map_subseteq_spec in Hcompatibility.
    apply Hcompatibility.

    rewrite /update_version_addr_local.
    + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
      * rewrite /update_lmemory_lword.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq; lia).
        rewrite update_version_region_local_preserves_lmem; eauto.
      * rewrite update_version_region_local_preserves_lmem; eauto.
  Qed.

  Lemma update_version_region_local_preserves_lmem_next
    (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version) :
    NoDup la ->
    a' ∈ la ->
    lmem !! (a', v+1) = None ->
    update_version_region_local lmem la v !! (a', v + 1) = lmem !! (a', v).
  Proof.
    move: lmem a' v.
    induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la Hlmem_next
    ; first (by set_solver).
    apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup].
    apply elem_of_cons in Ha'_in_la.

    rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
    rewrite /update_version_addr_local.
    rewrite /update_lmemory_lword.
    destruct Ha'_in_la as [|Ha'_in_la] ; simplify_map_eq.
    - destruct (update_version_region_local lmem la v !! (a, v))
        as [lwa|] eqn:Hlwa; rewrite update_version_region_local_inv in Hlwa.
      + by simplify_map_eq.
      + rewrite Hlwa update_version_region_local_notin_preserves_lmem; eauto.
    - destruct (update_version_region_local lmem la v !! (a, v))
        as [lwa|] eqn:Hlwa; rewrite update_version_region_local_inv in Hlwa.
      + rewrite lookup_insert_ne //= ; [|intro ; simplify_eq ; set_solver].
        erewrite IHla; eauto.
      + erewrite IHla; eauto.
  Qed.

  Lemma is_valid_updated_lmemory_preserves_lmem_next
    (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
    NoDup la ->
    a' ∈ la ->
    is_valid_updated_lmemory lmem la v lmem' ->
    Forall (fun a => lmem !! (a, v+1) = None) la ->
    lmem !! (a', v) = Some lw ->
    lmem' !! (a', v+1) = Some lw.
  Proof.
    move: lmem lmem' a' v lw.

    induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la [Hcompatibility Hupdated] Hmax_la Hlmem
    ; first (cbn in *; eapply lookup_weaken ; eauto; set_solver).

    apply NoDup_cons in HNoDup
    ; destruct HNoDup as [Ha_notin_la HNoDup].
    apply elem_of_cons in Ha'_in_la.

    apply Forall_cons in Hupdated
    ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

    apply Forall_cons in Hmax_la
    ; destruct Hmax_la as [ Hmax_a Hmax_la ].

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
      in Hcompatibility.

    rewrite map_subseteq_spec in Hcompatibility.
    apply Hcompatibility.
    rewrite -(update_version_region_local_preserves_lmem _ la) in Hlmem; eauto.

    rewrite /update_version_addr_local.
    + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
      * rewrite /update_lmemory_lword.
        destruct Ha'_in_la as [? | Ha'_in_la] ; simplify_map_eq; first done.
        pose proof Ha'_in_la as Ha'_in_la'.
        apply elem_of_list_lookup in Ha'_in_la'.
        destruct Ha'_in_la' as [? Ha'_lookup].
        eapply Forall_lookup in Hmax_la ; eauto.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq; set_solver).

        rewrite update_version_region_local_preserves_lmem_next; eauto.
        rewrite update_version_region_local_preserves_lmem in Hlmem ; eauto.
      * destruct Ha'_in_la as [? | Ha'_in_la] ; simplify_map_eq.
        rewrite update_version_region_local_preserves_lmem in Hlmem; eauto.
        rewrite update_version_region_local_preserves_lmem_next ; eauto.
        apply elem_of_list_lookup_1 in Ha'_in_la; destruct Ha'_in_la as [? Ha'_in_la].
        eapply Forall_lookup in Hmax_la ; eauto.
  Qed.

  Lemma list_to_map_zip_inv
    (a : Addr) ( v v' : Version )
    (la : list Addr) (lws : list LWord) :
    NoDup la ->
    length lws = length la ->
    is_Some ((list_to_map (zip (map (λ a' : Addr, (a', v)) la) lws) : gmap LAddr LWord) !! (a, v')) ->
    (v' = v) /\ (a ∈ la).
  Proof.
    intros HNoDup Hlen [lw Hlw].
    apply elem_of_list_to_map in Hlw.
    2:{
      rewrite fst_zip ; eauto; last  (rewrite map_length; lia).
      apply NoDup_fmap; auto.
      by intros x y Heq ; simplify_eq.
    }
    apply elem_of_zip_l in Hlw.
    apply elem_of_list_fmap in Hlw.
    by destruct Hlw as (? & ? & ?); simplify_eq.
  Qed.

  Lemma list_to_map_zip_version
    (la : list Addr) (a' : Addr) (v v' : Version) (lws : list LWord) :
    NoDup la ->
    a' ∈ la ->
    length lws = length la ->
    (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws): gmap LAddr LWord) !! (a', v)
    = (list_to_map (zip (map (λ a : Addr, (a, v')) la) lws): gmap LAddr LWord) !! (a', v').
  Proof.
    move: a' v v' lws.
    induction la as [|a la IHla]; intros * HNoDup Ha'_in_la Hlen.
    - cbn in *; set_solver.
    - cbn in Hlen; destruct lws as [|lw lws] ; simplify_eq.
      injection Hlen ; clear Hlen ; intro Hlen.

      apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup_la].
      apply elem_of_cons in Ha'_in_la.
      destruct Ha'_in_la; simplify_map_eq; first done.
      rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
      rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
      by apply IHla.
  Qed.

  Lemma update_version_region_local_insert
    (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord):
    NoDup la ->
    a' ∉ la ->
    lmem !! (a', v') = None ->
    Forall (fun a => lmem !! (a, v+1) = None) la ->
    update_version_region_local (<[(a', v'):=lw]> lmem) la v ⊆ lmem' ->
    update_version_region_local lmem la v ⊆ lmem'.
  Proof.
    move: lmem lmem' a' v v' lw.
    induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None HmaxMap Hupd.
    - cbn in *.
      eapply insert_delete_subseteq in Hupd; eauto.
      apply map_subseteq_spec ; intros [a0 v0] lw0 Hlw0.
      eapply lookup_weaken in Hlw0 ; last eauto.
      assert ((a0, v0) ≠ (a', v')) as Hneq by (intro ; simplify_map_eq).
      rewrite lookup_delete_ne in Hlw0 ; eauto.
    - rewrite NoDup_cons in HNoDup; destruct HNoDup as [Ha_noit_la HNoDup_la].
      rewrite not_elem_of_cons in Ha'_notin_la
      ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].
      rewrite Forall_cons in HmaxMap ; destruct HmaxMap as [ Hmax_v HmaxMap].

      assert (update_version_region_local lmem la v ⊆ lmem').
      { eapply IHla with (a' := a') (v' := v') (lw := lw); eauto.

        rewrite
          /update_version_region_local
            /=
            -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
            /update_version_addr_local
            /update_lmemory_lword
          in Hupd.

        destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
          eqn:?
        ; rewrite update_version_region_local_preserves_lmem in Heqo
        ; last done.

        assert (
            (update_version_region_local (<[(a', v'):=lw]> lmem) la v)
              !! (a, v+1) = None).
        { rewrite update_version_region_local_notin_preserves_lmem; eauto.
          rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
        }

        eapply map_subseteq_spec; intros [a0 v0] lw0 Hlw0.
        eapply lookup_weaken; last eauto.
        rewrite lookup_insert_ne //=.
        intro; simplify_eq.
        by rewrite H in Hlw0.
      }

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local lmem la v)
          /update_version_addr_local
          /update_lmemory_lword
      .

      destruct (update_version_region_local lmem la v !! (a, v))
        eqn:?; last done.
      eapply insert_subseteq_l; eauto.

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
          /update_version_addr_local
        in Hupd.

      rewrite update_version_region_local_preserves_lmem in Heqo.
      destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
        eqn:?
      ; rewrite update_version_region_local_preserves_lmem in Heqo0
      ; (rewrite lookup_insert_ne in Heqo0 ; [| intro ; simplify_eq ])
      ; rewrite Heqo in Heqo0
      ; simplify_eq.
      rewrite /update_lmemory_lword in Hupd.
      eapply map_subseteq_spec in Hupd.
      eapply Hupd.
      by simplify_map_eq.
  Qed.

  Lemma is_valid_updated_lmemory_preserves_lmem_incl
    (lmem' : LMem) (la : list Addr) (v : Version) (lws : list LWord) :
    NoDup la ->
    length lws = length la ->
    is_valid_updated_lmemory (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)) la v lmem' ->
    (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)) ⊆ lmem'.
  Proof.
    move: lmem' v lws.
    induction la as [|a la IHla] ; intros * HNoDup Hlen Hvalid.
    - cbn in *; apply map_empty_subseteq.
    - cbn in *.
      destruct lws as [|lw lws]; simplify_eq.
      cbn in Hlen; injection Hlen ; clear Hlen ; intros Hlen.
      apply NoDup_cons in HNoDup
      ; destruct HNoDup as [Ha_notin_la HNoDup].
      cbn in *.
      destruct Hvalid as [Hupd_incl Hnext].
      rewrite Forall_cons in Hnext ; destruct Hnext as [Hnext HnextMap].
      rewrite /=
        -/(update_version_region_local
             (<[(a, v):=lw]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)))
             la
             v)
        /update_version_addr_local
        update_version_region_local_notin_preserves_lmem
        /update_lmemory_lword
        in Hupd_incl; eauto; simplify_map_eq.
      assert (
          (update_version_region_local
             (<[(a, v):=lw]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws))) la v)
            ⊆ lmem').
      {
        assert (
            update_version_region_local (<[(a, v):=lw]> (list_to_map (zip (map (λ a0 : Addr, (a0, v)) la) lws)))
              la v !! (a, v + 1) = None
          ).
        {
          rewrite update_version_region_local_notin_preserves_lmem; eauto.
          rewrite lookup_insert_ne //= ; [| intro ; simplify_eq ; lia].
          apply not_elem_of_list_to_map; cbn.
          rewrite fst_zip; eauto; last (rewrite map_length; lia).
          intro Hcontra.
          apply elem_of_list_fmap in Hcontra.
          destruct Hcontra as (? & ? & Hcontra) ; simplify_eq; lia.
        }
        eapply insert_delete_subseteq in Hupd_incl; eauto.

        apply map_subseteq_spec; intros [a' v'] lwa' Hlwa'.
        eapply lookup_weaken in Hlwa'; last eauto.
        by apply lookup_delete_Some in Hlwa'; destruct Hlwa'.
      }

      eapply insert_subseteq_l; eauto.
      { assert (
            ((update_version_region_local (<[(a, v):=lw
                  ]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws))) la v)
               !! (a,v)) = Some lw).
        { rewrite update_version_region_local_preserves_lmem; by simplify_map_eq. }
        eapply lookup_weaken; eauto.
      }
      { eapply IHla; eauto.
        split; eauto.
        eapply update_version_region_local_insert; eauto.
        { clear -Hlen Ha_notin_la.
          eapply not_elem_of_list_to_map.
          intro Hcontra.
          rewrite fst_zip in Hcontra; last (rewrite map_length ; lia).
          rewrite elem_of_list_fmap in Hcontra.
          destruct Hcontra as (?&?&?); set_solver.
        }
        { clear -Hlen.
          apply Forall_forall.
          intros a Ha.
          eapply not_elem_of_list_to_map.
          intro Hcontra.
          rewrite fst_zip in Hcontra; last (rewrite map_length ; lia).
          rewrite elem_of_list_fmap in Hcontra.
          destruct Hcontra as (?&?&?) ; simplify_eq; lia.
        }
      }
  Qed.

  (* TODO refactor the proof *)
  Lemma is_valid_updated_lmemory_insert
    (lmem lmem': LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
    NoDup la ->
    a' ∉ la ->
    lmem !! (a', v') = None ->
    Forall (fun a => lmem !! (a, v+1) = None) la ->
    is_valid_updated_lmemory (<[(a', v') := lw]> lmem) la v lmem' ->
    is_valid_updated_lmemory lmem la v lmem'.
  Proof.
    move: lmem lmem' a' v v' lw.
    induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None HmaxMap Hvalid.
    - destruct Hvalid.
      split; cbn in *; last done.
      eapply map_subseteq_spec ; intros [a0 v0] lw0 Hlw0.
      eapply lookup_weaken ; last eapply H.
      rewrite lookup_insert_ne //=; intro ; simplify_eq.
      rewrite Hlmem_None in Hlw0 ; done.
    - rewrite NoDup_cons in HNoDup; destruct HNoDup as [Ha_noit_la HNoDup_la].
      rewrite not_elem_of_cons in Ha'_notin_la
      ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].
      rewrite Forall_cons in HmaxMap ; destruct HmaxMap as [ Hmax_v HmaxMap].

      assert (is_valid_updated_lmemory lmem la v lmem') as Hvalid_IH.
      { eapply IHla with (a' := a') (v' := v') (lw := lw); eauto.

        destruct Hvalid as [Hupd HnextMap].
        rewrite Forall_cons in HnextMap
        ; destruct HnextMap as [ [ lw' Hlw' ] HnextMap].

        rewrite
          /update_version_region_local
            /=
            -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
          in Hupd.
        split; eauto.

        rewrite
          /update_version_region_local
            /=
            -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
            /update_version_addr_local
            /update_lmemory_lword
          in Hupd.

        destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
          eqn:?
        ; rewrite update_version_region_local_preserves_lmem in Heqo
        ; last done.

        assert (
            (update_version_region_local (<[(a', v'):=lw]> lmem) la v)
              !! (a, v+1) = None).
        { rewrite update_version_region_local_notin_preserves_lmem; eauto.
          rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
        }

        eapply map_subseteq_spec; intros [a0 v0] lw0 Hlw0.
        eapply lookup_weaken; last eauto.
        rewrite lookup_insert_ne //=.
        intro; simplify_eq.
        by rewrite H in Hlw0.
      }

      destruct Hvalid as [Hupd HnextMap].
      destruct Hvalid_IH as [Hupd_IH HnextMap_IH].
      split; last done.

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local lmem la v)
          /update_version_addr_local
          /update_lmemory_lword
      .

      destruct (update_version_region_local (lmem) la v !! (a, v))
        eqn:?; last done.
      eapply insert_subseteq_l; eauto.

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
          /update_version_addr_local
        in Hupd.

      rewrite update_version_region_local_preserves_lmem in Heqo.
      destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
        eqn:?
      ; rewrite update_version_region_local_preserves_lmem in Heqo0
      ; (rewrite lookup_insert_ne in Heqo0 ; [| intro ; simplify_eq ])
      ; rewrite Heqo in Heqo0
      ; simplify_eq.
      rewrite /update_lmemory_lword in Hupd.
      eapply map_subseteq_spec in Hupd.
      eapply Hupd.
      by simplify_map_eq.
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

      Set Nested Proofs Allowed.
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

      iDestruct (big_sepM_insert_delete_list with "Hmmap") as "[Hrange Hmmap]"
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

      iDestruct (big_sepM_insert_delete_list with "Hmmap") as "[Hrange Hmmap]"
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

  (* TODO wp_rule in the other extreme case, where we have no points-to
     for the tested word *)

  (* TODO factor out the general proof for lcap and lsealedcap... *)

  (* TODO merge wp_opt from Dominique's branch and use it *)
  (* TODO extend proofmode, which means cases such as:
     dst = PC, src = PC, dst = stc *)

End cap_lang_rules.
