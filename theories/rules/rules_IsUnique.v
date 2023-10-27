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


  | IsUnique_fail (lwsrc: LWord) :
    lmem = lmem' → (* TODO are the equality condition actually necessary ? *)
    lregs = lregs' →
    lregs !! src = Some lwsrc ->
    is_log_cap lwsrc = false →
    IsUnique_spec lregs lmem dst src lregs' lmem' FailedV.


  (* TODO @Bastien *)

  Definition allow_access_map_or_true (r : RegName) (lregs : LReg) (lmem : LMem) : Prop :=
    exists p b e a v, read_reg_inr lregs r p b e a v
                 ∧ if decide (lregs !! r = Some (LCap p b e a v))
                   then Forall (fun a' => exists lw, lmem !! (a',v) = Some lw) (finz.seq_between b e)
                   else True.

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

    admit.

   Admitted.

End cap_lang_rules.
