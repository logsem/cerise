From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Import machine_base.
From cap_machine Require Export rules_base region.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
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

  Definition reg_allows_hash (lregs : LReg) (r : RegName) p b e a v :=
    lregs !! r = Some (LCap p b e a v) ∧ readAllowed p = true.

  Definition hash_lmemory_region (lm : LMem) (b e : Addr) (v : Version) :=
    let instructions : list LWord :=
      map snd
        ((map_to_list
            (filter (fun '(a, _) => (laddr_get_addr a) ∈ (finz.seq_between b e)
                                  /\ (laddr_get_version a) = v)
               lm)))
    in
    hash (fmap lword_get_word instructions).


  Inductive Hash_failure (lregs: LReg) (dst src: RegName) (lmem : LMem) :=
  | Hash_fail_const lw:
      lregs !! src = Some lw ->
      is_log_cap lw = false →
      Hash_failure lregs dst src lmem
  | Hash_fail_perm p b e a v:
      lregs !! src = Some (LCap p b e a v) ->
      readAllowed p = false →
      Hash_failure lregs dst src lmem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Hash_fail_invalid_PC p b e a v :
      lregs !! src = Some (LCap p b e a v) ->
      Forall (fun a => ∃ lw, lmem !! (a,v) = Some lw) (finz.seq_between b e) ->
      incrementLPC (<[ dst := LInt (hash_lmemory_region lmem b e v)]> lregs) = None ->
      Hash_failure lregs dst src lmem
  .

  Inductive Hash_spec (lregs: LReg) (dst src: RegName) (lmem : LMem) (lregs': LReg): cap_lang.val -> Prop :=
  | Hash_spec_success p b e a v :
      reg_allows_hash lregs src p b e a v ->
      Forall (fun a => ∃ w, lmem !! (a,v) = Some w) (finz.seq_between b e) ->
      incrementLPC (<[ dst := LInt (hash_lmemory_region lmem b e v)]> lregs) = Some lregs' ->
      Hash_spec lregs dst src lmem lregs' NextIV
  | Hash_spec_failure:
      Hash_failure lregs dst src lmem ->
      Hash_spec lregs dst src lmem lregs' FailedV.

  Definition allow_hash_map_or_true r (lregs : LReg) (lmem : LMem):=
    ∃ p b e a v, read_reg_inr lregs r p b e a v ∧
      if decide (reg_allows_hash lregs r p b e a v)
      then Forall (fun a => ∃ lw, lmem !! (a,v) = Some lw) (finz.seq_between b e)
      else True.

  Lemma allow_hash_implies_hashv:
    ∀ (src : RegName) (lmem : LMem) (lr : LReg) (p : Perm) (b e a : Addr) v,
      allow_hash_map_or_true src lr lmem
      → lr !! src = Some (LCap p b e a v)
      → readAllowed p = true
      → Forall (fun a => ∃ lw, lmem !! (a,v) = Some lw) (finz.seq_between b e).
  Proof.
    intros src lmem lr p b e a v HaHash Hr2v Hra.
    unfold allow_hash_map_or_true, read_reg_inr in HaHash.
    destruct HaHash as (?&?&?&?&?& Hrinr & Hmem).
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - exact Hmem.
    - contradiction Hrega. done.
  Qed.

  (* Lemma mem_eq_implies_allow_hash_map: *)
  (*   ∀ (lregs : LReg) (lmem : LMem) (src : RegName) (lw : LWord) p b e a v, *)
  (*     lmem = <[(a, v):=lw]> ∅ *)
  (*     → lregs !! src = Some (LCap p b e a v) *)
  (*     → allow_hash_map_or_true src lregs lmem. *)
  (* Proof. *)
  (*   intros lregs lmem src lw p b e a v Hmem Hrsrc. *)
  (*   exists p,b,e,a,v; split. *)
  (*   - unfold read_reg_inr. by rewrite Hrsrc. *)
  (*   - case_decide; last done. *)
  (*     exists lw. simplify_map_eq. auto. *)
  (* Qed. *)

  (* Lemma mem_neq_implies_allow_load_map: *)
  (*   ∀ (lregs : LReg) (lmem : LMem) (r2 : RegName) (pc_a : Addr) (pca_v : Version) *)
  (*     (lw lw' : LWord) p b e a v, *)
  (*     (a ≠ pc_a \/ v <> pca_v) *)
  (*     → lmem = <[(pc_a, pca_v):= lw]> (<[(a, v) := lw']> ∅) *)
  (*     → lregs !! r2 = Some (LCap p b e a v) *)
  (*     → allow_load_map_or_true r2 lregs lmem. *)
  (* Proof. *)
  (*   intros lregs lmem r2 pc_a pca_v lw lw' p b e a v H4 Hrr2 Hreg2. *)
  (*   exists p,b,e,a,v; split. *)
  (*   - unfold read_reg_inr. by rewrite Hreg2. *)
  (*   - case_decide; last done. *)
  (*     exists lw'. *)
  (*     destruct H4; assert ((pc_a, pca_v) <> (a, v)) by congruence; simplify_map_eq; auto. *)
  (* Qed. *)

  (* Lemma mem_implies_allow_load_map: *)
  (*   ∀ (lregs : LReg)(lmem : LMem)(r2 : RegName) (pc_a : Addr) pca_v *)
  (*     (lw lw' : LWord) p b e a v, *)
  (*     (if ((a,v ) =? (pc_a, pca_v))%la *)
  (*      then lmem = <[(pc_a, pca_v):=lw]> ∅ *)
  (*      else lmem = <[(pc_a, pca_v):=lw]> (<[(a, v):=lw']> ∅)) *)
  (*     → lregs !! r2 = Some (LCap p b e a v) *)
  (*     → allow_load_map_or_true r2 lregs lmem. *)
  (* Proof. *)
  (*   intros lregs lmem r2 pc_a pca_v lw lw' p b e a v H4 Hrr2. *)
  (*   destruct ((a,v) =? (pc_a, pca_v))%la eqn:Heq; cbn in Heq. *)
  (*     + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2]. *)
  (*       apply Z.eqb_eq, finz_to_z_eq in Heq1. subst a. *)
  (*       apply Nat.eqb_eq in Heq2. subst v. *)
  (*       eapply mem_eq_implies_allow_load_map; eauto. *)
  (*     + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq] *)
  (*     ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ] *)
  (*     ; eapply (mem_neq_implies_allow_load_map _ _ _ pc_a pca_v _ _ _ _ _ a v) ; eauto. *)
  (*       left ; solve_addr. *)
  (* Qed. *)

  (* Lemma mem_implies_loadv: *)
  (*   ∀ (pc_a : Addr) (pca_v : Version) (lw lw' : LWord) (a : Addr) *)
  (*     (lmem : LMem) (loadv : LWord) v, *)
  (*     (if ((a,v ) =? (pc_a, pca_v))%la *)
  (*      then lmem = <[(pc_a, pca_v):=lw]> ∅ *)
  (*      else lmem = <[(pc_a, pca_v):=lw]> (<[(a, v):=lw']> ∅))→ *)
  (*     lmem !! (a,v) = Some loadv → *)
  (*     loadv = (if ((a,v ) =? (pc_a, pca_v))%la then lw else lw'). *)
  (* Proof. *)
  (*   intros pc_a pca_v lw lw' a lmem loadv v H4 H6. *)
  (*   destruct ((a,v ) =? (pc_a, pca_v))%la eqn:Heq; cbn in Heq ; rewrite H4 in H6. *)
  (*   + apply andb_true_iff in Heq. destruct Heq as [Heq1 Heq2]. *)
  (*     apply Z.eqb_eq, finz_to_z_eq in Heq1; subst a. *)
  (*     apply Nat.eqb_eq in Heq2; subst v. *)
  (*     by simplify_map_eq. *)
  (*   + apply andb_false_iff in Heq. destruct Heq as [Heq | Heq] *)
  (*     ; [ apply Z.eqb_neq in Heq |  apply Nat.eqb_neq in Heq ] *)
  (*     ; rewrite lookup_insert_ne in H6; try congruence; try by simplify_map_eq. *)
  (* Qed. *)

  Definition exec_optL_Hash
    (lregs : LReg) (lmem : LMem)
    (dst src : RegName) : option LReg :=
    lwsrc ← lregs !! src ;
    match lwsrc with
    | LCap p b e a v =>
        if readAllowed p
        then
          lpc ← incrementLPC (<[dst := (LWInt (hash_lmemory_region lmem b e v)) ]> lregs) ;
          Some lpc (* trick to bind with update_reg *)
        else None
    | _ => None
    end.

  Lemma wp_hash Ep
    pc_p pc_b pc_e pc_a pc_v
    dst src lw lmem lregs :
    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Hash dst src) ⊆ dom lregs →
    lmem !! (pc_a, pc_v) = Some lw →
    allow_hash_map_or_true src lregs lmem →

    {{{ (▷ [∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
          ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Hash_spec lregs dst src lmem lregs' retv⌝ ∗
            ([∗ map] la↦lw ∈ lmem, la ↦ₐ lw) ∗
            [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaHash φ) "(>Hmem & >Hregs) Hφ".
    rewrite -(insert_id lmem _ _ Hmem_pc).
    iDestruct (big_sepM_insert_delete with "Hmem") as "[Hpc_a Hmem]"; cbn.

    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hregs Hmem Hφ]").

    iModIntro.
    iIntros (σ) "(Hσ & Hregs &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Hash lregs lmem dst src)).
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.

    iDestruct (big_sepM_insert_delete _ _ _ lw with "[Hpc_a $Hmem]") as "Hmem"; iFrame.
    rewrite insert_id; auto.
    iMod (state_interp_transient_intro_nodfracs with "[$Hregs $Hσ $Hmem]") as "Hσ".

    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver.
    iIntros (lw2) "Hσ %Hlrs %Hrs".

    destruct (is_log_cap lw2) eqn:Hlw2; cycle 1.
    {
      destruct_lword lw2 ; cbn in * ; simplify_eq.
      all: iModIntro.
      all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      all: rewrite big_sepM_fmap.
      all: iApply ("Hφ" with "[$Hmem $Hregs]").
      all: iPureIntro; constructor; by eapply Hash_fail_const.
    }

    destruct_lword lw2 ; cbn in * ; simplify_eq.
    destruct (decide (readAllowed p = true)) as [Hread|Hread]
    ; [|apply not_true_is_false in Hread] ; rewrite Hread ;cycle 1;cbn.
    {
      iModIntro.
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro; constructor; by eapply Hash_fail_perm.
    }

    pose proof (allow_hash_implies_hashv _ _ _ _ _ _ _ _ HaHash Hlrs Hread) as Hhash_mem.

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (k1 := fun x => Some x)).
    iApply wp_opt2_eqn_both.

    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LInt (hash_lmemory_region lmem b e v)) with "Hσ") as "Hσ".
    { set_solver. }
    { by cbn. }

    replace (WInt (hash_memory_region (mem σ) b e))
      with ( lword_get_word  (LInt (hash_lmemory_region lmem b e v))).
    2:{ admit. }


    iApply (wp2_opt_incrementPC with "[$Hσ Hcred Hφ]").
    { now rewrite elem_of_dom (lookup_insert_dec HPC). }
    iSplit; cbn; iIntros (φt' lrt') "Hσ %Heqn1 %Heqn2".
    - iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      eapply Hash_spec_failure.
      by econstructor.
    - iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)".
      rewrite big_sepM_fmap.
      iApply ("Hφ" with "[$Hmem $Hregs]").
      iPureIntro.
      eapply Hash_spec_success; eauto.
      split;eauto.
  Admitted.

  Lemma wp_hash_success Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst src
    wdst p b e a v ws lw
    :

    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWInt (hash ws)
          ∗ src ↦ᵣ LCap p b e a v
          ∗ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
      }}}.
  Proof.
  Admitted.

  Lemma wp_hash_success_same Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst p b e a v ws lw
    :

    decodeInstrWL lw = Hash dst dst →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWInt (hash ws)
          ∗ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
      }}}.
  Proof.
  Admitted.

  Lemma wp_hash_success_overlapPC Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst src
    wdst p b e a v ws ws' lw
    :

    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ [[ b , pc_a ]] ↦ₐ{ v } [[ ws ]]
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ [[ pc_a' , e ]] ↦ₐ{ v } [[ ws' ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ dst ↦ᵣ LWInt (hash (ws++[lw]++ws'))
          ∗ src ↦ᵣ LCap p b e a v
          ∗ [[ b , pc_a ]] ↦ₐ{ v } [[ ws ]]
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ [[ pc_a' , e ]] ↦ₐ{ v } [[ ws' ]]
      }}}.
  Proof.
  Admitted.

End cap_lang_rules.
