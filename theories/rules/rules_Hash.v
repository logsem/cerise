From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Import machine_base.
From cap_machine Require Export rules_base region logical_mapsto.

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

  (* Definition hash_lmemory_region (lm : LMem) (b e : Addr) (v : Version) := *)
  (*   let instructions : list LWord := *)
  (*     map snd *)
  (*       ((map_to_list *)
  (*           (filter (fun mem_addr => (laddr_get_addr (fst mem_addr)) ∈ (finz.seq_between b e) *)
  (*                                 /\ (laddr_get_version (fst mem_addr)) = v) *)
  (*              lm))) *)
  (*   in *)
  (*   hash (fmap lword_get_word instructions). *)

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
    lregs = lregs' ->
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

  Lemma incrementLPC_incrementPC_some regs regs' :
    incrementLPC regs = Some regs' ->
    incrementPC (lreg_strip regs) = Some (lreg_strip regs').
  Proof.
    rewrite /incrementPC /incrementLPC.
    intros Hlpc.
    rewrite /lreg_strip lookup_fmap; cbn.
    destruct (regs !! PC) as [lw|] eqn:Heq ; rewrite Heq; cbn in *; last done.
    destruct_lword lw; cbn in *; try done.
    destruct (a + 1)%a; last done.
    simplify_eq.
    by rewrite fmap_insert.
  Qed.

  Lemma incrementLPC_incrementPC_none regs :
    incrementLPC regs = None <-> incrementPC (lreg_strip regs) = None.
  Proof.
    intros.
    rewrite /incrementPC /incrementLPC.
    rewrite /lreg_strip lookup_fmap; cbn.
    destruct (regs !! PC) as [LX|] eqn:Heq ; rewrite Heq; cbn; last done.
    destruct LX ; cbn ; [(clear; firstorder) | | (clear; firstorder)].
    destruct sb as [? ? ? a' | ] ; eauto; cbn; last done.
    destruct (a' + 1)%a eqn:Heq'; done.
  Qed.

  Lemma incrementLPC_fail_updatePC regs m etbl ecur:
    incrementLPC regs = None ->
    updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} = None.
  Proof.
    intro Hincr. apply incrementLPC_incrementPC_none in Hincr.
    by apply incrementPC_fail_updatePC.
  Qed.


  Lemma incrementLPC_success_updatePC regs m etbl ecur regs' :
    incrementLPC regs = Some regs' ->
    ∃ p b e a a' (v : Version),
      regs !! PC = Some (LCap p b e a v) ∧
      (a + 1)%a = Some a' ∧
      updatePC {| reg := (lreg_strip regs); mem := m; etable := etbl ; enumcur := ecur |} =
      Some (NextI,
              {| reg := (<[PC:=WCap p b e a']> (lreg_strip regs));
                mem := m;
                etable := etbl ;
                enumcur := ecur |})
      ∧ regs' = <[ PC := (LCap p b e a' v) ]> regs.
  Proof.
    intro Hincr.
    opose proof (incrementLPC_incrementPC_some _ _ Hincr) as HincrPC.
    eapply (incrementPC_success_updatePC _ m etbl ecur) in HincrPC.
    destruct HincrPC as (p'&b'&e'&a''&a'''&Hregs&Heq&Hupd&Hregseq).
    rewrite /incrementLPC in Hincr.
    destruct (regs !! PC) as [wpc |]; last done.
    destruct_lword wpc; try done.
    destruct (a + 1)%a as [a'|] eqn:Heq'; last done; simplify_eq.
    rewrite /lreg_strip fmap_insert //= -/(lreg_strip regs)  in Hregseq.
    exists p, b, e, a, a', v.
    repeat (split; try done).
    by rewrite Hupd Hregseq.
  Qed.

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

  Lemma hash_lmemory_weaken lmem lm b e v :
    Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) (finz.seq_between b e) ->
    lmem ⊆ lm ->
    (hash_lmemory_region lm b e v) =
    (hash_lmemory_region lmem b e v).
  Admitted.

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
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaHash φ) "(>Hmem & >Hmap) Hφ".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as (lr lm vmap tbl_cur tbl_prev tbl_all)
        "(Hr & Hm
         & -> & Htbl_cur & Htbl_prev & Htbl_all
         & HEC
         & %Hdom_tbl1 & %Hdom_tbl2 & %Hdom_tbl3 & %Hdom_tbl4
         & %HLinv)"
    ; cbn in HLinv, Hdom_tbl1, Hdom_tbl2, Hdom_tbl3, Hdom_tbl4.
    pose proof HLinv as HLinv'.

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


    (* src contains a capability *)
    destruct (is_log_cap lsrcv) eqn:Hlsrcv; cycle 1; subst srcv; cbn in *.
    { (* Fail : not a capability *)
      destruct_lword lsrcv; cbn in * ; try congruence; clear Hlsrcv.
      all: simplify_map_eq.
      all: (iSplitR "Hφ Hmap Hmem"
            ; [ iExists lr, lm, vmap,_,_,_; iFrame; auto
              | iApply "Hφ" ; iFrame ; iFailCore Hash_fail_const

           ]).
    }
    destruct_lword lsrcv ; try (cbn in * ; congruence).
    cbn in Hstep.


    destruct (readAllowed p) eqn:HaRead; cycle 1; cbn in *.
    {
      simplify_map_eq.
      iSplitR "Hφ Hmap Hmem"
            ; [ iExists lr, lm, vmap,_,_,_; iFrame; auto
              | iApply "Hφ" ; iFrame ; iFailCore Hash_fail_perm
        ].
    }

    set (lregs' := (<[ dst := LInt (hash_lmemory_region lm b e v) ]> lregs)).
    set (lr' := (<[ dst := LInt (hash_lmemory_region lm b e v) ]> lr)).
    assert (lreg_strip lregs' ⊆ lreg_strip lr') as Hlregs'_in_lr'.
    { subst lregs' lr'.
      by apply map_fmap_mono, insert_mono.
    }


    assert ( (lreg_strip lr') =
               (<[ dst := WInt (hash_memory_region mem b e) ]> reg))
      as Hstrip_lr'.
    { subst lr'.
      destruct HLinv as [ [Hstrips Hcurreg] _].
      rewrite -Hstrips /lreg_strip !fmap_insert -/(lreg_strip lr) //=.
      erewrite lmeasure_measure; eauto.
    }

    destruct (incrementLPC lregs') as  [?|] eqn:Hlregs'
    ; pose proof Hlregs' as H'lregs'
    ; cycle 1.
    {
      apply incrementLPC_fail_updatePC with (m:=mem) (etbl:=etable) (ecur:=enumcur) in Hlregs'.
      eapply updatePC_fail_incl with
        (regs' := lreg_strip lr') (m':=mem)
        (etbl':=etable) (ecur':=enumcur) in Hlregs'
      ; auto
      ; cycle 1.
      {
        rewrite /lreg_strip lookup_fmap.
        subst lregs' lr'.
        apply fmap_is_Some.
        destruct (decide (dst = PC)); simplify_map_eq ; auto.
      }
      rewrite Hstrip_lr' in Hlregs'.
      match goal with
      | Hstep :
        match ?x with _ => _ end = (_,_) |- _ =>
          replace x with (None : option Conf) in Hstep
            by (destruct_lword lsrcv ; eauto)
      end
      ; simplify_eq.
      subst lr'.

      iSplitR "Hφ Hmap Hmem"
      ; [ iExists lr, lm, vmap,_,_,_; iFrame; auto
        | iApply "Hφ" ; iFrame].
      eapply allow_hash_implies_hashv in HaHash; eauto.
      subst lregs'.
      rewrite {1}(hash_lmemory_weaken lmem lm) in H'lregs'; eauto.
      cbn in *; iFailCore Hash_fail_invalid_PC.
    }

    (* PC has been incremented correctly *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementLPC_success_updatePC _ mem etable enumcur) in Hlregs'
        as (p1 & b1 & e1 & a1 & a_pc1 & v1 & HPC'' & Ha_pc' & HuPC & ->)
    ; simplify_map_eq.
    assert (dst <> PC) as Hdst by (subst lregs' ; intro ; simplify_map_eq).
    eapply updatePC_success_incl with
      (regs' := lreg_strip lr') (m':=mem) (etbl':=etable) (ecur':=enumcur) in HuPC
    ; auto.
    rewrite Hstrip_lr' in HuPC.
    rewrite HuPC in Hstep; clear HuPC.
    subst lregs' lr' ; simplify_eq ; simplify_map_eq.
    eapply allow_hash_implies_hashv in HaHash; eauto.


    iMod ((gen_heap_update_inSepM _ _ dst (LInt (hash_lmemory_region lm b e v))) with "Hr Hmap")
      as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC (LCap p1 b1 e1 a_pc1 v1)) with "Hr Hmap")
      as "[Hr Hmap]"; eauto ; first by simplify_map_eq.

    rewrite {1}(hash_lmemory_weaken lmem lm) in H'lregs'; eauto.


    iFrame; iModIntro ; iSplitR "Hφ Hmap Hmem"
    ; [| iApply "Hφ" ; iFrame; iPureIntro ; eapply Hash_spec_success; eauto]; cycle 1.
    { split; eauto. }

    iExists _, lm, vmap,_,_,_; iFrame; auto
    ; iPureIntro; econstructor; eauto
    ; repeat (split ; first done)
    ; destruct HLinv as [ [Hstrips Hcur_reg] [Hdom Hroot] ]
    ; cbn in *
    ; last (split;eauto)
    ; last done.
    assert ( is_cur_word (LCap p1 b1 e1 a_pc1 v1) vmap ) as Hcur_PC.
    { eapply lookup_weaken in HPC'' ; eauto.
      eapply is_cur_lword_lea with (a' := a_pc1) ; cycle 2 ; eauto ; apply isWithin_refl.
    }
    erewrite lmeasure_measure; eauto.
    eapply lreg_corresponds_insert_respects; eauto.
    eapply lreg_corresponds_insert_respects; done.
  Qed.

  (* TODO old proof *)
  (*   iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaHash φ) "(>Hmem & >Hregs) Hφ". *)
  (*   rewrite -(insert_id lmem _ _ Hmem_pc). *)
  (*   iDestruct (big_sepM_insert_delete with "Hmem") as "[Hpc_a Hmem]"; cbn. *)

  (*   iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hregs Hmem Hφ]"). *)

  (*   iModIntro. *)
  (*   iIntros (σ) "(Hσ & Hregs &Hpc_a)". *)
  (*   iModIntro. *)
  (*   iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred". *)

  (*   iApply (wp_wp2 (φ1 := exec_optL_Hash lregs lmem dst src)). *)
  (*   iApply wp_opt2_bind. *)
  (*   iApply wp_opt2_eqn. *)

  (*   iDestruct (big_sepM_insert_delete _ _ _ lw with "[Hpc_a $Hmem]") as "Hmem"; iFrame. *)
  (*   rewrite insert_id; auto. *)
  (*   iMod (state_interp_transient_intro_nodfracs with "[$Hregs $Hσ $Hmem]") as "Hσ". *)

  (*   iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred]") ; first by set_solver. *)
  (*   iIntros (lw2) "Hσ %Hlrs %Hrs". *)

  (*   destruct (is_log_cap lw2) eqn:Hlw2; cycle 1. *)
  (*   { *)
  (*     destruct_lword lw2 ; cbn in * ; simplify_eq. *)
  (*     all: iModIntro. *)
  (*     all: iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". *)
  (*     all: rewrite big_sepM_fmap. *)
  (*     all: iApply ("Hφ" with "[$Hmem $Hregs]"). *)
  (*     all: iPureIntro; constructor; by eapply Hash_fail_const. *)
  (*   } *)

  (*   destruct_lword lw2 ; cbn in * ; simplify_eq. *)
  (*   destruct (decide (readAllowed p = true)) as [Hread|Hread] *)
  (*   ; [|apply not_true_is_false in Hread] ; rewrite Hread ;cycle 1;cbn. *)
  (*   { *)
  (*     iModIntro. *)
  (*     iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". *)
  (*     rewrite big_sepM_fmap. *)
  (*     iApply ("Hφ" with "[$Hmem $Hregs]"). *)
  (*     iPureIntro; constructor; by eapply Hash_fail_perm. *)
  (*   } *)

  (*   pose proof (allow_hash_implies_hashv _ _ _ _ _ _ _ _ HaHash Hlrs Hread) as Hhash_mem. *)

  (*   rewrite updatePC_incrementPC. *)
  (*   iApply (wp_opt2_bind (k1 := fun x => Some x)). *)
  (*   iApply wp_opt2_eqn_both. *)

  (*   iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LInt (hash_lmemory_region lmem b e v)) with "Hσ") as "Hσ". *)
  (*   { set_solver. } *)
  (*   { by cbn. } *)

  (*   replace (WInt (hash_memory_region (mem σ) b e)) *)
  (*     with ( lword_get_word  (LInt (hash_lmemory_region lmem b e v))). *)
  (*   2:{ cbn. admit. } *)


  (*   iApply (wp2_opt_incrementPC with "[$Hσ Hcred Hφ]"). *)
  (*   { now rewrite elem_of_dom (lookup_insert_dec HPC). } *)
  (*   iSplit; cbn; iIntros (φt' lrt') "Hσ %Heqn1 %Heqn2". *)
  (*   - iDestruct (state_interp_transient_elim_abort with "Hσ") as "($ & Hregs & Hmem)". *)
  (*     rewrite big_sepM_fmap. *)
  (*     iApply ("Hφ" with "[$Hmem $Hregs]"). *)
  (*     iPureIntro. *)
  (*     eapply Hash_spec_failure. *)
  (*     by econstructor. *)
  (*   - iApply wp2_val. *)
  (*     cbn. *)
  (*     iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & Hmem)". *)
  (*     rewrite big_sepM_fmap. *)
  (*     iApply ("Hφ" with "[$Hmem $Hregs]"). *)
  (*     iPureIntro. *)
  (*     eapply Hash_spec_success; eauto. *)
  (*     split;eauto. *)
  (* Admitted. *)

(* Global Instance laddr_eqdec: EqDecision LAddr. *)
(* Proof. apply _. Defined. *)
(* Global Instance laddr_countable: Countable LAddr. *)
(* Admitted. *)


  Lemma wp_hash_success Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst src
    wdst p b e a v ws lw
    :

    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    (pc_a + 1)%a = Some pc_a' →
    pc_a ∉ finz.seq_between b e ->
    length ws = finz.dist b e ->

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ LCap p b e a v
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWInt (hash (lword_get_word <$> ws))
          ∗ src ↦ᵣ LCap p b e a v
          ∗ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
      }}}.
  Proof.
    intros Hdecode HcorrectPC Hread_allowed Hpca' Hpca_ne Hlen_ws.
    iIntros (φ) "(>HPC & >Hpca & >Hdst & >Hsrc & >Hmem) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    rewrite /region_mapsto.
    iDestruct ( big_sepL2_to_big_sepM with "Hmem") as "Hmem".
    { apply NoDup_fmap_2.
      - intros a1 a2 Haeq; congruence.
      - by apply finz_seq_between_NoDup.
    }
    iDestruct (big_sepM_insert with "[$Hmem $Hpca]") as "Hmem".
    { shelve. }

    iApply (wp_hash with "[$]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    {
      rewrite /allow_hash_map_or_true.
      exists p,b,e,a,v.
      split.
      - rewrite /read_reg_inr.
        rewrite lookup_insert_ne //.
        rewrite lookup_insert_ne //.
        by simplify_map_eq.
      - match goal with
        | H: _ |- context [decide ?x] => destruct (decide x)
        end; last done.
        apply Forall_forall.
        intros a' Ha'.
        destruct (decide (a' = pc_a)); simplify_map_eq.
        rewrite lookup_insert_ne; last congruence.
        rewrite -/(is_Some (_ !! (a',v))).
        apply elem_of_dom.
        rewrite dom_list_to_map_L.
        apply elem_of_list_to_set.
        rewrite fst_zip.
        2: { by rewrite Hlen_ws map_length finz_seq_between_length. }
        apply elem_of_list_fmap.
        eexists ; split; done.
    }
    iNext. iIntros (lregs' retv) "(%Hspec & Hmem & Hregs)".
    destruct Hspec; cycle 1.
    { destruct X; simplify_map_eq; try congruence.
      incrementLPC_inv; simplify_map_eq; eauto; congruence.
    }
    iApply "Hφ".
    incrementLPC_inv; simplify_map_eq; eauto.
    rewrite (insert_commute _ PC dst) // insert_insert.
    rewrite (insert_commute _ dst PC) // insert_insert.
    iDestruct (regs_of_map_3 with "Hregs") as "(?&?&?)"; eauto; iFrame.

    replace
      (hash_lmemory_region (<[(x2, x3):=lw]> (list_to_map (zip (map (λ a1 : Addr, (a1, v)) (finz.seq_between b e)) ws))) b0 e0 v0)
      with (hash (lword_get_word <$> ws)).
    2: {
      rewrite /hash_lmemory_region.
      f_equal.
      f_equal.
      destruct H2 as [? _]; simplify_map_eq.
      rewrite map_filter_insert_not; cycle 1.
      { intros w' [ ? ? ]; cbn in *; simplify_eq. }


      Set Nested Proofs Allowed.
  Lemma map_filter_alt':
    ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)}
      {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)}
      {EqDecision0 : EqDecision K},
      FinMap K M
    → ∀ {A : Type} (P : K * A → Prop) {H7 : ∀ x : K * A, Decision (P x)}
        (l : list (K * A)),
        NoDup l ->
        filter P l = map_to_list (filter P (list_to_map l)).
    Proof.
      intros * ? * Hnodup.
      induction l; cbn.
      - by rewrite map_filter_empty map_to_list_empty.
      - apply NoDup_cons in Hnodup. destruct Hnodup as [Hal Hnodup].
        destruct a as [a1 a2].
        destruct (decide (P (a1,a2))); rewrite IHl; auto.
        + rewrite map_filter_insert_True; last done.
          admit.
        + rewrite map_filter_insert_False; last done.
          admit.
    Admitted.
    admit.
    (* rewrite map_filter_alt'. *)
    }
    iFrame.
    iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]".
    { apply not_elem_of_list_to_map.
      rewrite fst_zip.
      2: { by rewrite Hlen_ws map_length finz_seq_between_length. }
      intro Hcontra.
      apply elem_of_list_fmap in Hcontra.
      destruct Hcontra as [? [? ?] ]; simplify_eq.
    }
    iFrame.
    iDestruct ( big_sepM_to_big_sepL2 with "Hmem") as "Hmem".
    { apply NoDup_fmap_2.
      - intros a1 a2 Haeq; congruence.
      - by apply finz_seq_between_NoDup.
    }
    { by rewrite Hlen_ws map_length finz_seq_between_length. }
    iFrame.

    Unshelve.
    {
      apply not_elem_of_list_to_map_1.
      intro Hcontra.
      eapply fst_elem_of_cons, elem_of_list_fmap in Hcontra.
      destruct Hcontra as [? [? ?] ]; simplify_eq.
    }
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
          ∗ dst ↦ᵣ LWInt (hash (lword_get_word <$> ws))
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
          ∗ dst ↦ᵣ LWInt (hash (lword_get_word <$> (ws++[lw]++ws')))
          ∗ src ↦ᵣ LCap p b e a v
          ∗ [[ b , pc_a ]] ↦ₐ{ v } [[ ws ]]
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ [[ pc_a' , e ]] ↦ₐ{ v } [[ ws' ]]
      }}}.
  Proof.
  Admitted.

End cap_lang_rules.
