From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Import machine_base.
From cap_machine Require Export rules_base region logical_mapsto.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{reservedaddresses : ReservedAddresses}.
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

  Inductive Hash_spec (lregs: LReg) (dst src: RegName) (lregs': LReg): cap_lang.val -> Prop :=
  | Hash_spec_success lwsrc :
    lregs !! src = Some lwsrc ->
    incrementLPC (<[ dst := LWInt (hash (lword_get_word lwsrc))]> lregs) = Some lregs' ->
    Hash_spec lregs dst src lregs' NextIV
  | Hash_spec_failure lwsrc:
    incrementLPC (<[ dst := LWInt (hash (lword_get_word lwsrc))]> lregs) = None →
    Hash_spec lregs dst src lregs' FailedV.

  Definition exec_optL_Hash
    (lregs : LReg) (dst src : RegName) : option LReg :=
    lwsrc ← lregs !! src;
    lpc ← incrementLPC (<[dst := LWInt (hash (lword_get_word lwsrc)) ]> lregs) ;
    Some lpc.

  (* Lemma hash_lmemory_weaken lmem lm b e v : *)
  (*   Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) (finz.seq_between b e) -> *)
  (*   lmem ⊆ lm -> *)
  (*   (hash_lmemory_region lm b e v) = *)
  (*   (hash_lmemory_region lmem b e v). *)
  (* Proof. *)
  (*   revert lm. *)
  (*   rewrite /hash_lmemory_region. *)
  (*   induction lmem using map_ind; intros lm Hall Hmem. *)
  (*   - f_equal. *)
  (*     match goal with | _ : _ |- context [ (filter ?f lm) ] => set (Flm := f) end. *)
  (*     pose proof (map_filter_empty_iff Flm lm) as [_ HFlm]. *)
  (*     rewrite HFlm. *)
  (*     + by rewrite map_filter_empty map_to_list_empty !fmap_nil. *)
  (*     + subst Flm. *)
  (*       apply map_Forall_lookup_2. *)
  (*       intros [a v'] lw Hlw; cbn. *)
  (*       intro Hcontra. *)
  (*       destruct Hcontra as [Hcontra ->]. *)
  (*       rewrite Forall_forall in Hall. *)
  (*       apply Hall in Hcontra. *)
  (*       set_solver. *)
  (*   - f_equal. *)
  (*     match goal with | _ : _ |- context [ (filter ?f lm) ] => set (Flm := f) end. *)
  (*     assert (lm = (<[i := x]> lm)) as Hlm_eq. *)
  (*     { rewrite insert_id; first done. *)
  (*       by eapply insert_weaken. *)
  (*     } *)
  (*     rewrite Hlm_eq. *)
  (*     apply insert_subseteq_r_inv in Hmem ; auto. *)
  (*     rewrite !map_filter_insert. *)
  (*     destruct (decide (Flm (i, x))). *)
  (*     + admit. *)
  (*     + rewrite !map_filter_delete. *)
  (* Admitted. *)

  Lemma wp_hash Ep
    pc_p pc_b pc_e pc_a pc_v
    dst src lw lregs :
    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (Hash dst src) ⊆ dom lregs →

    {{{ ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ lregs' retv, RET retv;
          ⌜ Hash_spec lregs dst src lregs' retv⌝ ∗
          (pc_a, pc_v) ↦ₐ lw ∗
          [∗ map] k↦y ∈ lregs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".

    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpc_a $Hmap Hφ]").
    iModIntro.
    iIntros (σ) "(Hσ & Hregs &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hppc & %Hpmema & %Hcorrpc & %Hdinstr) Hcred".

    iApply (wp_wp2 (φ1 := exec_optL_Hash lregs dst src)).
    iApply wp_opt2_bind.
    iApply wp_opt2_eqn.
    iDestruct (state_interp_transient_intro (lm:= ∅) with "[$Hregs $Hσ]") as "Hσ". set_solver.
    iApply (wp2_reg_lookup (lrt := lregs)); first by set_solver.
    iModIntro.
    iFrame "Hσ".
    iIntros (lwr) "Hσ %Hlrs %Hrs".

    iDestruct (update_state_interp_transient_from_regs_mod (dst := dst) (lw2 := LInt (hash (lword_get_word lwr))) with "Hσ") as "Hσ".
    { now set_solver. }
    { now intros. }

    rewrite updatePC_incrementPC.
    iApply (wp_opt2_bind (φ1 := incrementLPC (<[ dst := LInt (hash (lword_get_word lwr))]> lregs)) (k1 := (fun x => Some x))).
    iApply wp_opt2_eqn_both.

    iApply (wp2_opt_incrementPC with "[$Hσ Hpc_a Hφ]").
    { rewrite dom_insert. apply elem_of_union_r. now rewrite elem_of_dom HPC. }
    iSplit.
    - iIntros "Hσ %Hlin %Hin".
      iDestruct (state_interp_transient_elim_abort with "Hσ") as "(Hσ & Hregs & _)".
      iFrame.
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      by eapply Hash_spec_failure.
    - iIntros (regs' φt') "Hσ %Hlis %His".
      iApply wp2_val.
      cbn.
      iMod (state_interp_transient_elim_commit with "Hσ") as "($ & Hregs & _)".
      iApply ("Hφ" with "[$Hpc_a $Hregs]").
      iPureIntro.
      eapply Hash_spec_success; try eassumption.
  Qed.

  Lemma wp_hash_success Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst src
    wdst wsrc lw
    :

    decodeInstrWL lw = Hash dst src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ wsrc
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWInt (hash (lword_get_word wsrc))
          ∗ src ↦ᵣ wsrc
      }}}.
  Proof.
    intros Hdecode HcorrectPC Hpca'.
    iIntros (φ) "(>HPC & >Hpca & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    rewrite /region_mapsto.
    iApply (wp_hash with "[$]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lregs' retv) "(%Hspec & Hpca & Hregs)".
    destruct Hspec; cycle 1.
    { incrementLPC_inv; simplify_map_eq; eauto; congruence. }
    iApply "Hφ".
    incrementLPC_inv; simplify_map_eq; eauto.
    rewrite (insert_commute _ PC dst) // insert_insert.
    rewrite (insert_commute _ dst PC) // insert_insert.
    iDestruct (regs_of_map_3 with "Hregs") as "(?&?&?)"; eauto; iFrame.
  Qed.

  Lemma wp_hash_success_same Ep pc_p pc_b pc_e pc_a pc_a' pc_v lw src wsrc :

    decodeInstrWL lw = Hash src src →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ src ↦ᵣ wsrc
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
          ∗ (pc_a, pc_v) ↦ₐ lw
          ∗ src ↦ᵣ LWInt (hash (lword_get_word wsrc))
      }}}.
  Proof.
    intros Hdecode HcorrectPC Hpca'.
    iIntros (φ) "(>HPC & >Hpca & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    rewrite /region_mapsto.
    iApply (wp_hash with "[$]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lregs' retv) "(%Hspec & Hpca & Hregs)".
    destruct Hspec; cycle 1.
    { incrementLPC_inv; simplify_map_eq; eauto; congruence. }
    iApply "Hφ".
    incrementLPC_inv; simplify_map_eq; eauto.
    rewrite (insert_commute _ PC src) // insert_insert.
    rewrite (insert_commute _ src PC) // insert_insert.
    iDestruct (regs_of_map_2 with "Hregs") as "(?&?)"; eauto; iFrame.
  Qed.

  (* Lemma wp_hash_success_overlapPC Ep *)
  (*   pc_p pc_b pc_e pc_a pc_a' pc_v *)
  (*   dst src *)
  (*   wdst p b e a v ws ws' lw *)
  (*   : *)

  (*   decodeInstrWL lw = Hash dst src → *)
  (*   isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) → *)
  (*   readAllowed p = true → *)
  (*   (pc_a + 1)%a = Some pc_a' → *)

  (*   {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v *)
  (*       ∗ ▷ dst ↦ᵣ wdst *)
  (*       ∗ ▷ src ↦ᵣ LCap p b e a v *)
  (*       ∗ ▷ [[ b , pc_a ]] ↦ₐ{ v } [[ ws ]] *)
  (*       ∗ ▷ (pc_a, pc_v) ↦ₐ lw *)
  (*       ∗ ▷ [[ pc_a' , e ]] ↦ₐ{ v } [[ ws' ]] *)
  (*   }}} *)
  (*     Instr Executable @ Ep *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v *)
  (*         ∗ dst ↦ᵣ LWInt (hash (lword_get_word <$> (ws++[lw]++ws'))) *)
  (*         ∗ src ↦ᵣ LCap p b e a v *)
  (*         ∗ [[ b , pc_a ]] ↦ₐ{ v } [[ ws ]] *)
  (*         ∗ (pc_a, pc_v) ↦ₐ lw *)
  (*         ∗ [[ pc_a' , e ]] ↦ₐ{ v } [[ ws' ]] *)
  (*     }}}. *)
  (* Proof. *)
  (* Admitted. *)

End cap_lang_rules.
