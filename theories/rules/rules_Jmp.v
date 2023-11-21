From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base register_tactics.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Jmp_failure (regs: Reg) (r: RegName) (mem : gmap Addr Word) :=
  | Jmp_fail_bounds b e a:
      regs !! r = Some (WCap IE b e a) ->
      (withinBounds b e a = false \/ withinBounds b e (a^+1)%a = false) →
      Jmp_failure regs r mem
  .

  Inductive Jmp_spec
    (regs: Reg) (r: RegName)
    (regs': Reg) (mem : gmap Addr Word) : cap_lang.val → Prop
  :=
  | Jmp_spec_success_IE b e a wpc widc :
    regs !! r = Some (WCap IE b e a) ->
    withinBounds b e a = true ->
    withinBounds b e (a^+1)%a = true ->
    mem !! a = Some wpc ->
    mem !! (a^+1)%a = Some widc ->
    regs' = ( <[ idc := widc ]> (<[ PC := wpc ]> regs)) ->
    Jmp_spec regs r regs' mem NextIV

  | Jmp_spec_success w :
    regs !! r = Some w ->
    is_ie_cap w = false ->
    regs' = <[ PC := updatePcPerm w]> regs ->
    Jmp_spec regs r regs' mem NextIV

  | Jmp_spec_failure :
    Jmp_failure regs r mem ->
    Jmp_spec regs r regs' mem FailedV.


  Definition reg_allows_IE_jmp (regs : Reg) (r : RegName) p b e a :=
    regs !! r = Some (WCap p b e a)
    /\ p = IE
    ∧ withinBounds b e a = true
    ∧ withinBounds b e (a^+1)%a = true.

  Definition allow_jmp_mmap_or_true (r : RegName) (regs : Reg) (mem : Mem):=
    ∃ p b e a, read_reg_inr regs r p b e a ∧
                 if decide (reg_allows_IE_jmp regs r p b e a) then
                   ∃ w1 w2,
                     mem !! a = Some w1
                     /\ mem !! (a^+1)%a = Some w2
                 else True.

  Definition allow_jmp_rmap_or_true (r : RegName) (regs : Reg) :=
    ∃ p b e a, read_reg_inr regs r p b e a ∧
                 if decide (reg_allows_IE_jmp regs r p b e a) then
                   ∃ widc, regs !! idc = Some widc
                 else True.

  Lemma wp_jmp Ep pc_p pc_b pc_e pc_a r w mem regs  :
    decodeInstrW w = Jmp r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    allow_jmp_mmap_or_true r regs mem ->
    allow_jmp_rmap_or_true r regs ->
    regs_of (Jmp r) ⊆ dom regs →
    mem !! pc_a = Some w →

    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
          ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
      {{{ regs' retv, RET retv;
          ⌜ Jmp_spec regs r regs' mem retv⌝ ∗
            ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
            [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hmmap Hrmap Dregs Hmem_pc φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r) as [rv [Hr' _]]; first set_solver+. clear Hri.
    (* Derive the PC in memory *)
    iDestruct (gen_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    rewrite /exec /= in Hstep.

    (* Now we start splitting on the different cases in the Jmp spec, and prove them one at a time *)
    assert (Hr0 : r0 !! r = Some rv).
    { eapply (lookup_weaken regs r0) ;auto. }
    destruct (is_ie_cap rv) eqn:Hrv.
    - (* rv is an IE-capability *)
      destruct rv; simpl in Hrv; try discriminate.
      destruct sb as [ p b e a |]; simpl in Hrv; try discriminate.
      destruct p; try discriminate ; clear Hrv.

      (*  destruct the bounds *)
      destruct (decide (withinBounds b e a && withinBounds b e (a ^+ 1)%a)) as
        [Hbounds%Is_true_true | Hbounds%Is_true_false]
      ; (rewrite Hr0 /= Hbounds /= in Hstep).

      + (* in bounds, success *)
        pose proof Hr' as Hr.
        destruct Hmmap as (p'&b'&e'&a'& Hrinr & HallowLoad).
        destruct Hrmap as (p''&b''&e''&a''& Hrinr' & HallowLoad').

        rewrite /read_reg_inr in Hrinr, Hrinr'.
        rewrite Hr in Hrinr, Hrinr'; symmetry in Hrinr, Hrinr' ; simplify_eq.

        case_decide as Hdec ; last simplify_map_eq.
        2: { exfalso; apply Hdec.
             symmetry in Hbounds; apply andb_true_eq in Hbounds ; destruct Hbounds.
             repeat (split ; auto). }
        destruct Hdec as (Hreg & _ & _ & _).
        destruct HallowLoad as (wpc & widc & HaLoad & Ha'Load).
        destruct HallowLoad' as (w' & Hidc).

        iDestruct (gen_mem_valid_inSepM mem m a wpc with "Hm Hmem" ) as %Hma'
        ; eauto.
        iDestruct (gen_mem_valid_inSepM mem m (a^+1)%a widc with "Hm Hmem" ) as %Hma''
        ; eauto.
        rewrite Hma' Hma'' /= in Hstep; simplify_pair_eq ; simpl.
        iMod ((gen_heap_update_inSepM _ _ PC wpc) with "Hr Hmap") as "[Hr Hmap]"; eauto.
        iMod ((gen_heap_update_inSepM _ _ idc widc) with "Hr Hmap") as
          "[Hr Hmp]" ; eauto.
        { apply lookup_insert_is_Some'; right; auto. }
        iFrame; try iApply "Hφ"; iFrame.
        apply andb_true_iff in Hbounds ; destruct Hbounds as [Hbounds_a Hbounds_a'].
        iPureIntro; eapply Jmp_spec_success_IE; eauto.

      + (* in bounds, failure *)
        simplify_pair_eq; iFrame; iApply "Hφ"; iFrame.
        iPureIntro; eapply Jmp_spec_failure ; econstructor ; eauto.
        by apply andb_false_iff.


    - (* rv is not an IE-capability, always success *)
      rewrite Hr0 /= in Hstep; simplify_pair_eq.
      (* TODO better way to do thus, using match goal ?? *)
      rewrite (_ :
                match rv with
                | WCap IE b e a =>
                    if withinBounds b e a && withinBounds b e (a ^+ 1)%a
                    then
                      m !! a
                        ≫= (λ wpc : Word,
                               m !! (a ^+ 1)%a
                                 ≫= (λ widc : Word,
                                        Some (NextI, update_reg (update_reg (r0, m) PC wpc) idc widc)))
                    else None
                | _ => Some (NextI, update_reg (r0, m) PC (updatePcPerm rv))
                end = Some (NextI, update_reg (r0, m) PC (updatePcPerm rv))) in
        Hstep.
      2: {
        destruct rv ; cbn in Hrv; try discriminate; auto.
        destruct sb as [ p b e a |]; cbn in Hrv; try discriminate; auto.
        destruct p; try discriminate ; auto.
      }

      simplify_pair_eq; simpl.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame.
      iApply "Hφ". iFrame.
      iPureIntro; eapply Jmp_spec_success; eauto.
  Qed.

  Lemma wp_jmp_success E pc_p pc_b pc_e pc_a w r w' :
    decodeInstrW w = Jmp r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    is_ie_cap w' = false ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r ↦ᵣ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm w'
            ∗ pc_a ↦ₐ w
            ∗ r ↦ᵣ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hw' ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".

    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hreg %Hr]".
    iApply (wp_jmp with "[$Hmem $Hreg]"); eauto ; simplify_map_eq; eauto.
    {
      destruct_word w'; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    {
      destruct_word w'; eauto; eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: try destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { by rewrite !dom_insert; set_solver+. }

    iNext.
    iIntros (regs retv) "(%& Hmem & Hreg)".
    inversion H2; simplify_map_eq.
    - (* Success not IE *)
      iExtractList "Hreg" [PC;r] as ["HPC"; "Hr"].
      iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
      iApply "Hφ" ; iFrame.
    - (* Failure - contradiction *)
      exfalso.
      inversion H3.
      rewrite (_: <[PC:=WCap pc_p pc_b pc_e pc_a]> (<[r:=w']> ∅) !! r = Some w')
        in H4 ; [| by simplify_map_eq].
      injection H4 ; intros ->.
      simpl in Hw' ; congruence.
      Unshelve. all: eauto.
  Qed.

  Lemma wp_jmp_successPC E pc_p pc_b pc_e pc_a w :
    decodeInstrW w = Jmp PC →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ updatePcPerm (WCap pc_p pc_b pc_e pc_a)
           ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ".

    iDestruct (memMap_resource_1 with "Hpc_a") as "Hmem".
    iDestruct (map_of_regs_1 with "HPC") as "Hreg".
    iApply (wp_jmp with "[$Hmem $Hreg]"); eauto ; simplify_map_eq; eauto.
    (* TODO better way to derive them *)
    { apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    { apply isCorrectPC_not_ie_cap in Hvpc.
      eexists _,_,_,_; split
      ;try (rewrite /read_reg_inr ; simplify_map_eq; auto).
      rewrite /reg_allows_IE_jmp ; simplify_map_eq ; auto.
      all: case_decide as Heq ; simplify_eq ; auto.
      all: destruct Heq as (? & -> & ? & ?) ; simplify_map_eq.
      all: try destruct Heq as (? & _) ; simplify_map_eq.
    }
    iNext.
    iIntros (regs retv) "(%& Hmem & Hreg)".
    inversion H2; simplify_map_eq.
    - (* Success IE - contradiction *)
      inversion Hvpc ; destruct H11 ; congruence.
    - (* Success not IE *)
      iExtractList "Hreg" [PC] as ["HPC"].
      iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a _]"; auto.
      iApply "Hφ" ; iFrame.
    - (* Failure - contradiction *)
      exfalso.
      inversion H3.
      simplify_map_eq.
      inversion Hvpc ; destruct H10 ; congruence.
  Qed.

  (* TODO we need to do more cases (for _automation_), where:
       - r = idc
       - pc_a = a
       - pc_a = a+1
       - fail ?
   *)
  Lemma wp_jmp_success_IE E pc_p pc_b pc_e pc_a w r b e a w' wpc widc :
    decodeInstrW w = Jmp r →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     withinBounds b e a ->
     withinBounds b e (a^+1)%a ->

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ r ↦ᵣ WCap IE b e a
         ∗ ▷ idc ↦ᵣ w'
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ a ↦ₐ wpc
         ∗ ▷ (a^+1)%a ↦ₐ widc
     }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ wpc
         ∗ r ↦ᵣ WCap IE b e a
         ∗ idc ↦ᵣ widc
         ∗ pc_a ↦ₐ w
         ∗ a ↦ₐ wpc
         ∗ (a^+1)%a ↦ₐ widc }}}.
    Proof.
    iIntros (Hinstr Hvpc Hbound_a Hbound_a' ϕ)
      "(>HPC  & >Hr & >Hidc & >Hpc_a & >Ha & >Ha') Hφ".

    iDestruct (address_neq with "Ha' Hpc_a") as "%Ha'".
    iDestruct (address_neq with "Ha Ha'") as "%Hneqa".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Ha") as "[Hmem %Ha]".
    iDestruct (big_sepM_insert with "[Ha' Hmem]") as "Hmem" ; [| iFrame |].
    by simplify_map_eq.
    iDestruct (map_of_regs_3 with "HPC Hr Hidc") as "[Hreg %Hr']".
    destruct Hr' as (?&?&?).
    iApply (wp_jmp with "[$Hmem $Hreg]"); eauto ; simplify_map_eq; eauto.
    {
      eexists IE,b,e,a.
      split ; auto.
      unfold read_reg_inr; by simplify_map_eq.
      case_decide; auto.
      eexists _,_.
      split ; by simplify_map_eq.
    }
    {
      eexists IE,b,e,a.
      split ; auto.
      unfold read_reg_inr; by simplify_map_eq.
      case_decide; auto.
      eexists _; by simplify_map_eq.
    }
    { by rewrite !dom_insert; set_solver+. }

    iNext.
    iIntros (regs retv) "(%Hspec& Hmem & Hreg)".
    inversion Hspec; simplify_map_eq.
    - (* Success IE *)
      iApply "Hφ".
      iExtractList "Hreg" [PC;idc;r] as ["HPC"; "Hidc" ; "Hr"].
      iDestruct (big_sepM_insert with "Hmem") as "[Ha' Hmem]"; auto ; [ by simplify_map_eq|].
      iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a Hmem]"; auto ; [ by simplify_map_eq|].
      iDestruct (big_sepM_insert with "Hmem") as "[Ha _]"; auto.
      iFrame.
    - (* Failure - contradiction *)
      exfalso.
      inversion H5; simplify_map_eq.
      apply Is_true_true_1 in Hbound_a.
      apply Is_true_true_1 in Hbound_a'.
      destruct H7; congruence.
  Qed.

  Lemma wp_jmp_success_IE_same_idc E pc_p pc_b pc_e pc_a w b e a wpc widc :
    decodeInstrW w = Jmp idc →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    withinBounds b e a ->
    withinBounds b e (a^+1)%a ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ idc ↦ᵣ WCap IE b e a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ a ↦ₐ wpc
          ∗ ▷ (a^+1)%a ↦ₐ widc
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ wpc
            ∗ idc ↦ᵣ widc
            ∗ pc_a ↦ₐ w
            ∗ a ↦ₐ wpc
            ∗ (a^+1)%a ↦ₐ widc }}}.
  Proof.
  Admitted.

  (* TODO move jmp_rules.v *)
  Lemma wp_jmp_fail_IE_same_idc E pc_p pc_b pc_e pc_a w b e a :
    decodeInstrW w = Jmp idc →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    not (withinBounds b e a /\ withinBounds b e (a^+1)%a) ->

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ idc ↦ᵣ WCap IE b e a
          ∗ ▷ pc_a ↦ₐ w
    }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
            ∗ idc ↦ᵣ WCap IE b e a
            ∗ pc_a ↦ₐ w
      }}}.
  Proof.
  Admitted.

End cap_lang_rules.
