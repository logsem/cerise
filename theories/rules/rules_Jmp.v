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
  | Jmp_spec_success_IE b e a wpc wddc :
    regs !! r = Some (WCap IE b e a) ->
    withinBounds b e a = true ->
    withinBounds b e (a^+1)%a = true ->
    mem !! a = Some wpc ->
    mem !! (a^+1)%a = Some wddc ->
    regs' = ( <[ ddc := wddc ]> (<[ PC := wpc ]> regs)) ->
    Jmp_spec regs r regs' mem NextIV

  | Jmp_spec_success w :
    regs !! r = Some w ->
    (forall p b e a, w = WCap p b e a -> p <> IE) ->
    regs' = <[ PC := updatePcPerm w]> regs ->
    Jmp_spec regs r regs' mem NextIV

  | Jmp_spec_failure :
    Jmp_failure regs r mem ->
    Jmp_spec regs r regs' mem FailedV.

  Definition allow_load_map_or_true r (regs : Reg) (mem : gmap Addr Word):=
    ∃ p b e a,
      read_reg_inr regs r p b e a ∧
        if decide
             (regs !! r = Some (WCap p b e a)
              /\ withinBounds b e a = true
              /\ withinBounds b e (a^+1)%a = true)
        then
          (∃ w, mem !! a = Some w) /\ (∃ w, mem !! (a^+1)%a = Some w)
        else True.

  Lemma wp_jmp
    Ep pc_p pc_b pc_e pc_a
    r w mem regs  :
    decodeInstrW w = Jmp r →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    regs !! PC = Some (WCap pc_p pc_b pc_e pc_a) →
    ( forall b' e' a', regs !! r = Some (WCap IE b' e' a') ->
                  is_Some (regs !! ddc) /\ allow_load_map_or_true r regs mem)->
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
    iIntros (Hinstr Hvpc HPC HDDC Dregs Hmem_pc φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[Hr Hm] /=". destruct σ1; simpl.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    feed destruct (Hri r) as [rv [Hr' _]]. by set_solver+. clear Hri.
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
    destruct (is_cap rv) eqn:Hrv.
    - (* rv is a capability, we need to destruct on permission *)
      destruct rv; simpl in Hrv; try discriminate.
      destruct sb as [ p b e a |]; simpl in Hrv; try discriminate ; clear Hrv.
      destruct (decide (p = IE)) as [Hp | Hp].
      + (* p = IE, we need to make sure that *)
        destruct (decide (withinBounds b e a && withinBounds b e (a ^+ 1)%a)) as
          [Hbounds%Is_true_true | Hbounds%Is_true_false]
          ; (rewrite Hr0 /= Hbounds /= in Hstep).
        * (* in bounds, success *)
        destruct p; simpl; simplify_pair_eq.
        pose proof Hr' as Hr.
        apply HDDC in Hr; clear HDDC.
        destruct Hr as [HDDC HaLoad].
        unfold allow_load_map_or_true in HaLoad.
        destruct HaLoad as (p' & b' & e' & a' & Hread_reg & HaLoad).
        unfold read_reg_inr in Hread_reg.
        rewrite Hr' in Hread_reg. injection Hread_reg ; intros ; subst
        ; clear Hread_reg.

        case_decide.
        2: { (* contradiction *)
          exfalso.
          apply andb_true_iff in Hbounds.
          apply H3; split ; auto.
        }
        destruct HaLoad as [[wpc Ha] [wddc Ha']].

        iDestruct (gen_mem_valid_inSepM mem m a' wpc with "Hm Hmem" ) as %Hma'
        ; eauto.

        iDestruct (gen_mem_valid_inSepM mem m (a'^+1)%a wddc with "Hm Hmem" ) as %Hma''
        ; eauto.
        rewrite Hma' Hma'' /= in Hstep.

        simpl; simplify_pair_eq.
        iMod ((gen_heap_update_inSepM _ _ PC wpc) with "Hr Hmap") as "[Hr Hmap]"; eauto.
        iMod ((gen_heap_update_inSepM _ _ ddc wddc) with "Hr Hmap") as
          "[Hr Hmp]" ; eauto.
        { apply lookup_insert_is_Some'; by right. }
        iFrame; try iApply "Hφ"; iFrame.
        apply andb_true_iff in Hbounds ; destruct Hbounds as [Hbounds_a Hbounds_a'].
        iPureIntro; eapply Jmp_spec_success_IE; eauto.

        * (* in bounds, failure *)
          destruct p; simpl; simplify_pair_eq.
          iFrame; try iApply "Hφ"; iFrame.
          iPureIntro; eapply Jmp_spec_failure ; econstructor ; eauto.
          by apply andb_false_iff.


      + (* p <> IE, so it doesn't fail *)
        (* Success *)
        rewrite Hr0 /= in Hstep.
        destruct p; simpl; simplify_pair_eq
        ; iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"
        ; eauto
        ; iFrame; try iApply "Hφ"; iFrame
        ; iPureIntro; eapply Jmp_spec_success; eauto
        ; intros * Hcontra ; injection Hcontra
        ; intros _ _ _ Hcontra' ; clear -Hcontra'; subst ; congruence.
    - (* rv is not capability, always success *)
      (* Success *)
      destruct rv; simpl in Hrv
      ; try (destruct sb; simpl in Hrv; try discriminate ; clear Hrv)
      ; rewrite Hr0 /= in Hstep; simplify_pair_eq
      ; try (iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"
      ; eauto
      ; iFrame; try iApply "Hφ"; iFrame
      ; iPureIntro; eapply Jmp_spec_success; eauto).
  Qed.

  Lemma wp_jmp_success E pc_p pc_b pc_e pc_a w r w' :
    decodeInstrW w = Jmp r →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (forall b e a, w' <> WCap IE b e a) ->

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
    { intros * Hcontra; injection Hcontra ; intros ; subst.
      specialize (Hw' b' e' a') ; congruence. }
    { by rewrite !dom_insert; set_solver+. }

    iNext.
    iIntros (regs retv) "(%& Hmem & Hreg)".
    inversion H2; simplify_map_eq.
    - (* Success IE - contradiction *)
      specialize (Hw' b e a) ; congruence.
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
      specialize (Hw' b e a) ; congruence.
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
    { intros * Hcontra; injection Hcontra ; intros ; subst.
      inversion Hvpc ; destruct H7 ; congruence. }
    { by rewrite !dom_insert; set_solver+. }

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


  (* TODO we need to do cases where:
       - r = ddc
       - pc_a = a
       - pc_a = a+1
   *)
  Lemma wp_jmp_success_IE E pc_p pc_b pc_e pc_a w r b e a w' wpc wddc :
    decodeInstrW w = Jmp r →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     withinBounds b e a = true ->
     withinBounds b e (a^+1)%a = true ->
     r <> ddc ->

     {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
         ∗ ▷ r ↦ᵣ WCap IE b e a
         ∗ ▷ ddc ↦ᵣ w'
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ a ↦ₐ wpc
         ∗ ▷ (a^+1)%a ↦ₐ wddc
     }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ wpc
         ∗ r ↦ᵣ WCap IE b e a
         ∗ ddc ↦ᵣ wddc
         ∗ pc_a ↦ₐ w
         ∗ a ↦ₐ wpc
         ∗ (a^+1)%a ↦ₐ wddc }}}.
    Proof.
    iIntros (Hinstr Hvpc Hbound_a Hbound_a' Hr ϕ)
      "(>HPC  & >Hr & >Hddc & >Hpc_a & >Ha & >Ha') Hφ".

    iDestruct (address_neq with "Ha' Hpc_a") as "%Ha'".
    iDestruct (address_neq with "Ha Ha'") as "%Hneqa".
    iDestruct (memMap_resource_2ne_apply with "Hpc_a Ha") as "[Hmem %Ha]".
    iDestruct (big_sepM_insert with "[Ha' Hmem]") as "Hmem" ; [| iFrame |].
    by simplify_map_eq.
    iDestruct (map_of_regs_3 with "HPC Hr Hddc") as "[Hreg %Hr']".
    destruct Hr' as (?&?&?).
    iApply (wp_jmp with "[$Hmem $Hreg]"); eauto ; simplify_map_eq; eauto.
    { intros * Hreg_r; simplify_map_eq.
      split ; auto.
      unfold allow_load_map_or_true. exists IE, b', e', a'.
      split.
      unfold read_reg_inr; by simplify_map_eq.
      case_decide as H' ; auto ; clear H'.
      split ; eexists ; by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }

    iNext.
    iIntros (regs retv) "(%Hspec& Hmem & Hreg)".
    inversion Hspec; simplify_map_eq.
    - (* Success IE *)
      iApply "Hφ".
      iExtractList "Hreg" [PC;ddc;r] as ["HPC"; "Hddc" ; "Hr"].
      iDestruct (big_sepM_insert with "Hmem") as "[Ha' Hmem]"; auto ; [ by simplify_map_eq|].
      iDestruct (big_sepM_insert with "Hmem") as "[Hpc_a Hmem]"; auto ; [ by simplify_map_eq|].
      iDestruct (big_sepM_insert with "Hmem") as "[Ha _]"; auto.
      iFrame.
    - (* Success not IE - contradiction *)
      exfalso ; by eapply H6.
    - (* Failure - contradiction *)
      exfalso.
      inversion H5; simplify_map_eq.
      destruct H7; congruence.
  Qed.

End cap_lang_rules.
