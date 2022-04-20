From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

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
  Implicit Types reg : gmap (CoreN * RegName) Word.
  Implicit Types ms : gmap Addr Word.

  Inductive IsPtr_spec (i: CoreN) (regs: Reg) (dst src: RegName) (regs': Reg): cap_lang.val -> Prop :=
  | IsPtr_spec_success (w: Word):
      regs !! (i, src) = Some w →
      incrementPC (<[ (i, dst) := WInt (if is_cap w then 1%Z else 0%Z) ]> regs) i = Some regs' ->
      IsPtr_spec i regs dst src regs' (i, NextIV)
  | IsPtr_spec_failure (w: Word):
      regs !! (i, src) = Some w →
      incrementPC (<[ (i, dst) := WInt (if is_cap w then 1%Z else 0%Z) ]> regs) i = None ->
      IsPtr_spec i regs dst src regs' (i, FailedV).

  Lemma wp_IsPtr Ep i pc_p pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = IsPtr dst src ->
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    regs !! (i, PC) = Some (WCap pc_p pc_b pc_e pc_a) →
    regs_of_core (IsPtr dst src) i ⊆ dom _ regs →
    
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (i, Instr Executable) @ Ep
    {{{ regs' retv, RET retv;
        ⌜ IsPtr_spec i regs dst src regs' retv ⌝ ∗
          pc_a ↦ₐ w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iSplitR; auto. eapply core_step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri i dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct (Hri i src) as [wsrc [H'src Hsrc]]. by set_solver+.

    assert (exec_opt (IsPtr dst src) i (r, m)
            = updatePC i
                (update_reg (r, m) i dst
                   (WInt (if is_cap wsrc then 1%Z else 0%Z)))) as HH.
    {  rewrite /= Hsrc. unfold is_cap; destruct wsrc; auto. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ (i, dst) := WInt (if is_cap wsrc then 1%Z else 0%Z) ]> regs) i)
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inversion Hstep.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    (* Success *)

    eapply (incrementPC_success_updatePC _ i m) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.

    simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ (i, dst)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ (i, PC)) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_IsPtr_successPC E i pc_p pc_b pc_e pc_a pc_a' w dst w' :
    decodeInstrW w = IsPtr dst PC →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ (i, dst) ↦ᵣ w'
    }}}
      (i, Instr Executable) @ E
      {{{ RET (i, NextIV);
          (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ (i, dst) ↦ᵣ WInt 1%Z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [|].
     { iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, dst)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, PC) (i, dst)) ; simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

   Lemma wp_IsPtr_success E i pc_p pc_b pc_e pc_a pc_a' w dst r wr w' :
     decodeInstrW w = IsPtr dst r →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →

       {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↦ₐ w
             ∗ ▷(i, r)↦ᵣ wr
             ∗ ▷ (i, dst) ↦ᵣ w'
       }}}
         (i, Instr Executable) @ E
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗(i, r)↦ᵣ wr
           ∗ (i, dst) ↦ᵣ WInt (if is_cap wr then 1%Z else 0%Z) }}}.
   Proof.
    iIntros (Hinstr Hvpc Hpc_a ϕ) "(>HPC & >Hpc_a & >Hr & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
    by rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, dst)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, r) (i, dst)) ; simplify_pair_eq.
       rewrite (insert_commute _ (i, dst) (i, PC)) ; simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

   Lemma wp_IsPtr_success_dst E i pc_p pc_b pc_e pc_a pc_a' w dst w' :
     decodeInstrW w = IsPtr dst dst →
     isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     
       {{{ ▷ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
             ∗ ▷ pc_a ↦ₐ w
             ∗ ▷ (i, dst) ↦ᵣ w'
       }}}
         (i, Instr Executable) @ E
       {{{ RET (i, NextIV);
           (i, PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ w
           ∗ (i, dst) ↦ᵣ WInt (if is_cap w' then 1%Z else 0%Z) }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iApply (wp_IsPtr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq by simplify_pair_eq; eauto.
     by rewrite !dom_insert; set_solver+.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [|].
     { iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq by simplify_pair_eq.
       rewrite (insert_commute _ (i, PC) (i, dst)) ; simplify_pair_eq.
       rewrite insert_insert (insert_commute _ (i, PC) (i, dst)) ; simplify_pair_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { incrementPC_inv; simplify_map_eq by simplify_pair_eq; eauto. congruence. }
   Qed.

End cap_lang_rules.
