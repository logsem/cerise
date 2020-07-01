From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine.rules Require Import rules_LoadU. 

Section cap_lang_rules.
  Context `{memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
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

  Lemma isU_nonO p p' :
    PermFlows p p' → isU p = true → p' ≠ O.
  Proof.
    intros Hfl' Hra. destruct p'; auto. destruct p; inversion Hfl'. inversion Hra.
  Qed.

  (* TODO: replace all the 1's by general z's in this file *)
  
  Lemma wb_implies_verify_access p g:
    ∀ b e a a',
      (a' + 1)%a = Some a ->
      withinBounds ((p, g), b, e, a') = true ->
      (if Addr_le_dec b a'
       then if Addr_lt_dec a' a then if Addr_le_dec a e then Some a' else None else None
       else None) = Some a'.
  Proof.
    intros b e a a' Hincr Hwb.
    apply withinBounds_le_addr in Hwb as [Hle Hlt].
    destruct (Addr_le_dec b a');[|contradiction].
    destruct (Addr_lt_dec a' a);[|solve_addr].
    destruct (Addr_le_dec a e);[|solve_addr].
    auto.
  Qed.

  (* load from the top *)
  Lemma wp_loadU_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a a' pc_a'
        pc_p' p' :
    decodeInstrW w = LoadU r1 r2 (inl (-1)%Z) →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    isU p = true -> withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    (a + 1)%a = Some a' ->

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ w''  
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a')
          ∗ ▷ a ↦ₐ[p'] w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a')
             ∗ a ↦ₐ[p'] w' }}}. 
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc HU Hwb Hpca' Hincr φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'.
    pose proof (isU_nonO _ _ Hfl' HU) as Hp'. 
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%) ]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %]"; auto.
    iApply (wp_loadU with "[$Hmap $Hmem]");[|apply Hpc_p'|apply Hvpc|..];simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. simplify_map_eq.
      assert ((a' + -1)%a = Some a) as ->;[solve_addr|]. 
      erewrite wb_implies_verify_access;eauto. 
        by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       simplify_map_eq.
       assert ((a0 + -1)%a = Some a) as Heq;[solve_addr|]. rewrite Heq in H9.
       erewrite  wb_implies_verify_access in H9;eauto. simplify_eq. 
       simplify_map_eq. 
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       assert ((a0 + -1)%a = Some a) as Heq;[solve_addr|]. rewrite Heq in e4.
       erewrite  wb_implies_verify_access in e4;eauto. simplify_eq.
       Unshelve. all:auto. 
     }
  Qed.  

  (* load into PC from reg *)
  Lemma wp_loadU_success_reg_to_PC E r1 r2 pc_p pc_g pc_b pc_e pc_a w p g b e a a1 p' g' b' e' a' a'' pc_p' p'':
    decodeInstrW w = LoadU PC r1 (inr r2)  →
    PermFlows pc_p pc_p' →
    PermFlows p p'' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    isU p = true -> withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = Some a'' →
    (a + 1)%a = Some a1 ->

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ[pc_p'] w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a1)
          ∗ ▷ r2 ↦ᵣ inl (-1)%Z
          ∗ ▷ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p',g'),b',e',a'')
             ∗ pc_a ↦ₐ[pc_p'] w
             ∗ r1 ↦ᵣ inr ((p,g),b,e,a1)
             ∗ r2 ↦ᵣ inl (-1)%Z
             ∗ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}}.
  Proof.
    iIntros (Hinstr Hfl Hfl' Hvpc HU Hwb Hpca' Hincr φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'.
    pose proof (isU_nonO _ _ Hfl' HU) as Hp'.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%) ]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %]"; auto.
    iApply (wp_loadU with "[$Hmap $Hmem]");[apply Hinstr |apply Hpc_p'|apply Hvpc|..];simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. simplify_map_eq.
      assert ((a1 + -1)%a = Some a) as ->;[solve_addr|].
      erewrite wb_implies_verify_access;eauto.
        by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       simplify_map_eq.
       assert ((a0 + -1)%a = Some a) as Heq;[solve_addr|]. rewrite Heq in H9.
       erewrite  wb_implies_verify_access in H9;eauto. simplify_eq.
       simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; first congruence.
       all: assert ((a0 + -1)%a = Some a) as Heq;[solve_addr|]; rewrite Heq in e4;
       erewrite  wb_implies_verify_access in e4;eauto.
       * by exfalso.
       * simplify_map_eq. eapply (incrementPC_None_inv _ _ _ _ a') in e6; last by simplify_map_eq. congruence.
       Unshelve. all:auto.
     }
  Qed.


End cap_lang_rules. 
