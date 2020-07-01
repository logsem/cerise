From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine.rules Require Import rules_StoreU. 

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

  Lemma wb_implies_verify_access p g:
    ∀ b e a,
      withinBounds ((p, g), b, e, a) = true ->
      match (a + 0)%a with
        | Some a' =>
            if Addr_le_dec b a'
            then if Addr_le_dec a' a then if Addr_lt_dec a e then Some a' else None else None
            else None
        | None => None
        end = Some a. 
  Proof.
    intros b e a Hwb. 
    rewrite /= addr_add_0 /=. 
    apply withinBounds_le_addr in Hwb as [Hle Hlt].
    destruct (Addr_le_dec b a);[|contradiction].
    destruct (Addr_le_dec a a);[|solve_addr].
    destruct (Addr_lt_dec a e);[|contradiction].
    auto. 
  Qed.
  
  (* store and increment *)
  Lemma wp_storeU_success_0_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a a' w'' pc_p' p' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr src) →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p w'' = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ[p'] w'' }}}.
    Proof.
      iIntros (Hinstr Hfl Hfl' Hvpc Hpca' HU HstoreU Hwb Ha' φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    pose proof (isU_nonO _ _ Hfl' HU) as Hp''.
    pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'.
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU HstoreU. erewrite wb_implies_verify_access; eauto. 
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       simplify_map_eq.
       erewrite wb_implies_verify_access in H11; eauto. simplify_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction]. 
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite (insert_commute _ _ src) // insert_insert. 
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e6; eauto. simplify_eq. 
       Unshelve. all:auto. 
     }
    Qed.

  (* store and increment from and to the same register *)
  Lemma wp_storeU_success_0_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a a' pc_p' p' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr dst) →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p (inr (p, g, b, e, a)) = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->


     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ[p'] inr ((p,g),b,e,a)}}}.
    Proof.
      iIntros (Hinstr Hfl Hfl' Hvpc Hpca' HU HstoreU Hwb Ha' φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    pose proof (isU_nonO _ _ Hfl' HU) as Hp''.
    pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'.
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold canStoreU. rewrite HU HstoreU. erewrite wb_implies_verify_access; eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       simplify_map_eq.
       erewrite wb_implies_verify_access in H9; eauto. simplify_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e6; eauto. simplify_eq.
       Unshelve. all:auto.
     }
    Qed.

    Lemma wp_storeU_success_0_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a a' pc_p' p' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inl z) →
    PermFlows pc_p pc_p' →
    PermFlows p p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> 
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ[p'] w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ[p'] (inl z) }}}.
    Proof.
      iIntros (Hinstr Hfl Hfl' Hvpc Hpca' HU Hwb Ha' φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    pose proof (isU_nonO _ _ Hfl' HU) as Hp''.
    pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'.
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. erewrite wb_implies_verify_access; eauto. 
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       simplify_map_eq.
       erewrite wb_implies_verify_access in H9; eauto. simplify_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction]. 
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert. rewrite insert_insert. 
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e6; eauto. simplify_eq. 
       Unshelve. all:auto. 
     }
    Qed.


End cap_lang_rules. 
