From cap_machine.ftlr Require Export Jmp Jnz Mov Load Store AddSubLt Restrict
  Subseg IsPtr Get Lea Cas.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.

From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.examples Require Import mkregion_helpers.

Section fundamental.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MP: MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma extract_r_ex r i (reg : RegName) :
    (∃ w, r !! (i, reg) = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, (i, reg) ↦ᵣ w)%I.
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ reg' j, reg' ↦ᵣ j)%I r (i, reg) w); eauto.
  Qed.

  Lemma extract_r reg i (r : RegName) w :
    reg !! (i, r) = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     ((i, r) ↦ᵣ w ∗ (∀ x', (i, r) ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[(i, r) := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ k j, k ↦ᵣ j)%I reg (i, r) w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ k j, k ↦ᵣ j)%I reg (i, r) w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.
  
  Lemma fundamental_cap i r p b e a :
    ⊢ interp (WCap p b e a) →
      interp_expression r i (WCap p b e a).
  Proof.
    iIntros "#Hinv /=".
    iIntros "[[Hfull Hreg] Hmreg]".
    iRevert "Hinv".
    iLöb as "IH" forall (i r p b e a).
    iIntros "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
    destruct (decide (isCorrectPC (WCap p b e a))).
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto. solve_addr. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i0. subst. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|].
      rewrite /interp_ref_inv /=. 
      iInv (logN.@a) as (w) "[>Ha HP]" "Hcls". 
      iDestruct ((big_sepM_delete _ _ (i, PC)) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (WCap p b e a)).
      destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Store *)
        iApply (store_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption.
        2,3,4,5,6: eauto. apply is_AddSubLt_Lt ; auto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption.
        2,3,4,5,6: eauto. apply is_AddSubLt_Add ; auto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption.
        2,3,4,5,6: eauto. apply is_AddSubLt_Sub ; auto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* IsPtr *)
        iApply (isptr_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetP *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetB *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetE *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetA *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.

      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iNext ; iIntros "_".
        iApply wp_value.
        iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ (i, PC)) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iIntros (_).
        iExists (<[(i, PC):=WCap p b e a]> r). iFrame.
        iAssert (∀ r0 : RegName,
                   ⌜is_Some (<[(i, PC):=WCap p b e a]> r !! (i, r0))
                   /\  (∀ j : CoreN, i ≠ j → <[(i, PC):=WCap p b e a]> r !! (j, r0) = None)⌝)%I as "HA".
        { iIntros. destruct (decide ((i, PC) = (i,r0))).
          specialize (H r0) ; destruct H.
          - simplify_eq ; rewrite lookup_insert.
            iSplit ; eauto.
            iPureIntro. intros.
            rewrite lookup_insert_ne; auto ; simplify_pair_eq.
          - rewrite lookup_insert_ne; auto ; simplify_pair_eq.
            specialize (H r0) ; destruct H.
            iSplit ; auto.
            iPureIntro; intros.
            rewrite lookup_insert_ne; auto ; simplify_pair_eq.
        }
        iFrame "HA".
      + iApply (cas_case with "[] [] [] [] [] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ (i, PC)) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (WCap p b e a)).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iNext ; iIntros "_".
     iApply wp_value.
     iIntros (Hcontr); inversion Hcontr.
  Qed.

  Theorem fundamental i w r :
    ⊢ interp w -∗ interp_expression i r w.
  Proof.
    iIntros "Hw". destruct w as [| c].
    { iClear "Hw". iIntros "(? & Hreg)". unfold interp_conf.
      iApply (wp_wand with "[-]"). 2: iIntros (?) "H"; iApply "H".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_,_)). cbn.
      unfold registers_mapsto. rewrite -insert_delete_insert.
      iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]". by rewrite lookup_delete.
      iApply (wp_notCorrectPC with "HPC"). by inversion 1.
      iNext. iIntros. cbn. iApply wp_pure_step_later; auto. iNext.
      iIntros "_".
      iApply wp_value. iIntros (?). congruence. }
    { iApply fundamental_cap. done. }
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  Definition exec_cond b e p : iProp Σ :=
    (∀ a r i, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression i r (WCap p b e a))%I.

  Lemma interp_exec_cond p b e a :
    p ≠ E -> interp (WCap p b e a) -∗ exec_cond b e p.
  Proof.
    iIntros (Hnp) "#Hw".
    iIntros (a0 i r Hin). iNext. iModIntro.
    iApply fundamental. 
    rewrite !fixpoint_interp1_eq /=. destruct p; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  
  Lemma exec_wp p b e a :
    isCorrectPC (WCap p b e a) ->
    exec_cond b e p -∗
    ∀ i r, ▷ □ (interp_expr interp r) i (WCap p b e a).
  Proof. 
    iIntros (Hvpc) "#Hexec". 
    rewrite /exec_cond.
    iIntros (i r).
    assert (a ∈ₐ[[b,e]])%I as Hin. 
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    iSpecialize ("Hexec" $! a i r Hin). iFrame "#".
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm w :
    ⊢ interp w -∗ ▷ (∀ i r, interp_expression i r (updatePcPerm w)).
  Proof.
    iIntros "#Hw".
    assert ((∃ b e a, w = WCap E b e a) ∨ updatePcPerm w = w) as [Hw | ->].
    { destruct w; eauto. unfold updatePcPerm.
      case_match; eauto. }
    { destruct Hw as [b [e [a ->] ] ]. rewrite fixpoint_interp1_eq. cbn -[all_registers_s].
      iNext. iIntros (i rmap). iSpecialize ("Hw" $! i rmap). iDestruct "Hw" as "#Hw".
      iIntros "(HPC & Hr)". iApply "Hw". iFrame. }
    { iNext. iIntros (rmap i). iApply fundamental. eauto. }
  Qed.

  Lemma jmp_to_unknown w :
    ⊢ interp w -∗
      ▷ (∀ (i: CoreN) rmap,
          ⌜dom rmap = (all_registers_s_core i) ∖ {[ (i, PC) ]}⌝ →
          (i, PC) ↦ᵣ updatePcPerm w
          ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
          -∗ WP (i, Seq (Instr Executable)) {{ λ v, ⌜v = (i, HaltedV)⌝ →
               ∃ r : Reg, full_map r i ∧ registers_mapsto r }}).
  Proof.
    iIntros "#Hw". iDestruct (interp_updatePcPerm with "Hw") as "Hw'". iNext.
    iIntros (i rmap Hrmap).
    set rmap' := <[ (i, PC) := (WInt 0%Z: Word) ]> rmap
        : gmap (CoreN*RegName) Word.
    iSpecialize ("Hw'" $! rmap').
    iIntros "(HPC & Hr)". unfold interp_expression, interp_expr, interp_conf. cbn.
    iApply "Hw'". iClear "Hw'". iFrame. rewrite /registers_mapsto.
    iDestruct (big_sepM_sep with "Hr") as "(Hr & HrV)".
    iSplitL "HrV"; [iSplit|].
    { unfold full_map. iIntros (r).
      destruct (decide ( r = PC)).
      { inversion e ; subst.
        rewrite lookup_insert. iPureIntro.
        split ; eauto.
        intros j Hneq.
        subst rmap'.
        rewrite lookup_insert_ne ; last (apply pair_neq_inv ; left ; auto).
        apply elem_of_gmap_dom_none.
        rewrite Hrmap.
        intro contra.
        apply elem_of_difference in contra.
        destruct contra as [contra _].
        rewrite /all_registers_s_core in contra.
        apply elem_of_map_1 in contra.
        destruct contra as (? & contra & ?).
        clear -Hneq contra ; simplify_eq.
        }
      rewrite lookup_insert_ne;[| clear Hrmap; simplify_pair_eq].
      iPureIntro. rewrite elem_of_gmap_dom Hrmap.
      split. clear Hrmap; set_solver.
      intros j Hneq.
      subst rmap'.
      rewrite lookup_insert_ne ; last (apply pair_neq_inv ; left ; auto).
      apply elem_of_gmap_dom_none.
      rewrite Hrmap.
      intro contra.
      apply elem_of_difference in contra.
      destruct contra as [contra _].
      rewrite /all_registers_s_core in contra.
      apply elem_of_map_1 in contra.
      destruct contra as (? & contra & ?).
      clear -Hneq contra ; simplify_eq.
    }
    { iIntros (ri v Hri Hvs).
      rewrite lookup_insert_ne in Hvs;[| clear Hrmap; simplify_pair_eq].
      iDestruct (big_sepM_lookup _ _ (i, ri) with "HrV") as "HrV"; eauto.
      by apply pair_neq_inv' ; apply not_eq_sym.
    }
    rewrite insert_insert. iApply big_sepM_insert.
    { apply elem_of_gmap_dom_none. rewrite Hrmap ; clear Hrmap.
      set_solver. }
    iFrame.
  Qed.

  Lemma region_integers_alloc' E (b e a: Addr) l p :
    Forall (λ w, is_cap w = false) l →
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hl) "H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_integers_alloc _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r i).
         iDestruct (fundamental r _ i with "H") as "H'". eauto. }
    all: iApply region_integers_alloc; eauto.
  Qed.

  (* similar than the others, but without the later *)
  Lemma interp_updatePcPerm_adv p b e a :
    p = RX \/ p = RWX ->
    ⊢ interp (WCap p b e a) -∗ (∀ i r, interp_expression i r (updatePcPerm (WCap p b e a))).
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (rmap i). destruct Hp as [ -> | -> ] ; iApply fundamental ; eauto.
  Qed.


  Lemma jmp_to_unknown_adv p b e a :
    p = RX \/ p = RWX ->
    ⊢ interp (WCap p b e a) -∗
      ∀ (i: CoreN) rmap,
          ⌜dom rmap = (all_registers_s_core i) ∖ {[ (i, PC) ]}⌝ →
          (i, PC) ↦ᵣ updatePcPerm (WCap p b e a)
          ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
          -∗ WP (i, Seq (Instr Executable)) {{ λ v, ⌜v = (i, HaltedV)⌝ →
               ∃ r : Reg, full_map r i ∧ registers_mapsto r }}.
  Proof.
    iIntros (Hp) "#Hw". iDestruct (interp_updatePcPerm_adv with "Hw") as "Hw'"
    ; eauto.
    iIntros (i rmap Hrmap).
    set rmap' := <[ (i, PC) := (WInt 0%Z: Word) ]> rmap
        : gmap (CoreN*RegName) Word.
    iSpecialize ("Hw'" $! rmap').
    iIntros "(HPC & Hr)". unfold interp_expression, interp_expr, interp_conf. cbn.
    iApply "Hw'". iClear "Hw'". iFrame. rewrite /registers_mapsto.
    iDestruct (big_sepM_sep with "Hr") as "(Hr & HrV)".
    iSplitL "HrV"; [iSplit|].
    { unfold full_map. iIntros (r).
      destruct (decide (r = PC)).
      { subst r. rewrite lookup_insert. iPureIntro. split ; eauto.
        intros j Hneq.
        subst rmap'.
        rewrite lookup_insert_ne ; last (apply pair_neq_inv ; left ; auto).
        apply elem_of_gmap_dom_none.
        rewrite Hrmap.
        intro contra.
        apply elem_of_difference in contra.
        destruct contra as [contra _].
        rewrite /all_registers_s_core in contra.
        apply elem_of_map_1 in contra.
        destruct contra as (? & contra & ?).
        clear -Hneq contra ; simplify_eq.
      }
      rewrite lookup_insert_ne;[| clear Hrmap; simplify_pair_eq].
      iPureIntro. rewrite elem_of_gmap_dom Hrmap.
      split ;[ clear Hrmap; set_solver | ].
      intros j Hneq.
      subst rmap'.
      rewrite lookup_insert_ne ; last (apply pair_neq_inv ; left ; auto).
      apply elem_of_gmap_dom_none.
      rewrite Hrmap.
      intro contra.
      apply elem_of_difference in contra.
      destruct contra as [contra _].
      rewrite /all_registers_s_core in contra.
      apply elem_of_map_1 in contra.
      destruct contra as (? & contra & ?).
      clear -Hneq contra ; simplify_eq.
    }
    { iIntros (ri v Hri Hvs).
      rewrite lookup_insert_ne in Hvs;[| clear Hrmap; simplify_pair_eq].
      iDestruct (big_sepM_lookup _ _ (i, ri) with "HrV") as "HrV"; eauto.
      by apply pair_neq_inv' ; apply not_eq_sym.
    }
    rewrite insert_insert. iApply big_sepM_insert.
    { apply elem_of_gmap_dom_none. rewrite Hrmap ; clear Hrmap.
      set_solver. }
    iFrame.
  Qed.

End fundamental.
