From cap_machine.ftlr Require Export Jmp Jnz Mov Load Store AddSubLt Restrict Subseg IsPtr Get Lea. 
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, reg ↦ᵣ w)%I.
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I r reg w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.
  
  Lemma fundamental_cap r p b e a :
    ⊢ interp (WCap p b e a) →
      interp_expression r (WCap p b e a).
  Proof.
    iIntros "#Hinv /=".
    iIntros "[[Hfull Hreg] [Hmreg Hown]]".
    iRevert "Hinv".
    iLöb as "IH" forall (r p b e a).
    iIntros "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (WCap p b e a))).
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto. solve_addr. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i. subst. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|].
      rewrite /interp_ref_inv /=. 
      iInv (logN.@a) as (w) "[>Ha HP]" "Hcls". 
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (WCap p b e a)).
      destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto. 
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Store *)
        iApply (store_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* IsPtr *)
        iApply (isptr_case with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetP *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetB *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetE *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* GetA *)
        iApply (get_case _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [] [Hown] [Ha] [HP] [Hcls] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[HP Ha]");[iExists w;iFrame|iModIntro].
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=WCap p b e a]> r). iFrame.
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=WCap p b e a]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iFrame "HA".
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (WCap p b e a)).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  Qed.

  Theorem fundamental w r :
    ⊢ interp w -∗ interp_expression r w.
  Proof.
    iIntros "Hw". destruct w as [| c].
    { iClear "Hw". iIntros "(? & Hreg & ?)". unfold interp_conf.
      iApply (wp_wand with "[-]"). 2: iIntros (?) "H"; iApply "H".
      iApply (wp_bind (fill [SeqCtx])). cbn.
      unfold registers_mapsto. rewrite -insert_delete.
      iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]". by rewrite lookup_delete.
      iApply (wp_notCorrectPC with "HPC"). by inversion 1.
      iNext. iIntros. cbn. iApply wp_pure_step_later; auto. iNext.
      iApply wp_value. iIntros (?). congruence. }
    { iApply fundamental_cap. done. }
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  Definition exec_cond b e p : iProp Σ :=
    (∀ a r, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression r (WCap p b e a))%I.

  Lemma interp_exec_cond p b e a :
    p ≠ E -> interp (WCap p b e a) -∗ exec_cond b e p.
  Proof.
    iIntros (Hnp) "#Hw".
    iIntros (a0 r Hin). iNext. iModIntro. 
    iApply fundamental. 
    rewrite !fixpoint_interp1_eq /=. destruct p; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  
  Lemma exec_wp p b e a :
    isCorrectPC (WCap p b e a) ->
    exec_cond b e p -∗
    ∀ r, ▷ □ (interp_expr interp r) (WCap p b e a).
  Proof. 
    iIntros (Hvpc) "#Hexec". 
    rewrite /exec_cond.
    iIntros (r). 
    assert (a ∈ₐ[[b,e]])%I as Hin. 
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    iSpecialize ("Hexec" $! a r Hin). iFrame "#". 
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm w :
    ⊢ interp w -∗ ▷ (∀ r, interp_expression r (updatePcPerm w)).
  Proof.
    iIntros "#Hw".
    assert ((∃ b e a, w = WCap E b e a) ∨ updatePcPerm w = w) as [Hw | ->].
    { destruct w; eauto. unfold updatePcPerm.
      case_match; eauto. }
    { destruct Hw as [b [e [a ->] ] ]. rewrite fixpoint_interp1_eq. cbn -[all_registers_s].
      iNext. iIntros (rmap). iSpecialize ("Hw" $! rmap). iDestruct "Hw" as "#Hw".
      iIntros "(HPC & Hr & ?)". iApply "Hw". iFrame. }
    { iNext. iIntros (rmap). iApply fundamental. eauto. }
  Qed.

  Lemma jmp_to_unknown w :
    ⊢ interp w -∗
      ▷ (∀ rmap,
          ⌜dom (gset RegName) rmap = all_registers_s ∖ {[ PC ]}⌝ →
          PC ↦ᵣ updatePcPerm w
          ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ λ v, ⌜v = HaltedV⌝ →
               ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }}).
  Proof.
    iIntros "#Hw". iDestruct (interp_updatePcPerm with "Hw") as "Hw'". iNext.
    iIntros (rmap Hrmap).
    set rmap' := <[ PC := (WInt 0%Z: Word) ]> rmap : gmap RegName Word.
    iSpecialize ("Hw'" $! rmap').
    iIntros "(HPC & Hr & Hna)". unfold interp_expression, interp_expr, interp_conf. cbn.
    iApply "Hw'". iClear "Hw'". iFrame. rewrite /registers_mapsto.
    iDestruct (big_sepM_sep with "Hr") as "(Hr & HrV)".
    iSplitL "HrV"; [iSplit|].
    { unfold full_map. iIntros (r).
      destruct (decide (r = PC)). { subst r. rewrite lookup_insert //. eauto. }
      rewrite lookup_insert_ne //. iPureIntro. rewrite elem_of_gmap_dom Hrmap. set_solver. }
    { iIntros (ri v Hri Hvs).
      rewrite lookup_insert_ne // in Hvs.
      iDestruct (big_sepM_lookup _ _ ri with "HrV") as "HrV"; eauto. }
    rewrite insert_insert. iApply big_sepM_insert.
    { apply elem_of_gmap_dom_none. rewrite Hrmap. set_solver. }
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
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    all: iApply region_integers_alloc; eauto.
  Qed.

  Lemma region_valid_alloc' E (b e a: Addr) l p :
    ([∗ list] w ∈ l, interp w) -∗
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros "#Hl H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_alloc _ _ _ a _ RX with "Hl H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    all: iApply (region_valid_alloc with "Hl"); eauto.
  Qed.

  Lemma region_in_region_alloc' E (b e a: Addr) l p :
    Forall (λ a0 : Addr, ↑logN.@a0 ⊆ E) (finz.seq_between b e) ->
    Forall (λ w, is_cap w = false \/ in_region w b e) l →
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hmasks Hl) "H". destruct p.
    { (* O *) rewrite fixpoint_interp1_eq //=. }
    4: { (* E *) rewrite fixpoint_interp1_eq /=.
         iDestruct (region_valid_in_region _ _ _ a _ RX with "H") as ">#H"; auto.
         iModIntro. iIntros (r).
         iDestruct (fundamental _ r with "H") as "H'". eauto. }
    all: iApply (region_valid_in_region with "H"); eauto.
  Qed.

End fundamental.
