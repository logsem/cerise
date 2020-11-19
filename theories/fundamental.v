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
  
  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl eq_refl).

  (*TODO: change to region_conditions *)
  Theorem fundamental r p b e (a : Addr) :
    ⊢ (interp (inr (p,b,e,a)) →
     interp_expression r (inr (p,b,e,a)))%I.
  Proof.
    iIntros "#Hinv /=".
    iIntros "[[Hfull Hreg] [Hmreg Hown]]".
    iSplit; eauto; simpl.
    iRevert "Hinv".
    iLöb as "IH" forall (r p b e a).
    iIntros "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr (p,b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      assert (p = RX ∨ p = RWX) as Hp.
      { inversion i. subst. auto. }
      iDestruct (read_allowed_inv_regs with "[] Hinv") as (P) "(#Hinva & #Hread)";[eauto|destruct Hp as [-> | ->];auto|iFrame "% #"|].
      rewrite /interp_ref_inv /=. 
      iInv (logN.@a) as (w) "[>Ha HP]" "Hcls". 
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (p, b, e, a))).
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
        iExists (<[PC:=inr (p, b, e, a)]> r). iFrame.
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (p, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iFrame "HA".
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (p, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  Definition exec_cond b e p : iProp Σ :=
    (∀ a r, ⌜a ∈ₐ [[ b , e ]]⌝ → ▷ □ interp_expression r (inr (p,b, e,a)))%I.

  Lemma interp_exec_cond p b e a :
    p ≠ E -> interp (inr (p,b,e,a)) -∗ exec_cond b e p.
  Proof.
    iIntros (Hnp) "#Hw".
    iIntros (a0 r Hin). iNext. iModIntro. 
    iApply fundamental. 
    rewrite !fixpoint_interp1_eq /=. destruct p; done. 
  Qed.
  
  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  
  Lemma exec_wp p b e a :
    isCorrectPC (inr (p, b, e, a)) ->
    exec_cond b e p -∗
    ∀ r, ▷ □ (interp_expr interp r) (inr (p, b, e, a)).
  Proof. 
    iIntros (Hvpc) "#Hexec". 
    rewrite /exec_cond /enter_cond. 
    iIntros (r). 
    assert (a ∈ₐ[[b,e]])%I as Hin. 
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    iSpecialize ("Hexec" $! a r Hin). iFrame "#". 
  Qed.
  
  Lemma jmp_or_fail_spec w φ :
  ⊢ (interp w
    -∗ (if decide (isCorrectPC (updatePcPerm w)) then
          (∃ p b e a, ⌜w = inr (p,b,e,a)⌝
          ∗ ∀ r, ▷ □ (interp_expr interp r) (updatePcPerm w))
        else
          φ FailedV ∗ PC ↦ᵣ updatePcPerm w -∗ WP Seq (Instr Executable) {{ φ }} ))%I.
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))). 
    - inversion i.
      destruct w;inversion H. destruct c,p0,p0; inversion H.
      destruct H1 as [-> | ->]. 
      + destruct p0; simpl in H; simplify_eq.
        * iExists _,_,_,_; iSplit;[eauto|].
          iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|]. 
          iApply exec_wp;auto.
        * iExists _,_,_,_; iSplit;[eauto|]. 
          rewrite /= fixpoint_interp1_eq /=.
          iExact "Hw". 
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_; iSplit;[eauto|]. 
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|]. 
        iApply exec_wp;auto.
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_".
      iApply wp_pure_step_later;auto;iNext.
      iApply wp_value. iFrame.
  Qed.
  
End fundamental.
