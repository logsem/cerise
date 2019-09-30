From cap_machine Require Export logrel.
From cap_machine.ftlr Require Export Jmp Jnz Get Get2 AddSubLt AddSubLt2 IsPtr Lea Load Mov Store Restrict Subseg.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types r : (leibnizO Reg). 
  Implicit Types interp : D.
  Notation WORLD_S := (leibnizO ((STS_states * STS_rels) * bool)).
  Implicit Types M : WORLD_S. 

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, reg ↦ᵣ w)%I. 
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I r reg w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma get_world_destruct M :
    ∃ fs fr, M.1.1 = fs ∧ M.1.2 = fr.
  Proof.
    destruct M,p; simpl; eauto. 
  Qed.  
  
  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl).

  Lemma fundamental_RX M r b e g (a : Addr) :
    ((∃ p, ⌜PermFlows RX p⌝ ∧
    ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
     ⟦ inr ((RX,g),b,e,a) ⟧ₑ M r)%I
  with fundamental_RWX M r b e g (a : Addr) :
    ((∃ p, ⌜PermFlows RWX p⌝ ∧
    ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
     ⟦ inr ((RWX,g),b,e,a) ⟧ₑ M r)%I
  with fundamental_RWLX M r b e g (a : Addr) :
    ((∃ p, ⌜PermFlows RWLX p⌝ ∧
    ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) →
     ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ M r)%I. 
  Proof.
  { clear fundamental_RX.
    destruct (get_world_destruct M) as [fs [fr [Heqs Heqr] ] ].    
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [HM [Hsts Hown]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert (Heqs Heqr) "Hinv".    
    iLöb as "IH" forall (r a g fs fr b e M).
    iIntros (Heqs Heqr) "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iDestruct "Hinv" as (p' Hfp) "Hinv". 
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as "Hinva"; auto. 
      iMod (na_inv_open _ _ _ (logN.@a) with "Hinva Hown") as "(Ha & Hown & Hcls)"; auto. 
      rewrite /read_write_cond.
      iDestruct "Ha" as (w) "[>Ha #Hval]".
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (RX_jmp_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Jnz *)
        iApply (RX_jnz_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Mov *)
        iApply (RX_Mov_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Load *)
        iApply (RX_Load_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. 
      + (* Store *)
      (* iApply (RX_Store_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.  *)
        admit. 
      + (* Lt *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Add *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Sub *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Lea *)
        iApply (RX_Lea_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Restrict *)
        iApply (RX_Restrict_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Subseg *)
        iApply (RX_Subseg_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* IsPtr *) 
        iApply (RX_IsPtr_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* GetL *)
        iApply (RX_getL_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* GetP *)
        iApply (RX_getP_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* GetB *)
        iApply (RX_getB_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* GetE *)
        iApply (RX_getE_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* GetA *)
        iApply (RX_getA_case with "[] [] [] [] [] [HM] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Ha Hown]") as "Hown".
        { iFrame. iNext. iExists _; iFrame. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }            
        iFrame.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  }
  { clear fundamental_RWX.
    destruct (get_world_destruct M) as [fs [fr [Heqs Heqr] ] ].    
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [HM [Hsts Hown]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert (Heqs Heqr) "Hinv".    
    iLöb as "IH" forall (r a g fs fr b e M).
    iIntros (Heqs Heqr) "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RWX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iDestruct "Hinv" as (p' Hfp) "Hinv". 
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as "Hinva"; auto. 
      iMod (na_inv_open _ _ _ (logN.@a) with "Hinva Hown") as "(Ha & Hown & Hcls)"; auto. 
(* ======= *)
      rewrite /read_write_cond.
      iDestruct "Ha" as (w) "[>Ha #Hval]".
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        (* iApply (RWX_jmp_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit.  
      + (* Jnz *) admit.
      + (* Mov *) admit.
      + (* Load *) admit.
      + (* Store *) admit.
      + (* Lt *)
        (* iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit.  
      + (* Add *)
        (* iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* Sub *)
        (* iApply (RWX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.   *) admit. 
      + (* Lea *) admit. 
      + (* Restrict *) admit.
      + (* Subseg *) admit.
      + (* IsPtr *) admit. 
      + (* GetL *) 
        (* iApply (RWX_getL_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* GetP *)
        (* iApply (RWX_getP_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* GetB *)
        (* iApply (RWX_getB_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* GetE *)
        (* iApply (RWX_getE_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* GetA *)
        (* iApply (RWX_getA_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto. *) admit. 
      + (* Fail *) 
        iApply (wp_fail with "[HPC Ha]"); eauto. iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Ha Hown]") as "Hown".
        { iFrame. iNext. iExists _; iFrame. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RWX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RWX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }            
        iFrame.
    - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr. }
  { admit. }
  Admitted.

  Theorem fundamental (perm : Perm) b e g (a : Addr) stsf r :
    (⌜perm = RX ∨ perm = RWX ∨ perm = RWLX⌝) -∗
    (∃ p, ⌜PermFlows perm p⌝ ∧
          ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))) -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ stsf r.
  Proof.
    iIntros ([-> | [-> | ->] ]) "Hp". 
    - by iApply fundamental_RX.
    - by iApply fundamental_RWX.
    - by iApply fundamental_RWLX. 
  Qed. 
    
      
End fundamental. 