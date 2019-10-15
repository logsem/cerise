From cap_machine Require Export logrel.
From stdpp Require Import base.
From cap_machine.ftlr Require Export Jmp Jnz Get AddSubLt IsPtr Lea Load Mov Store Restrict Subseg.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

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
  
  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl).

  Theorem fundamental W r p g b e (a : Addr) :
    ((⌜p = RX⌝ ∨ ⌜p = RWX⌝ ∨ ⌜p = RWLX⌝) →
    (∃ p', ⌜PermFlows p p'⌝ ∧
    ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p' interp))) →
     interp_expression r W (inr ((p,g),b,e,a)))%I.  
  Proof.
    destruct W as [fs fr]. 
    iIntros (Hp) "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hr [Hsts Hown]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert (Hp) "Hinv".    
    iLöb as "IH" forall (fs fr r p g b e a).
    iIntros (Hp) "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((p,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iDestruct "Hinv" as (p' Hfp) "Hinv". 
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as "Hinva"; auto.
      iDestruct (region_open (fs,fr) a p' with "[$Hinva $Hr]") 
                                    as (w) "(Hr & Ha & % & #Hmono & #Hval) /=". 
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto. 
      + (* Store *)
      (* iApply (RX_Store_case with "[] [] [] [] [] [] [Hsts] [Ha] [Hown] [Hcls] [HPC] [Hmap]"); eauto.  *)
        admit. 
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.
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
  Admitted.
    
      
End fundamental. 