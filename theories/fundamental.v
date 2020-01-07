From cap_machine.ftlr Require Export Jmp Jnz Get AddSubLt IsPtr Lea Load Mov Store Restrict Subseg.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
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
    ((⌜p = RX⌝ ∨ ⌜p = RWX⌝ ∨ ⌜p = RWLX /\ g = Local⌝) →
    (∃ p', ⌜PermFlows p p'⌝ ∧
           ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p' interp)
                                             ∧ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
                                             ∧ ⌜region_std W a⌝)) →
     interp_expression r W (inr ((p,g),b,e,a)))%I.
  Proof.
    iIntros (Hp) "#Hinv /=".
    iIntros "[[Hfull Hreg] [Hmreg [Hr [Hsts Hown]]]]".
    iSplit; eauto; simpl.
    iRevert (Hp) "Hinv".
    iLöb as "IH" forall (W r p g b e a).
    iIntros (Hp) "#Hinv". 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((p,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iDestruct "Hinv" as (p' Hfp) "Hinv". 
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as "(Hinva & Hstate_a & Hrel_a)"; auto.
      iDestruct "Hstate_a" as %Hstate_a; iDestruct "Hrel_a" as %Hrel_a.
      assert (∃ (ρ : region_type), (std_sta W) !! (countable.encode a) = Some (countable.encode ρ) ∧ ρ ≠ Revoked) as [ρ [Hρ Hne] ].
      { destruct (pwl p),g; eauto. destruct Hstate_a as [Htemp | Hperm];eauto. }      
      iDestruct (region_open W a p' with "[$Hinva $Hr $Hsts]") 
                                    as (w) "(Hr & Hsts & Hstate & Ha & % & Hmono & #Hw) /="; eauto. 
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Load *)
      (* iApply (load_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto. *)
        admit.
      + (* Store *)
      (* iApply (store_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto. *)
        admit.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Restrict *)
      (* iApply (restrict_case with "[] [] [] [] [] [] [Hsts] [Hown] [Hr] [Ha] [HPC]"); eauto.*)
        admit.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* IsPtr *) 
        iApply (isptr_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* GetL *)
        iApply (getL_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* GetP *)
        iApply (getP_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* GetB *)
        iApply (getB_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* GetE *)
        iApply (getE_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* GetA *)
        iApply (getA_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iDestruct (region_close _ _ _ _ _ ρ with "[$Hr $Ha $Hstate $Hmono]") as "Hr";[auto|iFrame "#"; auto|].
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (p, g, b, e, a)]> r),W. iFrame.
        iAssert (⌜related_sts_priv_world W W⌝)%I as "#Hrefl". 
        { iPureIntro. split; apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (p, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }            
        iFrame.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (p, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  Admitted.

End fundamental. 