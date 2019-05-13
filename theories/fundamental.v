From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.

Section fundamental.
  Context `{memG Σ, regG Σ, inG Σ frac.fracR}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.


  Lemma extract_r_ex reg (r : RegName) :
    (∃ w, reg !! r = Some w) →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) → ∃ w, r ↦ᵣ w)%I. 
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ r i, r ↦ᵣ i)%I reg r w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma key_non_dupl γ : ∀ q, own γ 1%Qp ∗ own γ q%Qp -∗ False.
  Proof.
    iIntros (q) "[H1 Hq]".
    iDestruct (own_valid_2 γ with "[H1] [Hq]") as "%"; iFrame.
    iPureIntro. rewrite frac.frac_op' in H2.
    assert (((1 + q)%Qp ≤ 1%Qp)%Qc).
      by apply frac.frac_valid'.
    by apply (Qp_not_plus_q_ge_1 q). 
  Qed.


  Lemma fundamental_RX_global b e γ (a : Addr) :
    (read_cond b e Global γ interp -∗
    ⟦ inr ((RX,Global),b,e,a) ⟧ₑ )%I. 
  Proof.
    iIntros "#Hinv".
    iIntros (r m) "Hreg".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iIntros "Hmreg /=".
    iLöb as "IH". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,Global),b,e,a)))). 
    - (* Correct PC *)
      iInv (logN.@(b, e)) as (ws) "HregionHvalid" "Hcls".
      destruct (incr_addr_neg a (-1) ltac:(omega)) as [a1 X].
      iDestruct (extract_from_region _ _ a with "HregionHvalid")
        as (w) "(Hregionl & Hvalidl & >Ha & Hva & Hregionh & Hvalidh)".
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      { exact X. }
      { admit. } (* a + -1 and a + 1 are some addresses *)
      iDestruct (extract_r (<[PC:=inr (RX, Global, b, e, a)]> r) PC
                           (inr (RX, Global, b, e, a))
                   with "[Hmreg]") as "[HPC HPCmap]";
        first by apply (lookup_insert r PC). iFrame.
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + admit. (* Jmp *)
      + admit. (* Jnz *)
      + admit. (* Mov *)
      + (* Load *)
        (* these come from the reg interp relation *)
        iAssert (∃ w, dst ↦ᵣ w)%I as (wdst) "Hdst"; [admit|].
        iAssert (∃ w, src ↦ᵣ w)%I as (wsrc) "Hsrc"; [admit|].
        destruct wsrc eqn:Hsrc; [admit|].
        destruct c. do 3 destruct p.
        iAssert (∃ w, a0 ↦ₐ w)%I as (wa0) "Ha0"; [admit|].
        
        iApply (wp_load_success with "[HPC Hdst Hsrc Ha Ha0]"); eauto.
        * admit.
        * admit.
        * admit.
        * iFrame.
        * iNext. iIntros "(HPC & Hdst & Ha) /=".
          iApply (wp_wand with "[HPC Hreg HPCmap]").
          { iApply wp_pure_step_later; eauto. iNext.
            iApply ("IH" with "Hreg").
            iSpecialize ("HPCmap" with "HPC"). rewrite insert_insert. iFrame. 
          } iAssert (∀ v : val cap_lang,
                        (λ _ : valC cap_lang, ∃ r0 : Reg, registers_mapsto r0) v
                                -∗ ∃ r0 : Reg, registers_mapsto r0)%I as "Htrivial".
          { iIntros (_) "Hreg". iFrame. } iFrame. 
          iApply "Hcls". iNext.
          iExists (drop (region_size b a) ws). iFrame.
      + admit. (* Store *)
      + admit. (* Lt *)
      + admit. (* Add *)
      + admit. (* Sub *)
      + admit. (* Lea *)
      + admit. (* Restrict *)
      + admit. (* Subseg *)
      + admit. (* IsPtr *)
      + admit. (* GetL *)
      + admit. (* GetP *)
      + admit. (* GetB *)
      + admit. (* GetE *)
      + admit. (* GetA *)
      + admit. (* Fail *)
      + admit. (* Halt *)   
    - (* Incorrect PC *) admit.
  Admitted. 

  Lemma fundamental_RX_local b e γ (a : Addr) :
    (read_cond b e Local γ interp -∗
    ⟦ inr ((RX,Local),b,e,a) ⟧ₑ )%I. 
  Proof.
    iIntros "#Hinv".
    iIntros (r m) "Hreg".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iExists γ. iIntros "Hkey Hmreg /=".
    iLöb as "IH". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,Local),b,e,a)))). 
    - (* Correct PC *)
      iInv (logN.@(b, e)) as "[HregionHvalid | >Hkey']" "Hcls";
        last by iDestruct (key_non_dupl γ with "[Hkey Hkey']") as "Hf"; iFrame.
      iDestruct "HregionHvalid" as (ws) "HregionHvalid". 
      iDestruct (extract_from_region _ _ a with "HregionHvalid")
        as (w) "(Hregionl & Hvalidl & >Ha & Hva & Hregionh & Hvalidh)".
      { admit. }
      { admit. }
      { admit. } (* a + -1 and a + 1 are some addresses *)
      iDestruct (extract_r (<[PC:=inr (RX, Local, b, e, a)]> r) PC
                           (inr (RX, Local, b, e, a))
                   with "[Hmreg]") as "[HPC HPCmap]";
        first by apply (lookup_insert r PC). iFrame.
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + admit. (* Jmp *)
      + admit. (* Jnz *)
      + admit. (* Mov *)
      + (* Load *)
        (* these come from the reg interp relation *)
        iAssert (∃ w, dst ↦ᵣ w)%I as (wdst) "Hdst"; [admit|].
        iAssert (∃ w, src ↦ᵣ w)%I as (wsrc) "Hsrc"; [admit|].
        destruct wsrc eqn:Hsrc; [admit|].
        destruct c. do 3 destruct p.
        iAssert (∃ w, a0 ↦ₐ w)%I as (wa0) "Ha0"; [admit|].
        
        iApply (wp_load_success with "[HPC Hdst Hsrc Ha Ha0]"); eauto.
        * admit.
        * admit.
        * admit.
        * iFrame.
        * iNext. iIntros "(HPC & Hdst & Ha) /=".
          iApply (wp_wand with "[HPC Hreg HPCmap Hkey]").
          { iApply wp_pure_step_later; eauto. iNext.
            iApply ("IH" with "Hreg Hkey").
            iSpecialize ("HPCmap" with "HPC"). rewrite insert_insert. iFrame. 
          } iAssert (∀ v : val cap_lang,
                        (λ _ : valC cap_lang, ∃ r0 : Reg, registers_mapsto r0) v
                         -∗ ∃ r0 : Reg, registers_mapsto r0)%I as "Htrivial".
          { iIntros (_) "Hreg". iFrame. } iFrame. 
          iApply "Hcls". iNext. iLeft.
          iExists (drop (region_size b a) ws). iFrame.
      + admit. (* Store *)
      + admit. (* Lt *)
      + admit. (* Add *)
      + admit. (* Sub *)
      + admit. (* Lea *)
      + admit. (* Restrict *)
      + admit. (* Subseg *)
      + admit. (* IsPtr *)
      + admit. (* GetL *)
      + admit. (* GetP *)
      + admit. (* GetB *)
      + admit. (* GetE *)
      + admit. (* GetA *)
      + admit. (* Fail *)
      + admit. (* Halt *)   
    - (* Incorrect PC *) admit.
  Admitted. 
  
  Theorem fundamental (perm : Perm) b e g γ (a : Addr) :
    (⌜perm = RX⌝ ∧ read_cond b e g γ interp)%I ∨
    (⌜perm = RWX⌝ ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, ⌜isLocalWord w = false⌝))%I ∨
    (⌜perm = RWLX⌝ ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, True%I))%I -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ.
  Proof. 
    iIntros "[#[-> Hinv] | [#(Hrwx & Hrc & Hwc) | #(Hwlx & Hrc & Hwc)]]".
    - destruct g.
      + (* Global *)
          by iApply fundamental_RX_global. 
      + (* Local *)
          by iApply fundamental_RX_local. 
    - (* read and write condition, non local *) admit. 
    - (* read and write condition, permit local *) admit. 
Admitted. 
          
      
End fundamental. 