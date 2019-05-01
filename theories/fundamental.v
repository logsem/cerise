From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.

Section fundamental.
  Context `{memG Σ, regG Σ, inG Σ frac.fracR}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

(* "Hmtr" : [∗ map] r0↦w ∈ <[PC:=inr (RX, g, b, e, a)]> r, r0 ↦ᵣ w
  "Hmta" : [∗ map] a0↦w ∈ m, a0 ↦ₐ w *)

  (* Lemma extract_a m (a : Addr) : *)
  (*   [∗ map] a0↦w ∈ m, a0 ↦ₐ w -∗  *)

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
  
  Theorem fundamental (perm : Perm) b e g γ (a : Addr) :
    (perm = RX ∧ read_cond b e g γ interp) ∨
    (perm = RWX ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, ⌜isLocalWord w = false⌝%I)) ∨
    (perm = RWLX ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, True%I)) →
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ.
  Proof.
    intros [[-> Hrc] | [(Hrwx & Hrc & Hwc) | (Hwlx & Hrc & Hwc)]].
    - iIntros (r). iAlways. iIntros (m) "Hreg Hmreg /=".
      iLöb as "IH" forall (a).
      destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
      + (* Correct PC *)
        iDestruct (extract_r (<[PC:=inr (RX, g, b, e, a)]> r) PC (inr (RX, g, b, e, a))
                     with "[Hmtr]") as "[HPC HPCmap]";
          first by apply (lookup_insert r PC). iFrame.
        
        iAssert (∃ w, a ↦ₐ w)%I as (w) "Ha".  { admit. } (* this should come from the read/write conditions *)
        destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
        * admit. (* Jmp *)
        * admit. (* Jnz *)
        * admit. (* Mov *)
        * (* Load *)
          iAssert (∃ w, dst ↦ᵣ w)%I as (wdst) "Hdst". (* these come from the reg interp relation *)
          { admit. }
          iAssert (∃ w, src ↦ᵣ w)%I as (wsrc) "Hsrc".
          { admit. }
          destruct wsrc eqn:Hsrc.
          { admit. }
          destruct c. do 3 destruct p.
          iAssert (∃ w, a0 ↦ₐ w)%I as (wa0) "Ha0".
          { admit. }
          iApply (wp_load_success dst src _ _ _ _ a); eauto.
          Focus 3. iFrame.
          iNext. iIntros "[HPC Hdst]".
          iSpecialize ("HPCmap" with "HPC"). rewrite insert_insert. 
          iApply ("IH" with "[Hreg] [HPCmap] [Hmta]"); eauto.  
          
  Abort. 
          
End fundamental. 