From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.

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
    (⌜perm = RX⌝ ∧ read_cond b e g γ interp)%I ∨
    (⌜perm = RWX⌝ ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, ⌜isLocalWord w = false⌝))%I ∨
    (⌜perm = RWLX⌝ ∧ read_cond b e g γ interp ∧
     write_cond b e g γ interp (λne w, True%I))%I -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ.
  Proof. 
    iIntros "[#[-> Hrc] | [#(Hrwx & Hrc & Hwc) | #(Hwlx & Hrc & Hwc)]]".
    - destruct g.
      + iIntros (r m) "Hreg". iIntros (p) "Hmreg /=".
        iLöb as "IH" forall (p).
                            (* iInduction p as [| p ] "IHp". *)
                            destruct p. {
          destruct c. { admit. }
                      { iApply wp_value. auto. }
                      { iApply wp_value. auto.  }
                      { iApply wp_value.  auto. }
        }
        { iApply (wp_bind (fill [SeqCtx _])). 
          
          iApply "IH". 
        }
        destruct (decide (isCorrectPC (inr ((RX,Global),b,e,a)))). 
        { (* Correct PC *)
          (* iDestruct (extract_r (<[PC:=inr (RX, Global, b, e, a)]> r) PC *)
          (*                      (inr (RX, Global, b, e, a)) *)
          (*              with "[Hmreg]") as "[HPC HPCmap]"; *)
          (*   first by apply (lookup_insert r PC). iFrame. *)
          iDestruct "Hrc" as (b' e') "#[Hin Hinv]".
          (* iApply fupd_wp. *)
          iApply (wp_bind (fill [SeqCtx _])). 
          iInv (logN.@(b', e')) as (ws) "HregionHvalid" "Hcls".
          iDestruct (extract_from_region _ _ a with "HregionHvalid")
            as (w) "(Hregionl & Hvalidl & >Ha & Hva & Hregionh & Hvalidh)";
            [admit|admit|admit|].
          iDestruct (extract_r (<[PC:=inr (RX, Global, b, e, a)]> r) PC
                               (inr (RX, Global, b, e, a))
                       with "[Hmreg]") as "[HPC HPCmap]";
            first by apply (lookup_insert r PC). iFrame.
          destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
          - admit. (* Jmp *)
          - admit. (* Jnz *)
          - admit. (* Mov *)
          - (* Load *)
            (* these come from the reg interp relation *)
            iAssert (∃ w, dst ↦ᵣ w)%I as (wdst) "Hdst"; [admit|].
            iAssert (∃ w, src ↦ᵣ w)%I as (wsrc) "Hsrc"; [admit|].
            destruct wsrc eqn:Hsrc; [admit|].
            destruct c. do 3 destruct p0.
            iAssert (∃ w, a0 ↦ₐ w)%I as (wa0) "Ha0"; [admit|].
            
            iApply (wp_load_success with "[HPC Hdst Hsrc Ha Ha0]"); eauto.
            + admit.
            + admit.
            + admit.
            + iFrame.
            + iNext. iIntros "(HPC & Hdst & Ha) /=".
              iApply wp_pure_step_later; eauto.
              destruct p.
              {  }
              
              iApply "Hcls". iNext. 
              (* STUCK: How can we get the resources from a wand under a fupd *)
              (* is this even possible.... *)
              admit.
          - admit. (* Store *)
          - admit. (* Lt *)
          - admit. (* Add *)
          - admit. (* Sub *)
          - admit. (* Lea *)
          - admit. (* Restrict *)
          - admit. (* Subseg *)
          - admit. (* IsPtr *)
          - admit. (* GetL *)
          - admit. (* GetP *)
          - admit. (* GetB *)
          - admit. (* GetE *)
          - admit. (* GetA *)
          - admit. (* Fail *)
          - admit. (* Halt *)
        } 
        { (* Incorrect PC *) admit. }
        { iApply (wp_pure_step_later _ _ (Seq (Instr Failed) _)). }
      + (* Local *) admit.
    - admit.
    - admit. 
  Admitted. 
  
End fundamental. 