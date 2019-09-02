From iris.base_logic Require Export invariants na_invariants.
From iris.proofmode Require Import tactics.

Section range_inv.
  Context `{!invG Σ}.

  Definition range_inv N P Q : iProp Σ :=
    (□ (∀ E, ⌜↑N ⊆ E⌝ ={E,E ∖ ↑N}=∗ (▷ P) ∗ (▷ Q ={E ∖ ↑N, E}=∗ True)))%I.

  Lemma range_inv_alloc N E P Q : □ (Q -∗ P) ∗ ▷ P ={E}=∗ range_inv N P Q.
  Proof.
    iIntros "[#HQP HI]".
    iMod (inv_alloc N _ P with "HI") as "#Hinv".
    iModIntro. iAlways.
    iIntros (E' Hsub).
    iInv N as "HI" "Hcls".
    iFrame. iModIntro. iIntros "Q".
    iApply "Hcls".
    iApply "HQP". iFrame. 
  Qed.

  Lemma range_inv_tighten_r N P Q Q' :
    □ (Q' -∗ Q) -∗ range_inv N P Q -∗ range_inv N P Q'.
  Proof.
    iIntros "#HQQ' #Hinv".
    iAlways. iIntros (E Hsub).
    iMod ("Hinv" $! E Hsub) as "[HP Hcls]".
    iModIntro. iFrame.
    iIntros "HQ'".
    iApply "Hcls".
    iApply "HQQ'".
    iFrame. 
  Qed.

  Lemma range_inv_tighten_l N P P' Q :
    □ (P -∗ P') -∗ range_inv N P Q -∗ range_inv N P' Q.
  Proof.
    iIntros "#HPP' #Hinv".
    iAlways. iIntros (E Hsub).
    iMod ("Hinv" $! E Hsub) as "[HP Hcls]".
    iModIntro. iFrame.
    iApply "HPP'".
    iFrame. 
  Qed.

End range_inv.

Section abstract_inv.
  Context `{!invG Σ}.

  Definition abstract_inv I N : iProp Σ :=
    (□ (∀ E, ⌜↑N ⊆ E⌝ ={E,E ∖ ↑N}=∗ (▷ I) ∗ (▷ I ={E ∖ ↑N, E}=∗ True)))%I.

  Lemma abstract_inv_alloc N E I : ▷ I ={E}=∗ abstract_inv I N.
  Proof.
    iIntros "HI".
    iMod (inv_alloc N _ I with "HI") as "#Hinv".  
    iModIntro. iAlways.
    iIntros (E' Hsub).
    iInv N as "HI" "Hcls".
    iFrame. by iModIntro. 
  Qed.     
      
  Lemma abstract_inv_implies {A : Type} (P : iProp Σ) (Q : A → iProp Σ) N (a b : A) `{!∀ x, Persistent (Q x)} :
    □ (Q a -∗ Q b) -∗ abstract_inv (P ∗ Q a) N -∗ abstract_inv (P ∗ Q b) N. 
  Proof.
    iIntros "#HQimpl #Hinv".
    iAlways. iIntros (E Hsub).
    iMod ("Hinv" $! E Hsub) as "[[HP #HQ] Hcls]".
    iModIntro. iSplitL "HQ HP".
    - iNext. iFrame. iApply "HQimpl". iFrame "#".
    - iIntros "[HP HQb]". iApply "Hcls". iNext.
      iFrame. iFrame "#".
  Qed.

End abstract_inv. 

Section na_abstract_inv.
  Context `{!invG Σ,!na_invG Σ}.
  
  Definition na_abstract_inv p N I : iProp Σ :=
    (□ (∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → na_own p F ={E}=∗
                (▷ I ∗ na_own p (F ∖ ↑N))
                ∗ (▷ I ∗ na_own p (F ∖ ↑N) ={E}=∗ na_own p F)))%I.

  Lemma na_abstract_inv_alloc p N E I : ▷ I ={E}=∗ na_abstract_inv p N I.
  Proof.
    iIntros "HI".
    iMod (na_inv_alloc p E N I with "HI") as "#Hinv".  
    iModIntro. iAlways.
    iIntros (E' F' HsubE HsubF) "Hna".
    iInv N as "(Hi & Hna)" "Hcls".
    iFrame. by iModIntro. 
  Qed.     
  
  Lemma na_abstract_inv_implies {A : Type} (P : iProp Σ) (Q : A → iProp Σ) N p (a b : A) `{!∀ x, Persistent (Q x)} :
    □ (Q a -∗ Q b) -∗ na_abstract_inv p N (P ∗ Q a) -∗ na_abstract_inv p N (P ∗ Q b). 
  Proof.
    iIntros "#HQimpl #Hinv".
    iAlways. iIntros (E F HsubE HsubF) "Hna". 
    iMod ("Hinv" $! E F HsubE HsubF with "Hna") as "[[[HP #HQ] Hna] Hcls]".
    iModIntro. iSplitL "HQ HP Hna".
    - iFrame. iNext. iApply "HQimpl". iFrame "#".
    - iIntros "[[HP HQb] Hna]". iApply "Hcls". iFrame. iFrame "#".  
  Qed.
  

End na_abstract_inv.

  