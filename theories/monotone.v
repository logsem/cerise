From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel. 
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Lemma interp_monotone W W' w :
    (⌜related_sts_pub W.1 W'.1 W.2 W'.2⌝ →
    𝕍(W) w -∗ 𝕍(W') w)%I. 
  Proof.
    iIntros (Hrelated) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=. 
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto. 
    - iDestruct "Hw" as (g b e a') "[% Hw]". inversion H3; subst.
      iDestruct "Hw" as (p Hfl) "[Hbe Hexec]".
      iExists _,_,_,_. iSplitR;[eauto|].
      iExists _. iSplitR;[eauto|]. iFrame "#".
      iAlways.
      iIntros (a r W'' Hin).
      destruct g; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro. 
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame. 
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame.
    - iDestruct "Hw" as ( g b e a' Heq) "Hw". inversion Heq; subst.
      iExists _,_,_,_. iSplitR; [eauto|].
      iAlways. iIntros (r W'').
      destruct g; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto.
        }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iFrame.
    - iDestruct "Hw" as (g b e a' Heq) "Hexec". inversion Heq;subst.
      iDestruct "Hexec" as (p Hfl) "[Hbe Hexec]".
      iExists _,_,_,_. iSplitR;[eauto|].
      iExists p. iSplit;[auto|].
      iFrame "#". iAlways. iIntros (a r W'' Hin). 
      destruct g; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro. 
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame. 
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame.  
    - iDestruct "Hw" as (g b e a' Heq) "Hexec". inversion Heq;subst.
      iDestruct "Hexec" as (p Hfl) "[Hbe Hexec]".
      iExists _,_,_,_. iSplitR;[eauto|].
      iExists p. iSplit;[auto|].
      iFrame "#". iAlways. iIntros (a r W'' Hin). 
      destruct g; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global W W'')%I as "Hrelated".
        { iPureIntro. 
          apply related_sts_pub_priv_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame. 
      + iIntros (Hrelated').
        iAssert (future_world Local W W'')%I as "Hrelated".
        { iPureIntro.
          apply related_sts_pub_trans with W'.1 W'.2; auto. 
        }
        iSpecialize ("Hexec" $! a r W'' Hin with "Hrelated").
        iFrame. 
  Qed.

  Lemma region_monotone W W' :
    (⌜related_sts_pub W.1 W'.1 W.2 W'.2⌝ → region W -∗ region W')%I.
  Proof.
    iIntros (Hrelated) "HW".
    iDestruct "HW" as (M) "[HM Hmap]". 
    iExists (M). iFrame.
    iApply big_sepM_mono; iFrame. 
    iIntros (a γ Hsome) "Hm". 
    iDestruct "Hm" as (γpred v p φ Heq HO) "(Hl & #Hmono & #Hsavedφ & Hφ)".
    iExists _,_,_,_. do 2 (iSplitR;[eauto|]). iFrame "∗ #".
    iApply "Hmono"; iFrame; auto.
  Qed. 
    
End monotone. 