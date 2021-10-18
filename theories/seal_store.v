From iris.algebra Require Import agree gmap auth excl.
From iris.base_logic Require Import lib.own saved_prop.
From iris.proofmode Require Import tactics.
From cap_machine Require Import cap_lang stdpp_extra.

(* resources *)

Class sealStoreG Σ := SealStoreG { (* Create record constructor for typeclass *)
    SG_sealStore :>  inG Σ (authUR (gmapUR OType (agreeR gnameO)));
    SG_storedPreds :>  savedPredG Σ Word;
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (authUR (gmapUR OType (agreeR gnameO))); savedPredΣ Word].

Class sealStorePreG Σ := {
    SG_sealStorePre :>  inG Σ (authUR (gmapUR OType (agreeR gnameO)));
    SG_storedPredsPre :>  savedPredG Σ Word;
}.

Instance sealStoreG_preG `{sealStoreG Σ} : sealStorePreG Σ.
Proof. constructor. all: apply _. Defined.

Global Instance subG_sealStorePreΣ {Σ}:
  subG sealStorePreΣ Σ →
  sealStorePreG Σ.
Proof. solve_inG. Qed.

(* Auxiliary lemma's about gmap domains *)
Lemma gmap_none_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom (gset K) g1 = dom (gset K) g2 →
    g1 !! i = None → g2 !! i = None.
Proof.
  intros Hdom Hnon.
  apply elem_of_gmap_dom_none in Hnon.
  rewrite Hdom in Hnon.
  by apply elem_of_gmap_dom_none.
Qed.

Lemma gmap_isSome_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom (gset K) g1 = dom (gset K) g2 →
    is_Some (g1 !! i) → is_Some (g2 !! i).
Proof.
  intros Hdom Hnon.
  apply elem_of_gmap_dom in Hnon.
  rewrite Hdom in Hnon.
  by apply elem_of_gmap_dom.
Qed.

Section Store.
  Context `{!sealStoreG Σ}.

  Definition sealStore_map_def (Mγ: gmap OType gname) (preds: gmap OType (Word → iProp Σ)) : iProp Σ :=
    ([∗ map] o↦γpred ∈ Mγ,
     ∃ P, ⌜preds !! o = Some P⌝ ∗ saved_pred_own γpred P)%I.

  Definition seal_store_agree (Mγ : gmap OType gname) :
    gmapUR OType (agreeR gnameO) := to_agree <$> Mγ.
  Definition seal_store (preds : gmap OType (Word → iProp Σ)) : iProp Σ :=
    ∃ Mγ, own SG_sealN (● seal_store_agree Mγ) ∗ ⌜dom (gset _) Mγ = dom (gset _) preds⌝ ∗ sealStore_map_def Mγ preds.
  Definition seal_pred (o : OType) (P : Word → iProp Σ) :=
    (∃ γpred: gname, own SG_sealN (◯ {[o := to_agree γpred]}) ∗ saved_pred_own γpred P)%I.

  Global Instance seal_pred_persistent i P : Persistent (seal_pred i P).
  Proof. apply _. Qed.

  Lemma seal_store_update (o : OType) st (P : Word → iProp Σ):
    st !! o = None →
    seal_store st ==∗ seal_store (<[o:=P]> st) ∗ seal_pred o P.
  Proof.
    rewrite /seal_store /seal_store_agree /seal_pred.
    iIntros (Hnon) "Hss"; iDestruct "Hss" as (Mγ) "[Hown [Hdom Hdef]]". iDestruct "Hdom" as %Hdom.
    apply (gmap_none_convert _ Mγ) in Hnon; auto.
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP".
    iMod (own_update _ _ (● _ ⋅ ◯ {[o := to_agree γalloc]}) with "Hown") as "[Hauth Hfrag]".
    { apply auth_update_alloc.
    apply alloc_singleton_local_update; last done.
    by rewrite lookup_fmap Hnon. }
    rewrite <-fmap_insert.
    iSplitL "Hauth Hdef"; iExists _ ; iFrame; auto.
    rewrite !dom_insert_L.
    iSplitR.
    {iPureIntro. by rewrite Hdom. }
    rewrite /sealStore_map_def.
    iApply big_sepM_insert; auto.
    iSplitR "Hdef".
    - iExists _; iFrame "#". by rewrite lookup_insert.
    - iApply (big_sepM_mono with "Hdef").
      iIntros (o' g' Hsome) "Hog".
      iDestruct "Hog" as (P0) "[% Hsaved]".
      iExists _ ; iFrame.
      destruct (decide (o = o')) as [-> | Hne].
      + rewrite lookup_insert; congruence.
      + rewrite lookup_insert_ne ; auto.
  Qed.

  Lemma seal_pred_agree o P P':
    seal_pred o P -∗ seal_pred o P' -∗ (∀ x, ▷ (P x ≡ P' x)).
  Proof.
    iIntros "Hr1 Hr2".
    rewrite /seal_pred.
    iDestruct "Hr1" as (γ1) "[Hown1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hown2 Hpred2]".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid to_agree_op_valid_L in Hv |- * => <-.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma seal_full_frag_lkup o st P:
    seal_store st -∗ seal_pred o P -∗  ∃ P', (∀ x, ▷ (P x ≡ P' x)) ∗ ⌜st !! o = Some P'⌝.
  Proof.
    rewrite /seal_store /seal_store_agree /seal_pred.
    iIntros "Hss Hsp".
    iDestruct "Hss" as (Mγ) "[Hown1 [Hdom Hdef]]". iDestruct "Hdom" as %Hdom.
    iDestruct "Hsp" as (γpred) "[Hown2 Hsave]".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.

    (* Now derive My!!o=γpred *)
    apply auth_both_valid_discrete in Hv; destruct Hv as [Hv1 Hv2].
    specialize (Hv2 o).
    apply singleton_included_l in Hv1.
    destruct Hv1 as (y & Heq & Hi).
    rewrite ->Heq in Hv2.
    rewrite ->Some_included_total in Hi.
    apply to_agree_uninj in Hv2 as [y' Hy].
    revert Hi Heq; rewrite -Hy => Hi Heq.
    apply to_agree_included in Hi.
    rewrite ->leibniz_equiv_iff in Hi; subst y'.
    revert Heq; rewrite lookup_fmap fmap_Some_equiv => Heq.
    destruct Heq as [γ [HMy Hrx] ].
    apply to_agree_inj in Hrx. rewrite ->leibniz_equiv_iff in Hrx; subst γ.

    iDestruct (big_sepM_delete _ _ o with "Hdef") as "[Ho _]";[eauto|].
    iDestruct "Ho" as (P') "[% Hsave']".
    iExists (P').
    iSplitL; auto. iIntros (x).
    iApply (saved_pred_agree with "Hsave Hsave'").
Qed.

End Store.

(* Initialize the seal store under an arbitrary name *)
Lemma seal_store_init `{sealStorePreG Σ'}:
 ⊢ (|==> ∃ (_ : sealStoreG Σ'), seal_store (∅ :  gmap OType (Word → iProp Σ') ) : iProp Σ')%I.
Proof.
    iMod (own_alloc (A:= (authR (gmapUR OType (agreeR gnameO)))) (● (to_agree <$> (∅: gmap OType (leibnizO gname))))) as (γ) "H".
    { rewrite fmap_empty. by apply auth_auth_valid. }
    iModIntro. iExists (SealStoreG _ _ _ γ), ∅.
    iFrame.
    iSplitL; [rewrite !dom_empty_L | rewrite /sealStore_map_def]; auto.
Qed.
