From iris.algebra Require Import gmap auth excl csum.
From iris.base_logic Require Import lib.own saved_prop.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import cap_lang stdpp_extra.
From cap_machine Require Import logical_mapsto.


(* No Excl' here: do not want the valid option element, as this disallows us from changing the branch in the sum type *)
Lemma csum_alter_l_r {A : cmra} {C : ofe} (a : A) (c : C) : ✓ a → Cinl (Excl c) ~~> Cinr a.
Proof.
  intros Hv. by apply cmra_update_exclusive.
Qed.

Lemma Excl_included_false : ∀ {A : ofe} {a b : A}, Excl a ≼ Excl b → False.
Proof.
  intros * Hi. by apply (exclusive_included _ _ Hi).
Qed.

(* resources *)

Class sealStoreG Σ := SealStoreG { (* Create record constructor for typeclass *)
    SG_sealStore ::  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
    SG_storedPreds ::  savedPredG Σ LWord;
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))); savedPredΣ LWord].

Class sealStorePreG Σ := {
    SG_sealStorePre ::  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
    SG_storedPredsPre ::  savedPredG Σ LWord;
}.

Instance sealStoreG_preG `{sealStoreG Σ} : sealStorePreG Σ.
Proof. constructor. all: apply _. Defined.

Global Instance subG_sealStorePreΣ {Σ}:
  subG sealStorePreΣ Σ →
  sealStorePreG Σ.
Proof. solve_inG. Qed.

(* Auxiliary lemma's about gmap domains *)
Lemma gmap_none_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom g1 = dom g2 →
    g1 !! i = None → g2 !! i = None.
Proof.
  intros Hdom Hnon.
  apply not_elem_of_dom in Hnon.
  rewrite Hdom in Hnon.
  by apply not_elem_of_dom.
Qed.

Lemma gmap_isSome_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom g1 = dom g2 →
    is_Some (g1 !! i) → is_Some (g2 !! i).
Proof.
  intros Hdom Hnon.
  apply elem_of_dom in Hnon.
  rewrite Hdom in Hnon.
  by apply elem_of_dom.
Qed.

Section Store.
  Context `{!sealStoreG Σ}.

  Definition seal_pred (o : OType) (P : LWord → iProp Σ) :=
    (∃ γpred: gname, own SG_sealN ({[o := Cinr (to_agree γpred)]})
                     ∗ saved_pred_own γpred DfracDiscarded P)%I.
  Global Instance seal_pred_persistent i P : Persistent (seal_pred i P).
  Proof. apply _. Qed.
  Definition can_alloc_pred (o : OType) :=
    (own SG_sealN ({[o := Cinl (Excl ())]}))%I.

  Lemma seal_pred_agree o P P':
    seal_pred o P -∗ seal_pred o P' -∗ (∀ x, ▷ (P x ≡ P' x)).
  Proof.
    iIntros "Hr1 Hr2".
    rewrite /seal_pred.
    iDestruct "Hr1" as (γ1) "[Hown1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hown2 Hpred2]".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.
    rewrite singleton_op singleton_valid -Cinr_op Cinr_valid  to_agree_op_valid_L in Hv. subst.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma seal_store_update_alloc (o : OType) (P : LWord → iProp Σ):
   can_alloc_pred o ==∗ seal_pred o P.
  Proof.
    rewrite /seal_pred /can_alloc_pred.
    iIntros "Hown".
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP"; first apply dfrac_valid_discarded.


    iMod (own_update _ _ ({[o := Cinr (to_agree γalloc)]}) with "Hown").
    { apply singleton_update. eauto. by apply csum_alter_l_r. }
    iExists _; iFrame; done.
  Qed.

  Lemma seal_store_update_alloc_batch
    (seals : gset OType) (φ : OType -> LWord → iProp Σ) :
    ⊢ ([∗ set] o ∈ seals, can_alloc_pred o) ==∗ ([∗ set] o ∈ seals, seal_pred o (φ o))%I.
  Proof.
    induction seals using set_ind_L; iIntros "Hfree"; first by iModIntro.
    assert ({[x]} ## X) by set_solver.
    rewrite !big_sepS_union //.
    iDestruct "Hfree" as "[Hfree_x Hfree]".
    iSplitL "Hfree_x"; last iApply (IHseals with "[$]").
    rewrite !big_sepS_singleton //.
    by iApply seal_store_update_alloc.
  Qed.

  Lemma seal_store_update_alloc_batch_const
    (seals : gset OType) (φ : LWord → iProp Σ) :
    ⊢ ([∗ set] o ∈ seals, can_alloc_pred o) ==∗ ([∗ set] o ∈ seals, seal_pred o φ)%I.
  Proof.
    set (Φ := fun ot : OType => φ).
    iApply ( seal_store_update_alloc_batch seals Φ ).
  Qed.

End Store.

(* Initialize the seal store under an arbitrary name *)
Lemma seal_store_init `{sealStorePreG Σ'} oset:
 ⊢ (|==> ∃ (_ : sealStoreG Σ'), ([∗ set] o ∈ oset, can_alloc_pred o) : iProp Σ')%I.
Proof.
  iMod (own_alloc (A:= (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)))) ((gset_to_gmap (Cinl (Excl ())) oset): gmap OType (csumR (exclR unitO) (agreeR gnameO)))) as (γ) "H".
  { intros i. destruct (gset_to_gmap _ _ !! i) eqn:Heq; last done.
    apply lookup_gset_to_gmap_Some in Heq. by destruct Heq as [_ <-]. }
  iModIntro. iExists (SealStoreG _ _ _ γ).

  iInduction oset as [| x oset Hni] "IH" using set_ind_L; first done.
  iApply big_sepS_union. set_solver.
  rewrite gset_to_gmap_union_singleton.
  rewrite insert_singleton_op. 2: rewrite lookup_gset_to_gmap_None; set_solver.
  iDestruct (own_op with "H") as "[Hx H]".
  iSplitL "Hx".
  - by iApply big_sepS_singleton.
  - by iApply "IH".
Qed.
