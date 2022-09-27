From iris.algebra Require Import gmap auth excl csum.
From iris.base_logic Require Import lib.own saved_prop.
From iris.proofmode Require Import tactics.
From cap_machine Require Import cap_lang stdpp_extra.


(* No Excl' here: do not want the valid option element, as this disallows us from changing the branch in the sum type *)
Lemma csum_alter_l_r {A : cmra} {C : ofe} (a : A) (c : C) : ✓ a → Cinl (Excl c) ~~> Cinr a.
Proof. intros Hv n [[l|r|]|]; simpl in *; auto; intro Hval.
        - by exfalso.
        - generalize n. by rewrite <- cmra_valid_validN.
Qed.

Lemma Excl_included_false : ∀ {A : ofe} {a b : A}, Excl a ≼ Excl b → False.
Proof. intros * Hi. unfold "_ ≼ _" in Hi. destruct Hi as [z Hi]. rewrite /op /cmra_op in Hi. cbn in Hi. rewrite /excl_op_instance in Hi. inversion Hi.
Qed.

(* resources *)

Class sealStoreG Σ := SealStoreG { (* Create record constructor for typeclass *)
    SG_sealStore :>  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
    SG_storedPreds :>  savedPredG Σ Word;
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))); savedPredΣ Word].

Class sealStorePreG Σ := {
    SG_sealStorePre :>  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
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

  Definition seal_pred (o : OType) (P : Word → iProp Σ) :=
    (∃ γpred: gname, own SG_sealN ({[o := Cinr (to_agree γpred)]}) ∗ saved_pred_own γpred P)%I.
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
    rewrite singleton_op singleton_valid -Cinr_op Cinr_valid  to_agree_op_valid_L in Hv |- * => <-.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma seal_store_update_alloc (o : OType) (P : Word → iProp Σ):
   can_alloc_pred o ==∗ seal_pred o P.
  Proof.
    rewrite /seal_pred /can_alloc_pred.
    iIntros "Hown".
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP".


    iMod (own_update _ _ ({[o := Cinr (to_agree γalloc)]}) with "Hown").
    { apply singleton_update. eauto. by apply csum_alter_l_r. }
    iExists _; iFrame; done.
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
