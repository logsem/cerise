From iris.algebra Require Import agree gmap auth excl csum.
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
    SG_sealStore :>  inG Σ (authUR (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))));
    SG_storedPreds :>  savedPredG Σ Word;
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (authUR (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)))); savedPredΣ Word].

Class sealStorePreG Σ := {
    SG_sealStorePre :>  inG Σ (authUR (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))));
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

  Definition sealStore_map_def (Mγ: gmap OType (option gname)) (preds: gmap OType (option (Word → iProp Σ))) : iProp Σ :=
    ([∗ map] o↦oγpred ∈ Mγ,
     match oγpred with
     | None => ⌜preds !! o = Some None ⌝
     | Some γpred => ∃ P, ⌜preds !! o = Some (Some P)⌝ ∗ saved_pred_own γpred P end )%I.

  Definition seal_store_agree (Mγ : gmap OType (option gname)) :
    gmapUR OType (csumR (exclR unitO) (agreeR gnameO)) := (λ o , match o with | Some g => Cinr (to_agree g) | None => Cinl (Excl ()) end ) <$> Mγ.
  Definition seal_store (preds : gmap OType (option (Word → iProp Σ))) : iProp Σ :=
    ∃ Mγ, own SG_sealN (● seal_store_agree Mγ) ∗ ⌜dom (gset _) Mγ = dom (gset _) preds⌝ ∗ sealStore_map_def Mγ preds.

  Definition seal_pred (o : OType) (P : Word → iProp Σ) :=
    (∃ γpred: gname, own SG_sealN (◯ {[o := Cinr (to_agree γpred)]}) ∗ saved_pred_own γpred P)%I.
  Global Instance seal_pred_persistent i P : Persistent (seal_pred i P).
  Proof. apply _. Qed.
  Definition can_alloc_pred (o : OType) :=
    (own SG_sealN (◯ {[o := Cinl (Excl ())]}))%I.

  Lemma seal_store_update (o : OType) st (P : Word → iProp Σ):
    st !! o = None →
    seal_store st ==∗ seal_store (<[o:=Some P]> st) ∗ seal_pred o P.
  Proof.
    rewrite /seal_store /seal_store_agree /seal_pred.
    iIntros (Hnon) "Hss"; iDestruct "Hss" as (Mγ) "[Hown [Hdom Hdef]]". iDestruct "Hdom" as %Hdom.
    apply (gmap_none_convert _ Mγ) in Hnon; auto.
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP".
    iMod (own_update _ _ (● _ ⋅ ◯ {[o := Cinr (to_agree γalloc)]}) with "Hown") as "[Hauth Hfrag]".
    { apply auth_update_alloc.
    apply alloc_singleton_local_update; last done.
    by rewrite lookup_fmap Hnon. }
    change (Cinr (to_agree γalloc)) with ((λ o0 : option gname,
                       match o0 with
                       | Some g => Cinr (to_agree g)
                       | None => Cinl (Excl ())
                       end) (Some γalloc)).
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
      iIntros (o' g' Hsome) "Hog". destruct g'.
      * iDestruct "Hog" as (P0) "[% Hsaved]".
        iExists _ ; iFrame.
        destruct (decide (o = o')) as [-> | Hne].
        + rewrite lookup_insert; congruence.
        + rewrite lookup_insert_ne ; auto.
     * destruct (decide (o = o')) as [-> | Hne].
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
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid -Cinr_op Cinr_valid  to_agree_op_valid_L in Hv |- * => <-.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma sealStore_map_is_some (Mγ : gmap (finz ONum) (csumR (exclR unitO) (agreeR gnameO))) o x:  ✓ (● Mγ ⋅ ◯ {[o := x]}) -> Mγ !! o ≡ Some x.
    intros Hv.
    apply auth_both_valid_discrete in Hv; destruct Hv as [Hv1 Hv2].
    specialize (Hv2 o).
    apply singleton_included_l in Hv1.
    destruct Hv1 as (y & Heq & Hi).
    rewrite Heq Some_valid in Hv2 * => Hy.
    rewrite Some_included /= in Hi * => - [ | Hi]; first by intros ->.
    apply cmra_valid_included in Hi as Hx; auto.
    rewrite csum_included in Hi |- * => - [ ? |  [Hi | Hi]].
    - subst y ; by exfalso.
    - destruct Hi as [a [ a' [ -> [-> HFalse]]]].
      destruct a, a'; try contradiction.
      by apply Excl_included_false in HFalse.
    - destruct Hi as [a [ a' [ -> [-> Hi]]]].
      rewrite Cinr_valid in Hy * => Hy.
      apply agree_included in Hi. rewrite ->Hi in Hy.
      by apply agree_op_inv in Hy as ->.
  Qed.

  Lemma seal_full_frag_lkup o st P:
    seal_store st -∗ seal_pred o P -∗  ∃ P', (∀ x, ▷ (P x ≡ P' x)) ∗ ⌜st !! o = Some (Some P')⌝.
  Proof.
    rewrite /seal_store /seal_store_agree /seal_pred.
    iIntros "Hss Hsp".
    iDestruct "Hss" as (Mγ) "[Hown1 [Hdom Hdef]]". iDestruct "Hdom" as %Hdom.
    iDestruct "Hsp" as (γpred) "[Hown2 Hsave]".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.

    (* Now derive My!!o=γpred *)
    apply sealStore_map_is_some in Hv.
    assert (Mγ !! o = Some (Some γpred)) as HMo.
    { rewrite -leibniz_equiv_iff.
      rewrite lookup_fmap in Hv.
      destruct (Mγ !! o) as [o1|]; last inversion Hv.
      cbn in Hv. apply Some_equiv_inj in Hv.
      destruct o1 as [o1' | ]; last inversion Hv.
      by apply Cinr_inj, to_agree_inj in Hv as ->. }

    iDestruct (big_sepM_delete _ _ o with "Hdef") as "[Ho _]";[eauto|].
    iDestruct "Ho" as (P') "[% Hsave']".
    iExists (P').
    iSplitL; auto. iIntros (x).
    iApply (saved_pred_agree with "Hsave Hsave'").
  Qed.

  Lemma seal_store_update_alloc (o : OType) st (P : Word → iProp Σ):
   seal_store st -∗ can_alloc_pred o ==∗ seal_store (<[o:=Some P]> st) ∗ seal_pred o P.
  Proof.
    rewrite /seal_store /seal_store_agree /can_alloc_pred.
    iIntros "Hss Hown2".
    iDestruct "Hss" as (Mγ) "[Hown1 [Hdom Hdef]]". iDestruct "Hdom" as %Hdom.
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.
    apply sealStore_map_is_some in Hv.
    apply equiv_Some_inv_r' in Hv as (x & Hv & Hequiv).
    assert (x = Cinl (Excl ())) as ->. { (* We can derive this, since Excl supports LeibnizEquiv -> we just need to bypass the agreement branch *)
      destruct x; try by inversion Hequiv. apply Cinl_inj in Hequiv.
      rewrite leibniz_equiv_iff in Hequiv * => Hequiv. by subst.
    }
    iDestruct (own_op with "[$Hown1 $Hown2]") as "Hown".


    iMod (own_update _ _ (● _ ⋅ ◯ {[o := Cinr (to_agree γalloc)]}) with "Hown") as "[Hauth Hfrag]".
    { apply auth_update.
      eapply singleton_local_update. eauto.
      apply replace_local_update; [apply _ | done ]. }

    change (Cinr (to_agree γalloc)) with ((λ o0 : option gname,
                       match o0 with
                       | Some g => Cinr (to_agree g)
                       | None => Cinl (Excl ())
                       end) (Some γalloc)).
    rewrite <-fmap_insert.
    iSplitL "Hauth Hdef"; iExists _ ; iFrame; auto.
    rewrite !dom_insert_L.
    iSplitR.

    {iPureIntro. by rewrite Hdom. }

    rewrite /sealStore_map_def.
    iApply (big_sepM_delete _ _ o). by rewrite lookup_insert.
    rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ o with "Hdef") as "[Ho Hdef]".
    { rewrite lookup_fmap in Hv.
      destruct (Mγ !! o) as [o1|]; last inversion Hv.
      cbn in Hv. apply Some_eq_inj in Hv.
      destruct o1 as [o1' | ]; first inversion Hv.
      eauto. }
    iDestruct "Ho" as %Ho.
    iSplitR.

    { iExists P. iFrame "#". by rewrite lookup_insert. }

    iApply (big_sepM_mono with "Hdef").
    iIntros (o' g' Hsome) "Hog".
    assert (o ≠ o') as Hoo'. { intros ->. by rewrite lookup_delete in Hsome. }
    destruct g'.
    * iDestruct "Hog" as (P0) "[% Hsaved]".
      iExists _ ; iFrame.
      rewrite lookup_insert_ne; auto.
    * rewrite lookup_insert_ne; auto.
  Qed.

End Store.

(* Initialize the seal store under an arbitrary name *)
(* TODO: version that has certain contents from the start? *)
Lemma seal_store_init `{sealStorePreG Σ'}:
 ⊢ (|==> ∃ (_ : sealStoreG Σ'), seal_store (∅ :  gmap OType (option (Word → iProp Σ')) ) : iProp Σ')%I.
Proof.
  iMod (own_alloc (A:= (authR (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))))) (● (∅: gmap OType (csumR (exclR unitO) (agreeR gnameO))))) as (γ) "H".
  { by apply auth_auth_valid. }
  iModIntro. iExists (SealStoreG _ _ _ γ), ∅.
  iSplitL.
  - iSimpl. unfold seal_store_agree; by rewrite fmap_empty.
  - iSplitL; [rewrite !dom_empty_L | rewrite /sealStore_map_def]; auto.
Qed.
