From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
Import uPred. 

Definition gen_regUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR (leibnizC V)).
Definition to_gen_reg {L V} `{Countable L} : gmap L V → gen_regUR L V :=
  fmap (λ v, to_agree (v : leibnizC V)).

Class gen_regG (L V : Type) (Σ : gFunctors) `{Countable L} := GenRegG {
  gen_reg_inG :> inG Σ (authR (gen_regUR L V));
  gen_reg_name : gname
}.
Arguments gen_reg_name {_ _ _ _ _} _ : assert.



Section reg_definitions.
  Context `{Countable L, rG : !gen_regG L V Σ}.

  Definition gen_reg_ctx (σ : gmap L V) : iProp Σ :=
    own (gen_reg_name rG) (● (to_gen_reg σ)).

  Definition mapsto_reg_def (l : L) (v: V) : iProp Σ :=
    own (gen_reg_name rG) (◯ {[ l := to_agree (v : leibnizC V) ]}).
  Definition mapsto_reg_aux : seal (@mapsto_reg_def). by eexists. Qed.
  Definition mapsto_reg := mapsto_reg_aux.(unseal).
  Definition mapsto_reg_eq : @mapsto_reg = @mapsto_reg_def := mapsto_reg_aux.(seal_eq).

End reg_definitions.

Local Notation "l ↦ᵣ v" := (mapsto_reg l v)
  (at level 20, format "l  ↦ᵣ  v") : bi_scope.

Local Notation "l ↦ᵣ -" := (∃ v, l ↦ᵣ v)%I
  (at level 20, format "l  ↦ᵣ  -") : bi_scope.


Section to_gen_reg.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.

  (** Conversion to heaps and back *)
  Lemma to_gen_reg_valid σ : ✓ to_gen_reg σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_gen_reg_None σ l : σ !! l = None → to_gen_reg σ !! l = None.
  Proof. by rewrite /to_gen_reg lookup_fmap=> ->. Qed.
  Lemma gen_reg_singleton_included σ l v :
    {[l := to_agree v]} ≼ to_gen_reg σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[av []].
    rewrite /to_gen_reg lookup_fmap fmap_Some_equiv => -[v' [Hl /= ->]].
    move=> /Some_included_total /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
  Lemma to_gen_reg_insert l v σ :
    to_gen_reg (<[l:=v]> σ) = <[l:= to_agree (v:leibnizC V)]> (to_gen_reg σ).
  Proof. by rewrite /to_gen_reg fmap_insert. Qed.
  Lemma to_gen_reg_delete l σ :
    to_gen_reg (delete l σ) = delete l (to_gen_reg σ).
  Proof. by rewrite /to_gen_reg fmap_delete. Qed.
End to_gen_reg.

Section gen_reg.
  Context {L V} `{Countable L, !gen_regG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types h g : gen_regUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_reg_timeless l v : Timeless (l ↦ᵣ v).
  Proof. rewrite mapsto_reg_eq /mapsto_reg_def. apply _. Qed.
 
  Lemma mapsto_reg_agree l v1 v2 : l ↦ᵣ v1 -∗ l ↦ᵣ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_reg_eq /mapsto_reg_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid.
    by intros ?%agree_op_invL'.
  Qed.
    
  Lemma gen_reg_alloc σ l v :
    σ !! l = None → gen_reg_ctx σ ==∗ gen_reg_ctx (<[l:=v]>σ) ∗ l ↦ᵣ v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_reg_ctx mapsto_reg_eq /mapsto_reg_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (to_agree (v:leibnizC _)))=> //.
      by apply lookup_to_gen_reg_None. }
    iModIntro. rewrite to_gen_reg_insert. iFrame.
  Qed.

  Lemma mapto_reg_dupl l v : l ↦ᵣ v ⊣⊢ l ↦ᵣ v ∗ l ↦ᵣ v.
    iSplit.
    - iIntros "Hl". rewrite /gen_reg_ctx mapsto_reg_eq /mapsto_reg_def.
      iApply own_op.
      rewrite -auth_frag_op op_singleton agree_idemp.
      iFrame. 
    - iIntros "[Hl Hl']". iFrame. 
  Qed.

  Lemma gen_reg_valid σ l v : gen_reg_ctx σ -∗ l ↦ᵣ v -∗
     gen_reg_ctx σ ∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_reg_ctx mapsto_reg_eq /mapsto_reg_def.
    iDestruct (own_valid_2 with "Hσ Hl") as "#Hs". iFrame. 
    iDestruct "Hs" as %[Hl%gen_reg_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.

  Lemma gen_reg_lookup σ l v :
    σ !! l = Some v → to_gen_reg σ !! l = Some (to_agree v). 
  Proof.
    intros Hsome.
    apply (fmap_Some_2 to_agree) in Hsome.
    rewrite -Hsome. by rewrite -lookup_fmap.
  Qed. 

  Lemma gen_heap_dealloc σ l v :
    gen_reg_ctx σ -∗ l ↦ᵣ v ==∗ gen_reg_ctx (delete l σ).
  Proof.
    iIntros "Hσ Hl".
    iDestruct (mapto_reg_dupl with "Hl") as "[Hl Hl']". 
    iDestruct (gen_reg_valid σ l v with "Hσ Hl'") as "[Hσ #Hsome]".
    iDestruct "Hsome" as %Hsome. 
    rewrite /gen_reg_ctx mapsto_reg_eq /mapsto_reg_def to_gen_reg_delete.
    iApply (own_update_2 with "Hσ Hl").
    eapply auth_update_dealloc, (delete_singleton_local_update_cancelable _ _ _).
    apply gen_reg_lookup in Hsome. rewrite Hsome. done. 
    Unshelve. 
    apply cancelable_Some; try apply _.
    apply discrete_id_free; try apply _.
    intros. Admitted. 

    
  Lemma gen_heap_update σ l v1 v2 :
    gen_reg_ctx σ -∗ l ↦ᵣ v1 ==∗ gen_reg_ctx (<[l:=v2]>σ) ∗ l ↦ᵣ v2.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_reg_ctx mapsto_reg_eq /mapsto_reg_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_reg_singleton_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update.
      eapply (singleton_local_update (to_gen_reg σ) l (to_gen_reg σ) _ (to_agree v2));
        first by apply gen_reg_lookup. 
      exact       
      
      Unshelve. 
      (cancel_local_update _ _)=> //.
      by rewrite /to_gen_reg lookup_fmap Hl. rewrite /valid}
    iModIntro. rewrite to_gen_heap_insert. iFrame.
  Qed.
End gen_heap.
