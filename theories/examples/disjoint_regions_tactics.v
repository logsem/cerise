From iris.proofmode Require Import proofmode.
From stdpp Require Import sets list.
From cap_machine Require Import addr_reg region.

Class DisjointList A := disjoint_list : list A → Prop.
#[export] Hint Mode DisjointList ! : typeclass_instances.
Instance: Params (@disjoint_list) 2 := {}.
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") : stdpp_scope.
Notation "##@{ A } Xs" :=
  (@disjoint_list A _ Xs) (at level 20, only parsing) : stdpp_scope.

Section disjoint_list.
  Variable A: Type.
  Context `{Disjoint A, Union A, Empty A}.
  Implicit Types X : A.

  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ##@{A} []
    | disjoint_cons_2 (X : A) (Xs : list A) : X ## ⋃ Xs → ## Xs → ## (X :: Xs).
  Global Existing Instance disjoint_list_default.

  Lemma disjoint_list_nil  : ##@{A} [] ↔ True.
  Proof. split; constructor. Qed.
  Lemma disjoint_list_cons X Xs : ## (X :: Xs) ↔ X ## ⋃ Xs ∧ ## Xs.
  Proof.
    split; [inversion_clear 1; auto |].
    intros [??]. constructor; auto.
  Qed.
End disjoint_list.

Lemma disjoint_mono_l A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Y ## Z → X ## Z.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Lemma disjoint_mono_r A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Z ## Y → Z ## X.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Definition ByReflexivity (P: Prop) :=
  P.
#[export] Hint Extern 1 (ByReflexivity _) => reflexivity : disj_regions.

Definition AddrRegionRange (l: list Addr) (b e: Addr) :=
  ∀ a, a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionRange_singleton a :
  ByReflexivity (eqb_addr a top = false) →
  AddrRegionRange [a] a (a^+1)%a.
Proof.
  unfold ByReflexivity. cbn. intros ?%Z.eqb_neq.
  intros a' ->%elem_of_list_singleton. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionRange_singleton : disj_regions.

Lemma AddrRegionRange_region_addrs b e :
  AddrRegionRange (finz.seq_between b e) b e.
Proof.
  intros a ?%elem_of_finz_seq_between. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionRange_region_addrs : disj_regions.

Definition AddrRegionsRange (ll: list (list Addr)) (b e: Addr) :=
  ∀ l a, l ∈ ll → a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionsRange_single l b e :
  AddrRegionRange l b e →
  AddrRegionsRange [l] b e.
Proof.
  intros Hl l' a ->%elem_of_list_singleton ?%Hl. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionsRange_single | 1 : disj_regions.

Lemma AddrRegionsRange_cons l ll b e b' e' :
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  AddrRegionsRange (l :: ll) (finz.min b b') (finz.max e e').
Proof.
  intros Hl Hll l' a [->|H]%elem_of_cons.
  - intros ?%Hl. solve_addr.
  - intros ?%Hll; auto. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionsRange_cons | 10 : disj_regions.

Instance Empty_list {A}: Empty (list A). exact []. Defined.
Instance Union_list {A}: Union (list A). exact app. Defined.
Instance Singleton_list {A}: Singleton A (list A). exact (λ a, [a]). Defined.

Lemma addr_range_union_incl_range (ll: list (list Addr)) (b e: Addr):
  AddrRegionsRange ll b e →
  ⋃ ll ⊆ finz.seq_between b e.
Proof.
  revert b e. induction ll as [| l ll].
  - intros. cbn. unfold subseteq, list_subseteq. unfold empty, Empty_list.
    inversion 1.
  - intros b e HInd. cbn. unfold union, Union_list, subseteq, list_subseteq.
    intros x. intros [Hx|Hx]%elem_of_app.
    + specialize (HInd l x ltac:(constructor) Hx). apply elem_of_finz_seq_between.
      solve_addr.
    + assert (HI: AddrRegionsRange ll b e).
      { intros ? ? ? ?. eapply HInd. apply elem_of_list_further; eassumption.
        auto. }
      specialize (IHll _ _ HI).
      rewrite elem_of_subseteq in IHll |- *.
      by apply IHll.
Qed.

Lemma AddrRegionRange_iff_incl_region_addrs l b e :
  AddrRegionRange l b e ↔ (l ⊆ finz.seq_between b e).
Proof.
  unfold AddrRegionRange, subseteq, list_subseteq.
  split.
  - intros H **. rewrite elem_of_finz_seq_between. by apply H.
  - intros H **. apply elem_of_finz_seq_between. by apply H.
Qed.

Lemma addr_range_disj_union_empty (l: list Addr) :
  l ## ⋃ [].
Proof.
  cbn. unfold empty, Empty_list, disjoint.
  unfold set_disjoint_instance. intros * ? ?%elem_of_nil. auto.
Qed.
#[export] Hint Resolve addr_range_disj_union_empty | 1 : disj_regions.

Lemma addr_range_disj_range_union (l: list Addr) ll b e b' e':
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  ByReflexivity ((e <=? b') || (e' <=? b) = true)%a →
  l ## ⋃ ll.
Proof.
  intros Hl Hll. unfold ByReflexivity.
  rewrite orb_true_iff !Z.leb_le.
  intros.
  rewrite AddrRegionRange_iff_incl_region_addrs in Hl |- *.
  eapply disjoint_mono_l; eauto.
  eapply disjoint_mono_r. eapply addr_range_union_incl_range; eauto.
  unfold disjoint.
  intro. rewrite !elem_of_finz_seq_between. solve_addr.
Qed.
#[export] Hint Resolve addr_range_disj_range_union | 10 : disj_regions.

Lemma addr_disjoint_list_empty : ## ([]: list (list Addr)).
Proof. constructor. Qed.
#[export] Hint Resolve addr_disjoint_list_empty : disj_regions.

Lemma addr_disjoint_list_cons (l: list Addr) ll :
  l ## ⋃ ll →
  ## ll →
  ## (l :: ll).
Proof. intros. rewrite disjoint_list_cons; auto. Qed.
#[export] Hint Resolve addr_disjoint_list_cons : disj_regions.

Ltac disj_regions :=
  once (typeclasses eauto with disj_regions).
