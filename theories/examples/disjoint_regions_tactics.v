From iris.proofmode Require Import tactics.
From stdpp Require Import sets list.
From cap_machine Require Import addr_reg region.

Lemma disjoint_mono_l A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Y ## Z → X ## Z.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Lemma disjoint_mono_r A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Z ## Y → Z ## X.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Definition ByReflexivity (P: Prop) :=
  P.
Hint Extern 1 (ByReflexivity _) => reflexivity : disj_regions.

Definition AddrRegionRange (l: list Addr) (b e: Addr) :=
  ∀ a, a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionRange_singleton a :
  ByReflexivity (eqb_addr a top = false) →
  AddrRegionRange [a] a (^(a+1))%a.
Proof.
  unfold eqb_addr. unfold ByReflexivity. cbn. intros ?%Z.eqb_neq.
  intros a' ->%elem_of_list_singleton. solve_addr.
Qed.
Hint Resolve AddrRegionRange_singleton : disj_regions.

Lemma AddrRegionRange_region_addrs b e :
  AddrRegionRange (region_addrs b e) b e.
Proof.
  intros a ?%elem_of_region_addrs. solve_addr.
Qed.
Hint Resolve AddrRegionRange_region_addrs : disj_regions.

Definition AddrRegionsRange (ll: list (list Addr)) (b e: Addr) :=
  ∀ l a, l ∈ ll → a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionsRange_single l b e :
  AddrRegionRange l b e →
  AddrRegionsRange [l] b e.
Proof.
  intros Hl l' a ->%elem_of_list_singleton ?%Hl. solve_addr.
Qed.
Hint Resolve 1 AddrRegionsRange_single : disj_regions.

Lemma AddrRegionsRange_cons l ll b e b' e' :
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  AddrRegionsRange (l :: ll) (min b b') (max e e').
Proof.
  intros Hl Hll l' a [->|H]%elem_of_cons.
  - intros ?%Hl. solve_addr.
  - intros ?%Hll; auto. solve_addr.
Qed.
Hint Resolve 10 AddrRegionsRange_cons : disj_regions.

Instance Empty_list {A}: Empty (list A). exact []. Defined.
Instance Union_list {A}: Union (list A). exact app. Defined.
Instance Singleton_list {A}: Singleton A (list A). exact (λ a, [a]). Defined.

Lemma addr_range_union_incl_range (ll: list (list Addr)) (b e: Addr):
  AddrRegionsRange ll b e →
  ⋃ ll ⊆ region_addrs b e.
Proof.
  revert b e. induction ll as [| l ll].
  - intros. cbn. unfold subseteq, list_subseteq. unfold empty, Empty_list.
    inversion 1.
  - intros b e HInd. cbn. unfold union, Union_list, subseteq, list_subseteq.
    intros x. intros [Hx|Hx]%elem_of_app.
    + specialize (HInd l x ltac:(constructor) Hx). apply elem_of_region_addrs.
      solve_addr.
    + assert (HI: AddrRegionsRange ll b e).
      { intros ? ? ? ?. eapply HInd. apply elem_of_list_further; eassumption.
        auto. }
      specialize (IHll _ _ HI).
      rewrite elem_of_subseteq in IHll |- * => IHll.
      by apply IHll.
Qed.

Lemma AddrRegionRange_iff_incl_region_addrs l b e :
  AddrRegionRange l b e ↔ (l ⊆ region_addrs b e).
Proof.
  unfold AddrRegionRange, subseteq, list_subseteq.
  split.
  - intros H **. rewrite elem_of_region_addrs. by apply H.
  - intros H **. rewrite -elem_of_region_addrs. by apply H.
Qed.

Lemma addr_range_disj_union_empty (l: list Addr) :
  l ## ⋃ [].
Proof.
  cbn. unfold empty, Empty_list, disjoint_list, disjoint.
  unfold set_disjoint. intros * ? ?%elem_of_nil. auto.
Qed.
Hint Resolve 1 addr_range_disj_union_empty : disj_regions.

Lemma addr_range_disj_range_union (l: list Addr) ll b e b' e':
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  ByReflexivity ((e <=? b') || (e' <=? b) = true)%a →
  l ## ⋃ ll.
Proof.
  intros Hl Hll. unfold ByReflexivity.
  rewrite orb_true_iff /leb_addr !Z.leb_le.
  intros.
  rewrite AddrRegionRange_iff_incl_region_addrs in Hl |- * => Hl.
  eapply disjoint_mono_l; eauto.
  eapply disjoint_mono_r. eapply addr_range_union_incl_range; eauto.
  unfold disjoint, disjoint_list, set_disjoint.
  intro. rewrite !elem_of_region_addrs. solve_addr.
Qed.
Hint Resolve 10 addr_range_disj_range_union : disj_regions.

Lemma addr_disjoint_list_empty : ## ([]: list (list Addr)).
Proof. constructor. Qed.
Hint Resolve addr_disjoint_list_empty : disj_regions.

Lemma addr_disjoint_list_cons (l: list Addr) ll :
  l ## ⋃ ll →
  ## ll →
  ## (l :: ll).
Proof. intros. rewrite disjoint_list_cons; auto. Qed.
Hint Resolve addr_disjoint_list_cons : disj_regions.

Ltac disj_regions :=
  once (typeclasses eauto with disj_regions).
