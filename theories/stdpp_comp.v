
(** Composition of finite maps *)
From Coq Require Import ssreflect.
From stdpp Require Import fin_maps fin_map_dom.
From cap_machine Require Import stdpp_img.

Definition map_compose {A B C MA MB} `{FA:FinMap A MA, FB:FinMap B MB}
  (m : MB C) (n : MA B) := omap (m !!.) n.

Lemma omap_dom_subseteq `{FinMapDom K M D} {A B} (f : A → option B) (m : M A) :
  dom (omap f m) ⊆ dom m.
Proof.
  intros a. rewrite !elem_of_dom.
  intros [c Hm].
  apply lookup_omap_Some in Hm as [b [_ Hm]].
  exists b. done.
Qed.
Lemma omap_filter_subseteq `{FinMap K M} {A B} (f : A → option B)
  (P : K*A → Prop) `{∀ x, Decision (P x)} (m : M A) :
  omap f (filter P m) ⊆ omap f m.
Proof. apply map_omap_mono. apply map_filter_subseteq. Qed.

Section compose.
  Context {A MA B MB} `{FA:FinMap A MA} `{FB:FinMap B MB}.
  Context {C : Type}.
  Implicit Types (m : MB C) (n : MA B) (a : A) (b : B) (c : C).

  Lemma map_compose_lookup m n a :
    map_compose m n !! a = n !! a ≫= λ b, m !! b.
  Proof. apply lookup_omap. Qed.

  Lemma map_compose_lookup_Some m n a c :
    map_compose m n !! a = Some c ↔
    ∃ b, n !! a = Some b /\ m !! b = Some c.
  Proof.
    rewrite map_compose_lookup.
    destruct (n !! a) as [b|] eqn:Hm; simpl.
    - split.
      + intros Hn. exists b. done.
      + intros (b' & Hb' & Hn). apply (inj Some) in Hb'.
        rewrite Hb'. done.
    - split; [|intros [b [Hf _]]]; done.
  Qed.
  Lemma map_compose_lookup_Some_2 m n a b c :
    n !! a = Some b → m !! b = Some c →
    map_compose m n !! a = Some c.
  Proof. intros Hn Hm. apply map_compose_lookup_Some. by exists b. Qed.

  Lemma map_compose_lookup_None m n a :
    map_compose m n !! a = None ↔
    n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None.
  Proof.
    rewrite map_compose_lookup.
    destruct (n!!a) as [b|] eqn:Hn; simpl.
    - split.
      + intros Hm. right. by exists b.
      + intros [Hm | [b' [Hb' Hm]]]; [discriminate|].
        apply (inj Some) in Hb'. by rewrite Hb'.
    - split.
      + intros Hm. by left.
      + done.
  Qed.
  Lemma map_compose_lookup_None_2l m n a :
    n !! a = None → map_compose m n !! a = None.
  Proof. intros Hn. apply map_compose_lookup_None. by left. Qed.
  Lemma map_compose_lookup_None_2r m n a b :
    n !! a = Some b → m !! b = None → map_compose m n !! a = None.
  Proof. intros Hn Hm. apply map_compose_lookup_None. right. by exists b. Qed.

  Lemma map_compose_dom_subseteq `{∀ A : Type, Dom (MA A) D, Set_ A D, !FinMapDom A MA D} m n :
    dom (map_compose m n) ⊆ dom n.
  Proof. apply omap_dom_subseteq. Qed.

  Lemma map_compose_img_subseteq
    `{FinSet C D} m n :
    map_img (map_compose m n) ⊆@{D} map_img m.
  Proof.
    intros c. rewrite !elem_of_map_img. intros [a Ha].
    apply map_compose_lookup_Some in Ha as [b [_ Hb]]. by exists b.
  Qed.

  Lemma map_compose_empty_r m : map_compose m ∅ = (∅ : MA C).
  Proof. apply omap_empty. Qed.
  Lemma map_compose_empty_l n : map_compose (∅ : MB C) n = (∅ : MA C).
  Proof.
    apply map_eq. intros k. rewrite map_compose_lookup lookup_empty.
    destruct (n!!k); simpl; [apply lookup_empty|reflexivity].
  Qed.

  Lemma map_compose_union_l m1 m2 n :
    map_compose (m1 ∪ m2) n = map_compose m1 n ∪ map_compose m2 n.
  Proof.
    apply map_eq. intros a. rewrite lookup_omap.
    destruct (n!!a) as [b|] eqn:Hn; simpl.
    destruct (m1!!b) as [c|] eqn:Hm1.
    rewrite (lookup_union_Some_l _ _ _ c Hm1). symmetry.
    apply lookup_union_Some_l. apply map_compose_lookup_Some. by exists b.
    rewrite (lookup_union_r _ _ _ Hm1). symmetry.
    rewrite lookup_union_r. by apply (map_compose_lookup_None_2r m1 n a b).
    rewrite map_compose_lookup Hn. reflexivity.
    symmetry. rewrite lookup_union_None.
    split; by apply map_compose_lookup_None_2l.
  Qed.
  Lemma map_compose_union_r m n1 n2 :
    n1 ##ₘ n2 -> map_compose m (n1 ∪ n2) = map_compose m n1 ∪ map_compose m n2.
  Proof. intros Hs. by apply map_omap_union. Qed.

  #[global] Instance map_compose_mono_l n : Proper ((⊆) ==> (⊆)) (λ m, map_compose m n).
  Proof.
    intros m1 m2 Hinf. apply map_subseteq_spec. intros a c Ha.
    apply map_compose_lookup_Some. apply map_compose_lookup_Some in Ha as [b [Hn Hm]].
    exists b. split. done. rewrite map_subseteq_spec in Hinf. by apply Hinf.
  Qed.
  #[global] Instance map_compose_mono_r m : Proper ((⊆@{MA B}) ==> (⊆)) (map_compose m).
  Proof.
    intros n1 n2 Hinf. apply map_subseteq_spec. intros a c Ha.
    apply map_compose_lookup_Some. apply map_compose_lookup_Some in Ha as [b [Hn Hm]].
    exists b. split. rewrite map_subseteq_spec in Hinf. by apply Hinf. done.
  Qed.
  #[global] Instance map_compose_mono : Proper ((⊆@{MB C}) ==> (⊆@{MA B}) ==> (⊆)) map_compose.
  Proof.
    intros m1 m2 Hm n1 n2 Hn.
    transitivity (map_compose m1 n2).
    by apply map_compose_mono_r. by apply map_compose_mono_l.
  Qed.

  Lemma map_compose_filter_subseteq_l (P : B*C → Prop) `{∀ x, Decision (P x)} m n :
    map_compose (filter P m) n ⊆ map_compose m n.
  Proof. apply map_compose_mono_l. apply map_filter_subseteq. Qed.
  Lemma map_compose_filter_subseteq_r (P : A*B → Prop) `{∀ x, Decision (P x)} m n :
    map_compose m (filter P n) ⊆ map_compose m n.
  Proof. apply omap_filter_subseteq. Qed.

  Lemma map_compose_min_l `{FinSet B D, !RelDecision (∈@{D})} m n :
    map_compose m n = map_compose (filter (λ '(b,_), b ∈ map_img (SA:=D) n) m) n.
  Proof.
    apply map_eq. intro a. rewrite !map_compose_lookup.
    destruct (n!!a) eqn:Hn; simpl.
    - destruct (m!!b) eqn:Hm; symmetry. apply map_filter_lookup_Some.
      split. done. rewrite elem_of_map_img. by exists a.
      apply map_filter_lookup_None. by left.
    - done.
  Qed.
  Lemma map_compose_min_r `{FinSet B D, ∀ C : Type, Dom (MB C) D, !FinMapDom B MB D, !RelDecision (∈@{D})} m n :
    map_compose (FB:=FB) m n = map_compose (FB:=FB) m (filter (λ '(_,b), b ∈ dom m) n).
  Proof.
    apply map_eq. intro a. rewrite !map_compose_lookup.
    destruct (n!!a) eqn:Hn; simpl.
    - destruct (m!!b) eqn:Hm; symmetry.
      apply bind_Some. exists b. split.
      apply map_filter_lookup_Some. by rewrite elem_of_dom. done.
      apply bind_None. left. apply map_filter_lookup_None. right.
      intros x Hx. rewrite not_elem_of_dom. by simplify_eq.
    - symmetry. apply bind_None. left. apply map_filter_lookup_None. by left.
  Qed.

  Lemma map_compose_disjoint m1 m2 n :
    m1 ##ₘ m2 -> map_compose m1 n ##ₘ map_compose m2 n.
  Proof.
    intros Hdisj.
    rewrite map_disjoint_spec. intros a c1 c2 Ha1 Ha2.
    rewrite map_disjoint_spec in Hdisj.
    rewrite !map_compose_lookup in Ha1, Ha2.
    destruct (n!!a). simpl in Ha1, Ha2. apply (Hdisj _ _ _ Ha1 Ha2).
    simpl in Ha1. discriminate.
  Qed.

  (** Alternative definition of [map_compose m n] by induction on [n] *)
  Lemma map_compose_alt m n :
    map_compose m n = map_fold (λ a b (mn: MA C), match m !! b with
      | Some c => <[a:=c]> mn
      | None => mn end) ∅ n.
  Proof.
    apply (map_fold_ind (λ (mn : MA C) n, omap (m !!.) n = mn)).
    - apply map_compose_empty_r.
    - intros k b n' mn Hn' IH. rewrite omap_insert -IH.
      destruct (m!!b). reflexivity.
      apply delete_notin. by apply map_compose_lookup_None_2l.
  Qed.
End compose.
