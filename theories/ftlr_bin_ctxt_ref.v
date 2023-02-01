From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Import linking logrel_binary.
From cap_machine Require Import stdpp_img iris_extra.
From cap_machine Require Import fundamental_binary.

Global Instance big_sepL_Permutation {PROP : bi} {A} (φ : A -> PROP):
  Proper ((≡ₚ) ==> (⊣⊢)) (fun l => ([∗ list] v ∈ l, φ v)%I).
Proof.
  intros l1 l2 Hp.
  induction Hp.
  - reflexivity.
  - rewrite !big_sepL_cons IHHp. reflexivity.
  - rewrite !big_sepL_cons. iSplit; iIntros "[H1 [H2 H3]]"; iFrame.
  - rewrite IHHp1 IHHp2. reflexivity.
Qed.

Lemma big_sepM_big_sepL_map_to_list {PROP:bi} {K A : Type} `{EqDecision K, Countable K}
(r : gmap K A) (φ : K → A → PROP) :
  ([∗ map] k↦y ∈ r, φ k y) ⊣⊢
  ([∗ list] x ∈ (map_to_list r), φ x.1 x.2).
Proof.
  apply (map_ind (fun r' => ([∗ map] k↦y ∈ r', φ k y) ⊣⊢ ([∗ list] x ∈ (map_to_list r'), φ x.1 x.2))).
  - rewrite map_to_list_empty big_sepL_nil big_sepM_empty. done.
  - intros k v m Hmk IH. rewrite map_to_list_insert.
    rewrite big_sepL_cons. rewrite big_sepM_insert. simpl.
    iSplit; iIntros "[Hφ Hl]"; iFrame; iApply IH; done.
    all: apply Hmk.
Qed.

Lemma big_sepM_big_sepL2_map_to_list {PROP : bi} {K A}
  `{EqDecision K, Countable K, LeibnizEquiv A}
  (φ : K -> A -> PROP) (m : gmap K A):
  ([∗ map] k↦v ∈ m, φ k v) ⊣⊢
  ([∗ list] k;v ∈ (map_to_list m).*1;(map_to_list m).*2, φ k v).
Proof.
  induction m using map_ind.
  - rewrite big_sepM_empty map_to_list_empty. simpl. reflexivity.
  - rewrite (big_sepM_insert _ _ _ _ H2) IHm !big_sepL2_alt !zip_fst_snd.
    specialize (map_to_list_insert m i x H2) as Hf.
    rewrite (big_sepL_Permutation _ _ _ Hf) !map_length.
    assert (Heq: ∀ b : nat, (⌜b = b⌝:PROP) ⊣⊢ True).
    intros b. iSplit; done.
    rewrite !Heq. simpl. iSplit; iIntros "[H1 [H2 H3]]"; iFrame.
Qed.

Lemma map_zip_dom {K A B M D} `{FinMapDom K M D} (m1 : M A) (m2: M B) :
  dom (map_zip m1 m2) ≡ dom m1 ∩ dom m2.
Proof.
  apply (anti_symm subseteq); intros k Hk.
  - rewrite elem_of_intersection !elem_of_dom.
    apply elem_of_dom in Hk as [ [v1 v2] Hk].
    rewrite map_lookup_zip_with in Hk.
    destruct (m1 !! k).
    split. auto. destruct (m2 !! k). auto.
    discriminate. discriminate.
  - rewrite elem_of_intersection !elem_of_dom in Hk.
    rewrite elem_of_dom.
    destruct Hk as [ [v1 Hm1] [v2 Hm2] ].
    exists (v1,v2). rewrite map_lookup_zip_with Hm1 Hm2.
    reflexivity.
Qed.

Lemma map_zip_dom_L {K A B M D} `{FinMapDom K M D} `{!LeibnizEquiv D} (m1 : M A) (m2: M B) :
  dom (map_zip m1 m2) = dom m1 ∩ dom m2.
Proof. unfold_leibniz. apply map_zip_dom. Qed.

(* Fixpoint unzip {A B: Type} (l: list (A * B)) := match l with
  | [] => ([], [])
  | (a,b) :: l =>
      (a:: ((unzip l).1), b::(unzip l).2)
  end.

Lemma unzip_spec {A B: Type} (l: list (A * B)) i a b:
  l !! i = Some (a,b) <->
    (unzip l).1 !! i = Some a /\ (unzip l).2 !! i = Some b.
Proof.
  revert i. induction l; intros i.
  - rewrite !lookup_nil. split.
    intro H. discriminate H.
    intros [H _]. discriminate.
  - destruct i; destruct a0 as [c d]; simpl.
    split; intros H. apply Some_inj, pair_equal_spec in H as [H1 H2].
    simplify_eq. auto.
    destruct H as [H1 H2]. apply Some_inj in H1, H2.
    simplify_eq. reflexivity.
    apply IHl.
Qed. *)


(* Definition map_to_list_pair {K A M:Type} {F:FinMapToList K A M} (m:M) :=
  unzip (map_to_list m). *)

Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          {MP:MachineParameters}.

  Context {Symbols:Type}.
  Context {Symbols_eq_dec: EqDecision Symbols}.
  Context {Symbols_countable: Countable Symbols}.

  Infix "##ₗ" := (can_link can_address_only) (at level 70).

  (** Lifting the interp binary value relation from words to components
      This implies dom (exports y) ⊆ dom (exports x) *)
  Definition interp_exports (x y: component Symbols) : iProp Σ :=
    [∗ map] s ↦ wy ∈ exports y,
        match exports x !! s with
        | None => False (* values exported by y must also be exported by x *)
        | Some wx =>
          (* ([∗ map] a ↦ w ∈ segment x, a ↦ₐ w) ∗
          ([∗ map] a ↦ w ∈ segment y, a ↣ₐ w) -∗ *)
            interp (wx, wy)
        end.


  (** An induction on a component's exports map *)
  Lemma exports_ind (P: component Symbols -> Prop) c :
    P {| segment := segment c; imports := imports c; exports := ∅ |} ->
    (∀ s w exp,
      exports c !! s = Some w ->
      exp !! s = None ->
      exp ⊆ exports c ->
      P {| segment := segment c; imports := imports c; exports := exp |} ->
      P {| segment := segment c; imports := imports c; exports := <[s := w]> exp |}
    ) ->
    P c.
  Proof.
    intros Hinit Hind.
    destruct c as [s i e]. simpl in *.
    apply (map_ind (fun exp =>
      exp ⊆ e -> P {| segment := s; imports := i; exports := exp |}
    )).
    intros _. apply Hinit.
    intros s' w exp Hexp Hi Hsubset.
    assert (Hs: exp ⊆ e).
    { apply map_subseteq_spec. intros j x Hj. rewrite map_subseteq_spec in Hsubset.
      destruct (decide (s'=j)) as [Heq|Heq]. simplify_eq.
      apply Hsubset. rewrite (lookup_insert_ne _ _ _ _ Heq).
      apply Hj. }
    apply Hind.
    rewrite map_subseteq_spec in Hsubset. apply Hsubset. apply lookup_insert.
    apply Hexp. apply Hs.
    apply (Hi Hs). reflexivity.
  Qed.


  (* Lemma map_zip_empty_l {K M A B} `{H:FinMap K M} (m: M B):
    map_zip (∅: M A) m = ∅.
  Proof.
    unfold map_zip_with. rewrite merge_empty_l.
    apply map_eq. intros i. rewrite lookup_empty lookup_omap.
    destruct (m !! i); reflexivity.
  Qed. *)

  (*Lemma map_zip_insert_l {K M A B} `{H:FinMap K M} (m1: M A) (m2: M B) k v1:
    map_zip (<[ k := v1 ]> m1) m2 = match m2 !! k with
    | None => map_zip m1 m2
    | Some v2 => <[ k := pair v1 v2 ]> (map_zip m1 m2)
    end.
  Proof.
    apply map_eq. intros i.
    destruct (m2 !! k) eqn:Hm2.
    destruct (decide (k = i)) as [Hk | Hk]. rewrite Hk. rewrite Hk in Hm2.
    rewrite map_lookup_zip_with !lookup_insert Hm2. reflexivity.
    rewrite map_lookup_zip_with !(lookup_insert_ne _ _ _ _ Hk) map_lookup_zip_with.
    reflexivity.
    destruct (decide (k = i)) as [Hk | Hk]. rewrite Hk. rewrite Hk in Hm2.
    rewrite !map_lookup_zip_with !lookup_insert Hm2. destruct (m1 !! i); reflexivity.
    rewrite map_lookup_zip_with !(lookup_insert_ne _ _ _ _ Hk) map_lookup_zip_with.
    reflexivity.
  Qed.

  Lemma map_zip_insert_r {K M A B} `{H:FinMap K M} (m1: M A) (m2: M B) k v2:
    map_zip m1 (<[ k := v2 ]> m2) = match m1 !! k with
    | None => map_zip m1 m2
    | Some v1 => <[ k := pair v1 v2 ]> (map_zip m1 m2)
    end.
  Proof.
    apply map_eq. intros i.
    destruct (m1 !! k) eqn:Hm1.
    destruct (decide (k = i)) as [Hk | Hk]. rewrite Hk. rewrite Hk in Hm1.
    rewrite map_lookup_zip_with !lookup_insert Hm1. reflexivity.
    rewrite map_lookup_zip_with !(lookup_insert_ne _ _ _ _ Hk) map_lookup_zip_with.
    reflexivity.
    destruct (decide (k = i)) as [Hk | Hk]. rewrite Hk. rewrite Hk in Hm1.
    rewrite !map_lookup_zip_with !lookup_insert Hm1. destruct (m1 !! i); reflexivity.
    rewrite map_lookup_zip_with !(lookup_insert_ne _ _ _ _ Hk) map_lookup_zip_with.
    reflexivity.
  Qed.

  Lemma map_zip_filter_r {K M A B} `{H:FinMap K M} (m1: M A) (m2: M B) :
    map_zip m1 m2 = map_zip m1 (filter (fun '(k,_) => is_Some (m1 !! k)) m2).
  Proof.
    apply map_eq. intros k.
    rewrite !map_lookup_zip_with.
    destruct (m1 !! k) as [v1|] eqn:Hm1;
    destruct (m2 !! k) as [v2|] eqn:Hm2; simpl.
    - rewrite (map_filter_lookup_Some_2 _ _ _ _ Hm2). reflexivity.
      apply mk_is_Some in Hm1. apply Hm1.
    - rewrite (map_filter_lookup_None_2 _ _ _ (or_introl Hm2)). reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.*)

  Lemma map_zip_filter {K M A B} `{H:FinMap K M} (m1: M A) (m2: M B) :
    map_zip m1 m2 =
    map_zip
      (filter (fun '(k,_) => is_Some (m2 !! k)) m1)
      (filter (fun '(k,_) => is_Some (m1 !! k)) m2).
  Proof.
    apply map_eq. intros k.
    rewrite !map_lookup_zip_with.
    destruct (m1 !! k) as [v1|] eqn:Hm1;
    destruct (m2 !! k) as [v2|] eqn:Hm2; simpl.
    - rewrite (map_filter_lookup_Some_2 _ _ _ _ Hm2 (mk_is_Some _ _ Hm1)).
      rewrite (map_filter_lookup_Some_2 _ _ _ _ Hm1 (mk_is_Some _ _ Hm2)).
      reflexivity.
    - rewrite eq_None_not_Some in Hm2.
      rewrite (map_filter_lookup_None_2 _ _ _ (or_intror (fun _ _ => Hm2))).
      reflexivity.
    - rewrite (map_filter_lookup_None_2 _ _ _ (or_introl Hm1)). reflexivity.
    - rewrite eq_None_not_Some in Hm2.
      rewrite (map_filter_lookup_None_2 _ _ _ (or_intror (fun _ _ => Hm2))).
      reflexivity.
  Qed.

  (*(** Induction on the zip of two maps at once *)
  Lemma map_zip_ind {K M A B} `{H:FinMap K M} (P: M (A * B)%type -> Prop) :
    P ∅ ->
    (∀ m1 m2 i v,
      m1 !! i = None ->
      m2 !! i = None ->
      P (map_zip m1 m2) -> P (<[i := v]> (map_zip m1 m2))) ->
    ∀ m1 m2, P (map_zip m1 m2).
  Proof.
    intros HP0 HPind. intros m1 m2.
    rewrite map_zip_filter_l.
    induction m1 using map_ind.
    - rewrite map_zip_empty_l. apply HP0.
    - rewrite -map_zip_filter_l map_zip_insert_l map_zip_filter_l.
      destruct (m2 !! i) as [y|] eqn:Hm2.
      apply HPind. assumption. apply map_filter_lookup_None_2.
      right. intros _ _. rewrite H7. apply is_Some_None.
      all: apply IHm1.
  Qed.

  (** Strong induction on the zip of two maps at once *)
  Lemma map_zip_strong_ind {K M A B} `{H:FinMap K M} (P: M (A * B)%type -> Prop) m1 m2 :
    P ∅ ->
    (∀ m1' m2' i v1 v2,
      m1 !! i = Some v1 ->
      m2 !! i = Some v2 ->
      m1' !! i = None ->
      m2' !! i = None ->
      P (map_zip m1' m2') -> P (<[i := pair v1 v2]> (map_zip m1' m2'))) ->
    P (map_zip m1 m2).
  Proof.
    intros HP0 HPind.
    assert (HI:∀ m, map_zip m m2 ⊆ map_zip m1 m2 -> P (map_zip m m2)). intros m.
    apply map_zip_ind. intros _. apply HP0.
    intros m1' m2' i [v1 v2] Hm1' Hm2' Hind Hsubset.
    rewrite map_subseteq_spec in Hsubset.
    assert (H': map_zip m1 m2 !! i = Some (v1, v2)).
    { apply Hsubset. apply lookup_insert. }
    apply HPind.
    1,2: rewrite map_lookup_zip_with in H';
         destruct (m1 !! i); destruct (m2 !! i); simpl in H';
         discriminate || apply Some_inj, pair_equal_spec in H' as [H'1 H'2];
         simplify_eq; reflexivity.
    assumption. assumption.
    apply Hind. rewrite map_subseteq_spec. intros k x Hk.
    apply Hsubset.
    destruct (decide (i=k)) as [Heq|Heq].
    rewrite Heq in Hm1', Hm2'.
    rewrite map_lookup_zip_with Hm1' Hm2' in Hk. discriminate.
    rewrite (lookup_insert_ne _ _ _ _ Heq). exact Hk.
    apply HI. reflexivity.
  Qed. *)

  (** Induction on a pair of maps *)
  Lemma map_ind2 {K M A B} `{H:FinMap K M} (P: M A -> M B -> Prop) m1 m2 :
    P ∅ ∅ ->
    (∀ m1' m2' i,
      m1' !! i = None ->
      m2' !! i = None ->
      P m1' m2' ->
      match m1 !! i, m2 !! i with
      | None, None => True
      | Some v1, None => P (<[i:=v1]> m1') m2'
      | None, Some v2 => P m1' (<[i:=v2]> m2')
      | Some v1, Some v2 => P (<[i:=v1]> m1') (<[i:=v2]> m2')
      end) ->
    P m1 m2.
  Proof.
    intros HP0 HPind.
    assert (HPm1 : ∀ m, m ⊆ m1 -> P m (filter (fun '(k,_) => is_Some (m !! k)) m2)).
    { induction m using map_ind.
      - assert (Hempt: filter (λ '(k, _), is_Some ((∅: M A) !! k)) m2 = ∅).
        apply map_eq. intros i. rewrite lookup_empty map_filter_lookup_None lookup_empty.
        right. intros _ _. apply is_Some_None.
        rewrite Hempt. auto.
      - specialize (HPind m (filter (fun '(k,_) => is_Some (m !! k)) m2) i H7).
        intros Hsubset. assert (Hm1 : m1 !! i = Some x).
        rewrite map_subseteq_spec in Hsubset. apply Hsubset. apply lookup_insert.
        rewrite Hm1 in HPind.
        assert (Hinf: m ⊆ m1).
        rewrite map_subseteq_spec. intros j y Hjy.
        rewrite map_subseteq_spec in Hsubset. apply Hsubset.
        destruct (decide (i=j)) as [Heq|Heq]. simplify_eq.
        rewrite (lookup_insert_ne _ _ _ _ Heq). assumption.
        assert (Hf: filter (λ '(k, _), is_Some (m !! k)) m2 !! i = None).
        rewrite map_filter_lookup_None H7. right. intros _ _. apply is_Some_None.
        specialize (HPind Hf (IHm Hinf)).
        destruct (m2 !! i) as [y|] eqn:Hm2.
        + replace (filter (λ '(k, _), is_Some (<[i:=x]> m !! k)) m2) with (<[i:=y]> (filter (λ '(k, _), is_Some (m !! k)) m2)).
          apply HPind. apply map_eq. intros j.
          destruct (decide (i=j)) as [Heq|Heq]. rewrite Heq lookup_insert.
          symmetry. rewrite map_filter_lookup_Some. split. simplify_eq. assumption.
          rewrite lookup_insert. exists x. reflexivity.
          rewrite (lookup_insert_ne _ _ _ _ Heq).
          destruct (filter (λ '(k, _), is_Some (m !! k)) m2 !! j) eqn:Heq'; symmetry.
          apply map_filter_lookup_Some. apply map_filter_lookup_Some in Heq' as [Hl Hr].
          split. exact Hl. rewrite (lookup_insert_ne _ _ _ _ Heq). exact Hr.
          apply map_filter_lookup_None. apply map_filter_lookup_None in Heq' as [Hl | Hr].
          left. exact Hl. right. intros z Hz. rewrite (lookup_insert_ne _ _ _ _ Heq). apply (Hr z Hz).
        + replace (filter (λ '(k, _), is_Some (<[i:=x]> m !! k)) m2) with (filter (λ '(k, _), is_Some (m !! k)) m2).
          apply HPind.
          rewrite -map_filter_ext.
          intros j y Hjy.
          rewrite lookup_insert_ne. reflexivity.
          intros Hij. simplify_eq.
    }
    assert (HPm2: ∀ m, (filter (λ '(k, _), is_Some (m1 !! k)) m2) ##ₘ m
            -> m ⊆ m2 -> P m1 ((filter (λ '(k, _), is_Some (m1 !! k)) m2) ∪ m)).
    { intros m. induction m using map_ind.
      - intros Hdisj Hsup.
        rewrite map_union_empty. apply HPm1. reflexivity.
      - intros Hdisj Hsup.
        assert (Hm2 : m2 !! i = Some x).
        rewrite map_subseteq_spec in Hsup. apply Hsup. apply lookup_insert.
        destruct (m1 !! i) eqn:Hm1.
        rewrite map_disjoint_spec in Hdisj. exfalso.
        apply (Hdisj i x x).
        apply map_filter_lookup_Some_2. assumption. exists a. assumption.
        apply lookup_insert.
        assert (Hf: filter (λ '(k, _), is_Some (m1 !! k)) m2 !! i = None).
        apply map_filter_lookup_None_2. right. intros _ _. rewrite Hm1. apply is_Some_None.
        rewrite -(insert_union_r _ _ _ _ Hf).
        specialize (HPind m1 ((filter (λ '(k, _), is_Some (m1 !! k)) m2) ∪ m) i Hm1).
        rewrite Hm1 Hm2 in HPind.
        apply HPind.
        rewrite lookup_union_None. split; assumption.
        apply IHm.
        rewrite map_disjoint_spec. intros j y z Hjy Hjz.
        rewrite map_disjoint_spec in Hdisj. apply (Hdisj j y z Hjy).
        destruct (decide (i=j)) as [Heq|Heq]. simplify_eq.
        rewrite (lookup_insert_ne _ _ _ _ Heq). assumption.
        rewrite map_subseteq_spec. intros j y Hjy.
        rewrite map_subseteq_spec in Hsup. apply Hsup.
        destruct (decide (i=j)) as [Heq|Heq]. simplify_eq.
        rewrite (lookup_insert_ne _ _ _ _ Heq). assumption.
    }
    rewrite -(map_filter_union_complement (λ '(k, _), is_Some (m1 !! k)) m2).
    apply HPm2.
    apply map_disjoint_filter_complement. apply map_filter_subseteq.
  Qed.

  Lemma big_sepM_sep_zip_affine {PROP:bi} {K A B} `{EqDecision K, Countable K}
    (Φ: K -> A -> PROP) (Ψ: K -> B -> PROP)
    `{∀ k a, Affine (Φ k a), ∀ k b, Affine (Ψ k b)}
    m1 m2 :
    ([∗ map] a ↦ w ∈ m1, Φ a w) ∗
    ([∗ map] a ↦ w ∈ m2, Ψ a w) -∗
    [∗ map] a ↦ w ∈ map_zip m1 m2,
      (⌜ m1 !! a = Some w.1 ⌝ ∗ Φ a w.1) ∗
      (⌜ m2 !! a = Some w.2 ⌝ ∗ Ψ a w.2).
  Proof.
    iIntros "[Hm1 Hm2]".
    rewrite map_zip_filter.
    rewrite (big_sepM_sep_zip (fun a v => ⌜m1!!a = Some v⌝ ∗ Φ a v)%I (fun a v => ⌜m2!!a = Some v⌝ ∗ Ψ a v)%I).
    rewrite !big_sepM_sep.
    iSplitL "Hm1"; iSplitR.
    1,3: iApply big_sepM_intro; iModIntro; iIntros (k x) "%Hk"; iPureIntro;
         rewrite map_filter_lookup_Some in Hk; destruct Hk as [Hk _]; apply Hk.
    iApply (big_sepM_subseteq _ m1). apply map_filter_subseteq. done.
    iApply (big_sepM_subseteq _ m2). apply map_filter_subseteq. done.
    intros k. split;
    intros [x Hx]; rewrite map_filter_lookup_Some in Hx;
    destruct Hx as [Hx [y Hy] ]; exists y;
    rewrite map_filter_lookup_Some; split; exact Hy || exists x; exact Hx.
  Qed.



  (* Lemma big_sepM_zip_to_big_sepL2 {PROP : bi} {K A B}
    `{EqDecision K, Countable K, LeibnizEquiv A, LeibnizEquiv B}
    (φ : K -> A -> B -> PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k↦v ∈ map_zip m1 m2, φ k v.1 v.2) ⊣⊢
    ([∗ list] k;v ∈ (map_to_list (map_zip m1 m2)).*1;(map_to_list (map_zip m1 m2)).*2, φ k v.1 v.2).
  Proof.
    apply (map_zip_ind (fun m =>
    ([∗ map] k↦v ∈ m, φ k v.1 v.2) ⊣⊢
    ([∗ list] k;v ∈ (map_to_list m).*1;(map_to_list m).*2, φ k v.1 v.2))).
    - rewrite big_sepM_empty map_to_list_empty. simpl. reflexivity.
    - intros m1' m2' i [v1 v2] Hm1' Hm2' IH.
      assert (Hzip: map_zip m1' m2' !! i = None).
      rewrite map_lookup_zip_with Hm1' Hm2'. reflexivity.
      rewrite (big_sepM_insert _ _ _ _ Hzip) IH !big_sepL2_alt !zip_fst_snd.
      specialize (map_to_list_insert (map_zip m1' m2') i (pair v1 v2) Hzip) as Hf.
      rewrite (big_sepL_Permutation _ _ _ Hf) !map_length.
      assert (Heq: ∀ b : nat, (⌜b = b⌝:PROP) ⊣⊢ True).
      intros b. iSplit; done.
      rewrite !Heq. simpl. iSplit; iIntros "[H1 [H2 H3]]"; iFrame.
  Qed. *)

  (** Allocates invariants for segment c in links (x ⋈ c) and (y ⋈ c)
      assuming the exports of x and y are valid. *)
  Lemma interp_exports_inv_alloc E {x y c: component Symbols} :
    (∀ w, w ∈ img (segment c) -> no_capability w (dom (segment c))) ->
    x ##ₗ c -> y ##ₗ c ->
    dom (exports x) ⊆ dom (exports y) ->
    ([∗ map] a ↦ w ∈ segment (x ⋈ c), a ↦ₐ w) ∗
    ([∗ map] a ↦ w ∈ segment (y ⋈ c), a ↣ₐ w) ∗
    interp_exports x y ={E}=∗
      ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
        ⌜a ∈ dom (segment c)⌝ →
          inv (logN.@a)
          (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hexp) "[Hpx [Hpy #Hexp]]".
    rewrite -(big_sepM_filter (fun '(a,_) => a ∈ _)).
    rewrite (big_sepM_big_sepL2_map_to_list (fun a _ => inv _ _)).
    iApply region_inv_alloc.
    rewrite -(big_sepM_big_sepL2_map_to_list (fun a v => (a ↦ₐ v.1 ∗ a ↣ₐ v.2 ∗ interp v)%I)).
    rewrite big_sepM_filter.
    iApply (big_sepM_mono (fun a w =>
      interp_exports x y ∗
      (⌜ segment (x ⋈ c) !! a = Some w.1 ⌝ ∗ a ↦ₐ w.1) ∗
      (⌜ segment (y ⋈ c) !! a = Some w.2 ⌝ ∗ a ↣ₐ w.2))%I).
    iIntros (a [w w'] Hzip) "[#Hexp [[%Hxca Hw] [%Hyca Hw']]] %Ha".
    simpl. iFrame.
    (* assert validity of w,w' by case disjunction *)
    rewrite (link_segment_lookup_r _ Hsep1 Ha) in Hxca.
    rewrite (link_segment_lookup_r _ Hsep2 Ha) in Hyca.
    rewrite !resolve_imports_spec /= in Hxca, Hyca.
    destruct (imports c !! a) as [s|] eqn:Hic.
    destruct (exports y !! s) as [wy|] eqn:Hey;
    destruct (exports x !! s) as [wx|] eqn:Hex.
    apply Some_inj in Hxca, Hyca.
    (* if they are exports from x,y, validity comes from the hypothese *)
    1,2: iPoseProof (big_sepM_lookup _ _ _ _ Hey with "Hexp") as "H".
    rewrite Hex Hxca Hyca. iApply "H".
    rewrite Hex. done.
    apply mk_is_Some, elem_of_dom in Hex.
    apply not_elem_of_dom in Hey.
    contradiction (Hey (Hexp _ Hex)).
    (* else we know they are only words, and thus valid *)
    1,2: rewrite Hxca in Hyca; apply Some_inj in Hyca; rewrite -Hyca.
    1,2: apply elem_of_img_rev in Hxca; apply Hno_caps in Hxca.
    1,2: destruct w; try contradiction Hxca.
    1,2: rewrite fixpoint_interp1_eq; done.

    rewrite (big_sepM_sep (fun _ _ => interp_exports x y)).
    iSplitR.
    iApply big_sepM_dup. iModIntro. iIntros "H".
    iFrame. done. done.
    iApply (big_sepM_sep_zip_affine
      (fun a v => a ↦ₐ v)%I
      (fun a v => a ↣ₐ v)%I).
    iFrame.

    Unshelve. apply TCOr_l. unfold Affine.
    iIntros (j z) "#H". done.
  Qed.



  Lemma interp_link {x y c:component Symbols}:
    (∀ w, w ∈ img (segment c) -> no_capability w (dom (segment c))) ->
    x ##ₗ c -> y ##ₗ c ->
    imports x = ∅ -> imports y = ∅ ->
    spec_ctx ∗ interp_exports x y ∗
    ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
    ⌜a ∈ dom (segment c)⌝ →
      inv (logN.@a)
      (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))) -∗
    interp_exports (x ⋈ c) (y ⋈ c).
  Proof.
    iIntros (Hno_caps Hsep1 Hsep2 Hno_imps_x Hno_imps_y) "[#Hspec [#Hexp #Hinv]]".
    (* weird induction scheme: essentially an induction on the exports of c
       but keeping our persistent hypotheses out of the induction *)
    apply (exports_ind (fun c' => envs_entails
    (Envs
    (Esnoc _ "Hinv"
       ([∗ map] a ↦ _ ∈ map_zip (segment (x ⋈ c)) (segment (y ⋈ c)),
        ⌜a ∈ dom (segment c)⌝ →
         inv _
         (∃ w w' : Word, a ↦ₐ w ∗ a ↣ₐ w' ∗ interp (w, w'))))
    _ _)
    _)%I c).
    (* For exports from x,y this is a direct result of our hypothese *)
    - iApply big_sepM_intro. iModIntro.
      rewrite /= !map_union_empty. iIntros (s w) "%Hey".
      iPoseProof (big_sepM_lookup _ _ _ _ Hey with "Hexp") as "H'".
      destruct (exports x !! s); done.
    (* For exports of c we need to do a bit of work.
       First, prove they are indeed exports of c and not x or y *)
    - iIntros (s w exp Hec Hexp Hexp_sub IH).
      inversion Hsep1. inversion Hsep2.
      destruct (exports y !! s) as [ey|] eqn:Hey.
      rewrite map_disjoint_dom in Hexp_disj0.
      apply mk_is_Some, elem_of_dom in Hec, Hey.
      contradiction (Hexp_disj0 _ Hey Hec).
      destruct (exports x !! s) as [ex|] eqn:Hex.
      rewrite map_disjoint_dom in Hexp_disj.
      apply mk_is_Some, elem_of_dom in Hec, Hex.
      contradiction (Hexp_disj _ Hex Hec).
      unfold interp_exports. iSimpl.
      replace (exports y ∪ <[s:=w]> exp) with (<[s:=w]> (exports y ∪ exp)).
      iApply big_sepM_insert. apply lookup_union_None. split; assumption.
      iSplitR.
      (* Now use the invariants to prove the validity of these exports *)
      + rewrite (lookup_union_r _ _ _ Hex) lookup_insert.
        rewrite fixpoint_interp1_eq.
        destruct w. done.
        destruct p. done.
        all: iSplitR; try done.
        (* Use fundamental theorem to change interp_expr into interp *)
        4: iIntros (r); do 2 iModIntro; iApply fundamental_binary;
           done || rewrite fixpoint_interp1_eq; iSimpl; iSplitR; try done.
        (* add the hypothese a ∈ dom (segment c) which we need to access our invariants *)
        all: iApply (big_sepL_mono (fun _ a => ⌜a ∈ dom (segment c)⌝ -∗ _)%I).
        1,3,5,7,9:
          iIntros (k y' Hk) "Hl"; iApply "Hl"; iPureIntro;
          inversion Hwf_r;
          apply (Hwr_exp _ (elem_of_img_rev _ _ _ Hec)), elem_of_finz_seq_between, elem_of_list_lookup;
          exists k; apply Hk.
        all: induction (finz.seq_between b e);
             try (iApply big_sepL_nil; done).
        all: iApply big_sepL_cons; iSplitR; try apply IHl.
        all: iIntros "%Ha"; iExists interp.
        all: iSplitL.
        (* read_cond and write_cond boil down to interp -> interp,
           so they are trivial *)
        4,10: iSplitL.
        2,4,5,6,7,9,11: iSimpl; do 2 iModIntro; iIntros (ww ww') "H"; done.
        (* others results come from the invariants *)
        all: assert (Ha': a0 ∈ dom (map_zip (segment (x ⋈ c)) (segment (y ⋈ c)))).
        1,3,5,7,9:
          rewrite map_zip_dom_L !(resolve_imports_link_dom can_address_only);
          (rewrite !dom_union_L -union_intersection_r_L; apply (union_subseteq_r _ _ a0 Ha))
          || solve_can_link.
        all: apply elem_of_dom in Ha' as [z Ha'].
        all: iPoseProof (big_sepM_lookup _ _ a0 _ Ha' with "Hinv") as "Ha0".
        all: iApply "Ha0"; iPureIntro; exact Ha.
      + unfold interp_exports in IH. simpl in IH.
        iApply (big_sepM_mono (fun k wy =>
          interp_exports x y ∗ match (exports x ∪ exp) !! k with
            | Some wx => interp (wx, wy)
            | None => False%I
          end)%I (fun k wy =>
          match (exports x ∪ <[s:=w]> exp) !! k with
            | Some wx => interp (wx, wy)
            | None => False%I
          end) (exports y ∪ exp)).
        iIntros (s' wy Hwy) "[#Hexp #H]".
        apply lookup_union_Some_raw in Hwy as [Hwy | [Hwy Hexp_y] ].
        iPoseProof (big_sepM_lookup _ _ _ _ Hwy with "Hexp") as "H'".
        destruct (exports x !! s') eqn:Hx.
        rewrite !(lookup_union_Some_l _ _ _ _ Hx). done. done.
        destruct (exports x !! s') eqn:Hx.
        rewrite map_subseteq_spec in Hexp_sub.
        rewrite map_disjoint_spec in Hexp_disj.
        contradiction (Hexp_disj s' _ _ Hx (Hexp_sub s' _ Hexp_y)).
        destruct (decide (s=s')) as [Heq|Heq].
        rewrite Heq in Hexp. rewrite Hexp in Hexp_y. discriminate.
        rewrite !(lookup_union_r _ _ _ Hx).
        rewrite (lookup_insert_ne _ _ _ _ Heq). done.
        iApply big_sepM_sep. iSplitR.
        iApply big_sepM_intro. iModIntro. iIntros (k x0) "_". done.
        apply IH.
      + apply insert_union_r. assumption.

    Unshelve. all: apply TCOr_l; unfold Affine;
    iIntros (j t) "#H"; done.
  Qed.
    as "H".
       unfold interp_exports in IH. simpl in IH.

        all: apply elem_of_dom in Ha' as [z Ha']; apply Ha'.
        rewrite !dom_union_L -union_intersection_r_L.
        apply (union_subseteq_r _ _ a0 Ha).
        Search ((_ ∪ _) ∩ _).
        Search "map_zip". _dom
        apply mk_is_Some.
        rewrite map_lookup_zip_with.


      4: iSimpl. inter iApply fundamental_binary. spec_ctx


      iSplitR. done.

    iApply fupd

    2: apply IH.
    set_solver.
    iApply big_sepM_map_to_list.
    induction (map_to_list (exports (y ⋈ c))) eqn:Heq. done.
    iApply big_sepL_cons. iSplitR.
    destruct a as [s w].
    Search "big_sepL".

    (* intros s. unfold Plain.
    destruct (exports (y ⋈ c) !! s);
    destruct (exports (x ⋈ c) !! s).

    apply uPred_plainly.
    Search BiPlainly.
    unfold plainly, bi_plainly_plainly.
    Print Plainly.
    apply (interp_plainly (o0, o)).
    Print Persistent.
    admit.
    iModIntro. done. done. done. done. simpl. *)
    (* assert (
    Proper (bi_entails ==> flip impl)
    (environments.envs_entails
      {|
        environments.env_intuitionistic := environments.Enil;
        environments.env_spatial :=
          environments.Esnoc
            (environments.Esnoc
              (environments.Esnoc environments.Enil
              "Hpx" ([∗ map] a↦w ∈ segment (x ⋈ c), a ↦ₐ w))
              "Hpy" ([∗ map] a↦w ∈ segment (y ⋈ c), a ↣ₐ w))
              "Hxy" (interp_exports x y);
        environments.env_counter := 1%positive
      |})
    ).
    intros P Q PQ. unfold flip, impl. admit.
    Search (_ ={_}=∗ ∀ _, _).
    rewrite -fupd_plainly_forall_2.
    big_sepL_fupd
    Search (_ ={_}=∗ ∀ _, _). Print Plain. *)
    (* iSpecialize ("Hxy" $! a). *)
    assert (Hyc: exports (y ⋈ c) !! s = Some w).
    { apply elem_of_map_to_list. rewrite Heq.
      apply elem_of_cons. left. reflexivity. }
    apply lookup_union_Some_raw in Hyc as [Hey | [Hey Hec] ].
    destruct (exports c !! s) as [ec|] eqn:Hec.
    rewrite map_disjoint_dom in Hexp_disj0.
    apply mk_is_Some, elem_of_dom in Hec, Hey.
    contradiction (Hexp_disj0 _ Hey Hec).

    iPoseProof (big_sepM_lookup _ _ _ _ Hey with "Hxy") as "H'".
    rewrite (lookup_union_l _ _ _ Hec).
    destruct (exports x !! s); done.

    destruct (exports x !! s) as [ex|] eqn:Hex.
    rewrite map_disjoint_dom in Hexp_disj.
    apply mk_is_Some, elem_of_dom in Hec, Hex.
    contradiction (Hexp_disj _ Hex Hec).
    rewrite (lookup_union_r _ _ _ Hex) Hec. simpl.
    admit.
    apply IHl.

    rewrite fixpoint_interp1_eq.
    destruct ec. done.
    destruct p; simpl. done.
    iApply fupd_frame_l. iSplit. done.
    iApply (big_sepL_mono (fun _ a => ∃ w w',
      ⌜segment (x ⋈ c) !! a = Some w /\
      segment (y ⋈ c) !! a = Some w'⌝ ∗ a ↦ₐ w ∗ a ↣ₐ w')%I).
    iIntros (k a' Ha') "Hw".
    iDestruct "Hw" as (w w') "[[%Hw %Hw'] [Haw Haw']]".
    iExists interp. iSplit.
    2: {
      iNext. iIntros (w0 w0'). iModIntro.
      iIntros "Hinterp". iApply "Hinterp".
    }
    Search "fupd".
    iApply (inv_alloc).
    iApply inv_alloc.
     [w [w' Hw] ].
    iAssert ([∗ list] a0 ∈ finz.seq_between b e, )
    (* iPoseProof (big_sepM_map_to_list with "Hpx") as "H". *)

    big_sepL_mono big_sepL_forall
    big_sepL_elem_of
    big_sepL_cons. iIntros (a0).
    Search big_opL.
    iSplit. iPureIntro. reflexivity. auto.  done.

    (s) "Hs".
    Search (_ ={_}=∗ (big_opM _ _ _)).
  Definition interp_imports := _.

  Definition interp_resolve_imports (x y: component Symbols) : iProp Σ :=
    interp_imports -∗ interp_exports
    (* ∀ i_x i_y, (* Symbols -> Word *)
      ⌜ img (imports x) ⊆ dom i_x /\ img (imports y) ⊆ dom i_y ⌝ ∗
      [∗ set] s ∈ (dom i_x ∩ dom i_y), interp (i_x !!! s, i_y !!! s) ∗
      interp_closed_program
        (x ⋈ {| segment := ∅; imports := ∅; exports := i_x|})
        (y ⋈ {| segment := ∅; imports := ∅; exports := i_y|}). *)



End logrel.
