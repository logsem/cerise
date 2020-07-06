From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From cap_machine Require Import
     rules logrel fundamental region_invariants multiple_updates region_invariants_uninitialized.
From stdpp Require Import countable.

Definition std_rel_pub_decb (x y: region_type): bool :=
  match x with
  | Permanent => match y with
                | Permanent => true
                | _ => false
                end
  | Temporary => match y with
                | Temporary => true
                | _ => false
                end
  | Revoked => match y with
              | Temporary | Revoked => true
              | _ => false
              end
  | Static m => match y with
               | Temporary => true
               | Static m' => @bool_decide _ (gmap_eq_eq m m')
               | _ => false
               end
  end.

Lemma std_rel_pub_decb_spec x y:
  reflect (rtc std_rel_pub x y) (std_rel_pub_decb x y).
Proof.
  case_eq (std_rel_pub_decb x y); intros.
  - econstructor. destruct x, y; simpl in H; try congruence;
                    match goal with
                    | |- rtc std_rel_pub ?X ?X => left
                    | _ => idtac
                    end.
    + eapply rtc_once. econstructor.
    + eapply rtc_once. econstructor.
    + eapply bool_decide_eq_true_1 in H. subst g0.
      left.
  - econstructor; red; intro.
    destruct x, y; simpl in H; try congruence;
      match goal with
      | H: rtc std_rel_pub Temporary ?X |- _ => eapply std_rel_pub_rtc_Temporary in H; auto; discriminate
      | H: rtc std_rel_pub Permanent ?X |- _ => eapply std_rel_pub_rtc_Permanent in H; auto; discriminate
      | H: rtc std_rel_pub Revoked ?X |- _ => eapply std_rel_pub_rtc_Revoked in H; auto; destruct H; discriminate
      | H: rtc std_rel_pub (Static _) ?X |- _ => eapply std_rel_pub_rtc_Static in H; auto; destruct H; try discriminate
      | _ => idtac
      end.
    eapply bool_decide_eq_false_1 in H.
    eapply H. inv H0; auto.
Qed.

Definition related_sts_std_pub_decb {A: Type} {eqa: EqDecision A} {count: Countable A} (fstd gstd: STS_std_states A region_type): bool :=
  @bool_decide _ (gset_subseteq_dec (dom (gset A) fstd) (dom (gset A) gstd))
  &&
  map_fold
  (fun i x b => match gstd !! i with
             | Some y => std_rel_pub_decb x y && b
             | None => b
             end)
  true
  fstd.

Lemma fold_std_rel_pub_decb
      {A: Type} {eqa: EqDecision A} {count: Countable A}
      (fstd gstd: STS_std_states A region_type):
  map_fold
  (fun i x b => match gstd !! i with
             | Some y => std_rel_pub_decb x y && b
             | None => b
             end)
  true fstd = true <->
  (∀ (i : A) (x y : region_type),
      fstd !! i = Some x →
      gstd !! i = Some y →
      rtc std_rel_pub x y).
Proof.
  split.
  { intros X k a b A1 A2.
    generalize (map_fold_ind (fun (r: bool) fstd => map_fold
                                                (λ (i : A) (x : region_type) (b : bool),
                                                 match gstd !! i with
                                                 | Some y => std_rel_pub_decb x y && b
                                                 | None => b
                                                 end) true fstd = true
                                              → ∀ (i : A) (x y : region_type),
                                  fstd !! i = Some x
                                  → gstd !! i = Some y → rtc std_rel_pub x y)
                             (λ (i : A) (x : region_type) (b : bool),
                              match gstd !! i with
                              | Some y => std_rel_pub_decb x y && b
                              | None => b
                              end)
                             true). intros Y.
    eapply Y; eauto.
    - intros. rewrite lookup_empty in H0. inv H0.
    - intros. rewrite map_fold_insert_L in H1; auto.
      { destruct (eqa i i0).
        - subst i0. rewrite lookup_insert in H2. inv H2.
          rewrite H3 in H1. eapply andb_true_iff in H1.
          destruct H1.
          eapply (reflect_iff _ _ (std_rel_pub_decb_spec _ _)) in H1.
          auto.
        - rewrite lookup_insert_ne in H2; auto.
          eapply H0; eauto.
          destruct (gstd !! i); auto.
          eapply andb_true_iff in H1. destruct H1. auto. }
      { simpl; intros.
        destruct (gstd !! j1); destruct (gstd !! j2); auto.
        rewrite !andb_assoc.
        rewrite (andb_comm (std_rel_pub_decb z2 r1)). reflexivity. } }
  { generalize (map_fold_ind (fun (r: bool) fstd => (∀ (i : A) (x y : region_type),
     fstd !! i = Some x → gstd !! i = Some y → rtc std_rel_pub x y)
  → map_fold
      (λ (i : A) (x : region_type) (b : bool),
         match gstd !! i with
         | Some y => std_rel_pub_decb x y && b
         | None => b
         end) true fstd = true)
                             (λ (i : A) (x : region_type) (b : bool),
                              match gstd !! i with
                              | Some y => std_rel_pub_decb x y && b
                              | None => b
                              end)
                             true).
    intros Y. eapply Y; clear Y.
    - intros. rewrite map_fold_empty; auto.
    - intros. rewrite map_fold_insert_L.
      + case_eq (gstd !! i); intros.
        * eapply andb_true_iff; split.
          { eapply (reflect_iff _ _ (std_rel_pub_decb_spec _ _)).
            eapply H1; eauto.
            rewrite lookup_insert; auto. }
          { eapply H0. intros; eapply H1; eauto.
            destruct (eqa i i0).
            - subst i0; congruence.
            - rewrite lookup_insert_ne; auto. }
        * eapply H0. intros; eapply H1; eauto.
          destruct (eqa i i0).
          { subst i0; congruence. }
          { rewrite lookup_insert_ne; auto. }
      + simpl; intros.
        destruct (gstd !! j1); destruct (gstd !! j2); auto.
        rewrite !andb_assoc.
        rewrite (andb_comm (std_rel_pub_decb z2 r1)). reflexivity.
      + auto. }
Qed.

Lemma related_sts_std_pub_decb_spec
      {A: Type} {eqa: EqDecision A} {count: Countable A}
      (fstd gstd: STS_std_states A region_type):
  reflect (related_sts_std_pub fstd gstd) (related_sts_std_pub_decb fstd gstd).
Proof.
  case_eq (related_sts_std_pub_decb fstd gstd); rewrite /related_sts_std_pub_decb; intros.
  - eapply andb_true_iff in H; destruct H.
    eapply bool_decide_eq_true_1 in H.
    econstructor. split; auto.
    eapply fold_std_rel_pub_decb; eauto.
  - apply andb_false_iff in H. econstructor.
    destruct H as [H | H].
    + eapply bool_decide_eq_false_1 in H.
      red; intros. destruct H0. eapply H; eauto.
    + red; intros. destruct H0.
      eapply fold_std_rel_pub_decb in H1. congruence.
Qed.

Lemma imap_related_sts_pub_world
      {A: Type} {eqa: EqDecision A} {count: Countable A}
      W1 W2 f:
  std W2 = map_imap f (std W1) ->
  loc W2 = loc W1 ->
  (forall k a, exists b, f k a = Some b /\ rtc std_rel_pub a b) ->
  related_sts_pub_world W1 W2.
Proof.
  destruct W1, W2; simpl; intros; split; simpl.
  - subst o1. split.
    + red. red; intros.
      eapply elem_of_gmap_dom in H.
      eapply elem_of_gmap_dom.
      destruct H. rewrite map_lookup_imap H /=.
      destruct (H1 x x0) as [y0 [A0 A1] ]. rewrite A0.
      eauto.
    + intros. rewrite map_lookup_imap H /= in H2.
      destruct (H1 i x) as [y0 [A0 A1] ]. rewrite A0 in H2; inv H2.
      auto.
  - inv H0; eapply related_sts_pub_refl.
Qed.

Lemma map_imap_2
      {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
      {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, FinMapToList K A (M A)} 
      {EqDecision0 : EqDecision K} `{FinMap K M}:
  ∀ (A1 A2 B : Type) (f1 : K → A1 → option B) (f2 : K → A2 → option A1) (m : M A2),
  map_imap f1 (map_imap f2 m) = map_imap (fun k v => f2 k v ≫= f1 k) m.
Proof.
  intros. eapply map_eq. intros.
  rewrite !map_lookup_imap /=.
  destruct (m !! i); simpl; auto.
Qed.
  
Lemma std_update_multiple_imap W l ρ:
  (forall a, a ∈ l -> is_Some (std W !! a)) ->
  std_update_multiple W l ρ = (map_imap (fun k v => if decide (k ∈ l) then Some ρ else Some v)  (std W), loc W).
Proof.
  destruct W as [Wstd Wloc]. simpl.
  induction l.
  - simpl. rewrite map_imap_Some. reflexivity.
  - simpl. intros. rewrite IHl /std_update /=.
    + f_equal; auto.
      generalize (map_imap_insert (λ (k : Addr) (v : region_type), if decide (k ∈ l) then Some ρ else Some v) a ρ Wstd).
      replace (if decide (a ∈ l) then Some ρ else Some ρ) with (Some ρ) by (destruct (decide (a ∈ l)); auto). intros A.
      rewrite -A. eapply (map_imap_ext (λ (k : Addr) (v : region_type), if decide (k ∈ l) then Some ρ else Some v) (λ (k : Addr) (v : region_type), if decide (k ∈ a :: l) then Some ρ else Some v) (<[a:=ρ]> Wstd) Wstd).
      intros. destruct (addr_eq_dec a k).
      * subst k. rewrite lookup_insert /=.
        replace (if decide (a ∈ l) then Some ρ else Some ρ) with (Some ρ) by (destruct (decide (a ∈ l)); auto).
        destruct (decide (a ∈ a :: l)).
        { match goal with
          | |- _ = _ <$> ?X => case_eq X; intros; simpl; auto
          end.
          eapply H in e. destruct e. rewrite H1 in H0. inv H0. }
        { exfalso. eapply n. eapply elem_of_list_here. }
      * rewrite lookup_insert_ne; auto. f_equal.
        destruct (decide (k ∈ l)).
        { destruct (decide (k ∈ a :: l)); auto.
          exfalso. eapply n0. eapply elem_of_list_further. auto. }
        destruct (decide (k ∈ a :: l)); auto.
        { eapply elem_of_cons in e. exfalso. destruct e.
          - eapply n; auto.
          - eapply n0; auto. }
    + intros. eapply H. eapply elem_of_list_further. auto.
Qed.

Lemma revoke_imap W:
  revoke W = (map_imap (fun _ v => Some (revoke_i v)) (std W), loc W).
Proof.
  rewrite /revoke /revoke_std_sta. f_equal.
  apply (map_eq _ (map_imap (λ (_ : Addr) (v : region_type), Some (revoke_i v)) (std W))).
  intros. rewrite lookup_fmap map_lookup_imap /=.
  match goal with
  | |- _ = ?X ≫= _ => destruct X; simpl; auto
  end.
Qed.

Lemma override_uninitializedW_imap m W:
  dom (gset Addr) m ⊆ dom (gset Addr) (std W) ->
  override_uninitializedW m W = (map_imap (fun k v => match m !! k with Some w => Some (Static {[k:=w]}) | None => Some v end) (std W), loc W).
Proof.
  intros. rewrite /override_uninitializedW. f_equal.
  eapply (map_eq (override_uninitialized m (std W))).
  intros. rewrite map_lookup_imap /=. case_eq (m !! i); intros; simpl.
  - specialize (override_uninitializedW_lookup_some W _ _ _ H0) as A.
    rewrite A. match goal with
               | |- _ = ?X ≫= _ => case_eq X; intros; simpl; auto
               end.
    assert (is_Some (std W !! i)).
    { eapply elem_of_gmap_dom. eapply H. eapply elem_of_gmap_dom. eauto. }
    destruct H2; rewrite H2 in H1; inv H1.
  - specialize (override_uninitializedW_lookup_none W _ _ H0) as A.
    rewrite A /std. match goal with
                    | |- _ = ?X ≫= _ => case_eq X; intros; simpl; auto
                    end.
Qed.