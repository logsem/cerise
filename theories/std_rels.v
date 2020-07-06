From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From cap_machine Require Import
     rules logrel fundamental region_invariants.
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
