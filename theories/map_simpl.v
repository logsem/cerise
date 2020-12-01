From stdpp Require Import gmap.
From Equations Require Import Equations.

Section simpl_gmap.

  Variable K: Type.
  Hypothesis HeqdecK: EqDecision K.
  Hypothesis HcountK: Countable K.

  (* reified gmap *)
  Inductive rgmap {A: Type}: Type :=
  | Ins (k: positive) (a: A) (m: rgmap)
  | Del (k: positive) (m: rgmap)
  | Symb.

  Fixpoint denote {A: Type} (rm: @rgmap A) (fm: positive -> option K) (m: gmap K A): gmap K A :=
    match rm with
    | Ins k a rm =>
      match fm k with
      | Some k => <[k := a]> (denote rm fm m)
      | None => denote rm fm m
      end
    | Del k rm =>
      match fm k with
      | Some k => delete k (denote rm fm m)
      | None => denote rm fm m
      end
    | Symb => m
    end.

  Fixpoint rlength {A: Type} (rm: @rgmap A): nat :=
    match rm with
    | Ins _ _ rm => S (rlength rm)
    | Del _ rm => S (rlength rm)
    | Symb => O
    end.

  Fixpoint remove_key {A: Type} k (rm: @rgmap A) :=
    match rm with
    | Ins k' a rm => if decide (k = k') then remove_key k rm else Ins k' a (remove_key k rm)
    | Del k' rm => if decide (k = k') then remove_key k rm else Del k' (remove_key k rm)
    | Symb => Symb
    end.

  Lemma rlength_remove_key:
    forall A k (rm: @rgmap A), rlength (remove_key k rm) <= rlength rm.
  Proof.
    induction rm; simpl; auto.
    - destruct (decide (k = k0)); simpl; lia.
    - destruct (decide (k = k0)); simpl; lia.
  Qed.

  Equations simpl_rmap {A: Type} (rm: @rgmap A): @rgmap A by wf (rlength rm) lt :=
    simpl_rmap (Ins k a rm) := Ins k a (simpl_rmap (remove_key k rm));
    simpl_rmap (Del k rm) := Del k (simpl_rmap (remove_key k rm));
    simpl_rmap (Symb) := Symb.
  Next Obligation.
    generalize (rlength_remove_key _ k rm). lia. Qed.
  Next Obligation.
    generalize (rlength_remove_key _ k rm). lia. Qed.

  Lemma denote_remove_key_ins:
    forall A fm (Hfm: forall n1 n2 k, fm n1 = Some k -> fm n2 = Some k -> n1 = n2) (rm: @rgmap A) k k' a (m: gmap K A),
      fm k = Some k' ->
      <[k':=a]> (denote rm fm m) = <[k':=a]> (denote (remove_key k rm) fm m).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H.
        rewrite insert_insert.
        eapply IHrm; eauto.
      + case_eq (fm k); intros.
        * assert (Hne: k1 <> k').
          { red; intros; subst k1. eapply n. eapply Hfm; eauto. }
          simpl. rewrite insert_commute; auto.
          rewrite H0.
          erewrite IHrm; eauto.
          rewrite insert_commute; eauto.
        * simpl. rewrite H0. eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite H. rewrite insert_delete. eapply IHrm; eauto.
      + simpl. case_eq (fm k); intros.
        * assert (Hne: k1 <> k').
          { red; intros; subst k1. eapply n. eapply Hfm; eauto. }
          erewrite <- delete_insert_ne; auto.
          erewrite IHrm, delete_insert_ne; eauto.
        * eauto.
  Qed.

  Lemma denote_remove_key_del:
    forall A fm (Hfm: forall n1 n2 k, fm n1 = Some k -> fm n2 = Some k -> n1 = n2) (rm: @rgmap A) k k' (m: gmap K A),
      fm k = Some k' ->
      delete k' (denote rm fm m) = delete k' (denote (remove_key k rm) fm m).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H. rewrite delete_insert_delete. eauto.
      + simpl. case_eq (fm k); intros.
        * assert (Hne: k1 <> k').
          { red; intros; subst k1. eapply n. eapply Hfm; eauto. }
          rewrite delete_insert_ne; auto.
          erewrite IHrm, <- delete_insert_ne; eauto.
        * eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite H, delete_idemp. eauto.
      + simpl. case_eq (fm k); intros.
        * assert (Hne: k1 <> k').
          { red; intros; subst k1. eapply n. eapply Hfm; eauto. }
          rewrite delete_commute; auto.
          erewrite IHrm, delete_commute; eauto.
        * eauto.
  Qed.

  Lemma denote_remove_key_none:
    forall A fm (rm: @rgmap A) k (m: gmap K A),
      fm k = None ->
      denote rm fm m = denote (remove_key k rm) fm m.
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H. auto.
      + simpl. destruct (fm k); auto.
        erewrite IHrm; eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H. auto.
      + simpl. destruct (fm k); auto.
        erewrite IHrm; eauto.
  Qed.

  Lemma simpl_rmap_correct':
    forall A fm (Hfm: forall n1 n2 k, fm n1 = Some k -> fm n2 = Some k -> n1 = n2) n (rm: @rgmap A) (m: gmap K A),
      rlength rm <= n ->
      denote rm fm m = denote (simpl_rmap rm) fm m.
  Proof.
    induction n; intros.
    - destruct rm; simpl in H; try lia.
      reflexivity.
    - destruct rm; [| | reflexivity].
      + rewrite simpl_rmap_equation_1; simpl.
        rewrite <- (IHn (remove_key k rm)).
        * case_eq (fm k); intros.
          { apply denote_remove_key_ins; auto. }
          { apply denote_remove_key_none; auto. }
        * generalize (rlength_remove_key _ k rm). simpl in H; lia.
      + rewrite simpl_rmap_equation_2; simpl.
        rewrite <- (IHn (remove_key k rm)).
        * case_eq (fm k); intros.
          { apply denote_remove_key_del; auto. }
          { apply denote_remove_key_none; auto. }
        * generalize (rlength_remove_key _ k rm). simpl in H; lia.
  Qed.

  Lemma simpl_rmap_correct:
    forall A fm (Hfm: forall n1 n2 k, fm n1 = Some k -> fm n2 = Some k -> n1 = n2) (rm rm': @rgmap A) (m: gmap K A),
      simpl_rmap rm = rm' ->
      denote rm fm m = denote rm' fm m.
  Proof.
    intros. subst rm'. apply (simpl_rmap_correct' _ fm Hfm (rlength rm)); auto; lia.
  Qed.

End simpl_gmap.

Definition add_key (K: Type) (encode: K -> positive) (fm: positive -> option K) (k: K) :=
  match fm (encode k) with
  | Some _ => fm
  | None => fun p => if positive_eq_dec p (encode k) then Some k else fm p
  end.

Lemma add_key_preserves_inj:
  forall K encode (fm: positive -> option K) k,
    (forall n1 n2 k', fm n1 = Some k' -> fm n2 = Some k' -> n1 = n2) ->
    (forall n k, fm n = Some k -> n = encode k) ->
    (forall n1 n2 k', add_key K encode fm k n1 = Some k' ->
                 add_key K encode fm k n2 = Some k' ->
                 n1 = n2) /\
    (forall n k', add_key K encode fm k n = Some k' -> n = encode k').
Proof.
  intros. split; intros.
  { unfold add_key in H1, H2.
    case_eq (fm (encode k)); intros.
    - rewrite H3 in H2, H1. eapply H; eauto.
    - rewrite H3 in H2, H1.
      destruct (positive_eq_dec n1 (encode k)).
      + inversion H1; clear H1. subst k'.
        destruct (positive_eq_dec n2 (encode k)).
        * congruence.
        * eapply H0 in H2. elim n; auto.
      + destruct (positive_eq_dec n2 (encode k)).
        * inversion H2; clear H2; subst k'.
          eapply H0 in H1. elim n; auto.
        * eapply H; eauto. }
  { unfold add_key in H1.
    case_eq (fm (encode k)); intros.
    - rewrite H2 in H1. eapply H0 in H1; auto.
    - rewrite H2 in H1. destruct (positive_eq_dec n (encode k)).
      + inversion H1; clear H1; subst k'. auto.
      + eapply H0; eauto. }
Qed.

Lemma empty_fm_inj:
  forall K,
    let fm := (fun (_: positive) => @None K) in
    forall n1 n2 k', fm n1 = Some k' -> fm n2 = Some k' -> n1 = n2.
Proof.
  simpl. intros. inversion H.
Qed.

Lemma empty_fm_encode:
  forall K encode,
    let fm := (fun (_: positive) => @None K) in
    forall n k, fm n = Some k -> n = encode k.
Proof.
  simpl; intros. inversion H.
Qed.

From Ltac2 Require Import Ltac2 Option Constr.

Ltac2 rec reify_helper kk aa term encode fm hfm1 hfm2 :=
  lazy_match! term with
  | <[?k := ?a]> ?m =>
    let fm' := '(add_key $kk $encode $fm $k) in
    let hfm1' := '(proj1 (add_key_preserves_inj $kk $encode $fm $k $hfm1 $hfm2)) in
    let hfm2' := '(proj2 (add_key_preserves_inj $kk $encode $fm $k $hfm1 $hfm2)) in
    let (rm, h, fm'', hfm'') := reify_helper kk aa m encode fm' hfm1' hfm2' in
    (constr:(@Ins $aa (encode $k) $a $rm), h, fm'', hfm'')
  | delete ?k ?m =>
    let fm' := '(add_key $kk $encode $fm $k) in
    let hfm1' := '(proj1 (add_key_preserves_inj $kk $encode $fm $k $hfm1 $hfm2)) in
    let hfm2' := '(proj2 (add_key_preserves_inj $kk $encode $fm $k $hfm1 $hfm2)) in
    let (rm, h, fm'', hfm'') := reify_helper kk aa m encode fm' hfm1' hfm2' in
    (constr:(@Del $aa (encode $k) $rm), h, fm'', hfm'')
  | ?m => (constr:(@Symb $aa), m, fm, hfm1)
end.

Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs) (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).

Goal <[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[6 := 3]> (∅: gmap nat nat)))))))) = <[5 := 2]> (<[6 := 3]> (∅: gmap nat nat)).
  lazy_match! goal with
  | [|- ?x = _] => let (x', m, fm, hfm) := reify_helper 'nat 'nat x 'encode '(fun (_: positive) => @None nat) '(empty_fm_inj nat) '(empty_fm_encode nat encode) in
                 replace_with x '(@denote _ _ _ _ $x' $fm $m) > [() | reflexivity];
                 erewrite (@simpl_rmap_correct nat _ _ nat $fm $hfm) > [() | vm_compute; reflexivity]
  end. simpl.
  reflexivity.
Qed.

Ltac2 map_simpl_aux k a x encode :=
  let (x', m, fm, hfm) := (reify_helper k a x encode '(fun (_: positive) => @None $k) '(empty_fm_inj $k) '(empty_fm_encode $k $encode)) in
  replace_with x '(@denote _ _ _ _ $x' $fm $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ $fm $hfm)) > [() | vm_compute; reflexivity];
  simpl.

Ltac2 map_simpl_aux_debug k a x encode :=
  let (x', m, fm, hfm) := (reify_helper k a x encode '(fun (_: positive) => @None $k) '(empty_fm_inj $k) '(empty_fm_encode $k $encode)) in
  replace_with x '(@denote _ _ _ _ $x' $fm $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ $fm $hfm)) > [() | time vm_compute; reflexivity];
  time simpl.

From iris.proofmode Require Import environments.

Set Default Proof Mode "Classic".

Ltac map_simpl name :=
  match goal with
  | |- context [ Esnoc _ (base.ident.INamed name) ([∗ map] _↦_ ∈ ?m, _)%I ] =>
    match type of m with
    | gmap ?K ?A =>
      let f := ltac2:(k a m encode |- map_simpl_aux (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) (Option.get (Ltac1.to_constr encode))) in
      f K A m (@encode K _ _)
    end
  end.

Ltac map_simpl_debug name :=
  match goal with
  | |- context [ Esnoc _ (base.ident.INamed name) ([∗ map] _↦_ ∈ ?m, _)%I ] =>
    match type of m with
    | gmap ?K ?A =>
      let f := ltac2:(k a m encode |- map_simpl_aux_debug (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) (Option.get (Ltac1.to_constr encode))) in
      f K A m (@encode K _ _)
    end
  end.

