From stdpp Require Import gmap.
From Equations Require Import Equations.

Section simpl_gmap.

  Variable K: Type.
  Hypothesis HeqdecK: EqDecision K.
  Hypothesis HcountK: Countable K.

  (* reified gmap *)
  Inductive rgmap {A: Type}: Type :=
  | Ins (k: nat) (a: A) (m: rgmap)
  | Del (k: nat) (m: rgmap)
  | Symb.

  Fixpoint denote {A: Type} (rm: @rgmap A) (fm: nat -> option K) (m: gmap K A): gmap K A :=
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
    forall A fm (rm: @rgmap A) k k' a (m: gmap K A),
      fm k = Some k' ->
      <[k':=a]> (denote rm fm m) = <[k':=a]> (denote (remove_key k rm) fm m).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H.
        rewrite insert_insert.
        eapply IHrm; eauto.
      + case_eq (fm k); intros.
        * cbn. destruct (decide (k1 = k')).
          { subst k1. rewrite insert_insert, H0.
            rewrite insert_insert.
            eapply IHrm. auto.
          }
          { simpl. rewrite insert_commute; auto.
            rewrite H0.
            erewrite IHrm; eauto.
            rewrite insert_commute; eauto. }
        * simpl. rewrite H0. eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite H. rewrite insert_delete. eapply IHrm; eauto.
      + simpl. case_eq (fm k); intros.
        * destruct (decide (k1 = k')).
          { subst k1. rewrite !insert_delete.
            eapply IHrm; eauto. }
          { erewrite <- delete_insert_ne; auto.
            erewrite IHrm, delete_insert_ne; eauto. }
        * eauto.
  Qed.

  Lemma denote_remove_key_del:
    forall A fm (rm: @rgmap A) k k' (m: gmap K A),
      fm k = Some k' ->
      delete k' (denote rm fm m) = delete k' (denote (remove_key k rm) fm m).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite H. rewrite delete_insert_delete. eauto.
      + simpl. case_eq (fm k); intros.
        * destruct (decide (k1 = k')).
          { subst k1. rewrite !delete_insert_delete.
            eapply IHrm; eauto. }
          { rewrite delete_insert_ne; auto.
            erewrite IHrm, <- delete_insert_ne; eauto. }
        * eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite H, delete_idemp. eauto.
      + simpl. case_eq (fm k); intros.
        * destruct (decide (k1 = k')).
          { subst k1. rewrite !delete_idemp.
            eapply IHrm; eauto. }
          { rewrite delete_commute; auto.
            erewrite IHrm, delete_commute; eauto. }
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
    forall A fm n (rm: @rgmap A) (m: gmap K A),
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
    forall A fm (rm rm': @rgmap A) (m: gmap K A),
      simpl_rmap rm = rm' ->
      denote rm fm m = denote rm' fm m.
  Proof.
    intros. subst rm'. apply (simpl_rmap_correct' _ fm (rlength rm)); auto; lia.
  Qed.

End simpl_gmap.

From Ltac2 Require Import Ltac2 Option Constr.

Ltac2 rec add_key (l: constr list) (k: constr) (n: constr) :=
  match l with
  | [] => (k::l, n)
  | c :: ll => match Constr.equal c k with
                | false => let (lll, nn) := add_key ll k '(S $n) in
                          ((c :: lll), nn)
                | _ => (l, n)
                end
  end.

Ltac2 rec make_list (l: constr list) :=
  match l with
  | [] => '[]
  | c :: ll => let k := make_list ll in
              '($c :: $k)
  end.

Ltac2 rec reify_helper kk aa term fm :=
  lazy_match! term with
  | <[?k := ?a]> ?m =>
    let (env, k') := add_key fm k 'O in
    let (rm, h, fm'') := reify_helper kk aa m env in
    (constr:(@Ins $aa $k' $a $rm), h, fm'')
  | delete ?k ?m =>
    let (env, k') := add_key fm k 'O in
    let (rm, h, fm'') := reify_helper kk aa m env in
    (constr:(@Del $aa $k' $rm), h, fm'')
  | ?m => (constr:(@Symb $aa), m, fm)
  end.

Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs) (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).

(* Debug test *)
(* Goal <[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[5 := 2]> (<[6 := 3]> (∅: gmap nat nat)))))))) = <[5 := 2]> (<[6 := 3]> (∅: gmap nat nat)). *)
(*   lazy_match! goal with *)
(*   | [|- ?x = _] => let (x', m, fm) := reify_helper 'nat 'nat x [] in *)
(*                  let env := make_list fm in *)
(*                  replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity]; *)
(*                  erewrite (@simpl_rmap_correct nat _ _ nat (fun n => @list_lookup _ n $env)) > [() | vm_compute; reflexivity] *)
(*   end. time (cbn [denote list_lookup lookup]). *)
(*   reflexivity. *)
(* Qed. *)

Ltac2 map_simpl_aux k a x encode :=
  let (x', m, fm) := (reify_helper k a x []) in
  let env := make_list fm in
  replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ (fun n => @list_lookup _ n $env))) > [() | vm_compute; reflexivity];
  cbn [denote list_lookup lookup].

Ltac2 map_simpl_aux_debug k a x encode :=
  let (x', m, fm) := (reify_helper k a x []) in
  let env := make_list fm in
  replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ (fun n => @list_lookup _ n $env))) > [() | vm_compute; reflexivity];
  time (cbn [denote list_lookup lookup]).

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
