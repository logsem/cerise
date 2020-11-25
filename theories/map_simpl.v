From stdpp Require Import gmap.
From Equations Require Import Equations.

Section simpl_gmap.

  Variable K: Type.
  Hypothesis HeqdecK: EqDecision K.
  Hypothesis HcountK: Countable K.

  (* reified gmap *)
  Inductive rgmap {A M: Type}: Type :=
  | Ins (k: K) (a: A) (m: rgmap)
  | Del (k: K) (m: rgmap)
  | Symb (m: M).

  Fixpoint denote {A: Type} (rm: @rgmap A (gmap K A)): gmap K A :=
    match rm with
    | Ins k a rm => <[k := a]> (denote rm)
    | Del k rm => delete k (denote rm)
    | Symb m => m
    end.

  Fixpoint rlength {A M: Type} (rm: @rgmap A M): nat :=
    match rm with
    | Ins _ _ rm => S (rlength rm)
    | Del _ rm => S (rlength rm)
    | Symb m => O
    end.

  Fixpoint remove_key {A M: Type} (k: K) (rm: @rgmap A M) :=
    match rm with
    | Ins k' a rm => if decide (k = k') then remove_key k rm else Ins k' a (remove_key k rm)
    | Del k' rm => if decide (k = k') then remove_key k rm else Del k' (remove_key k rm)
    | Symb m => Symb m
    end.

  Lemma rlength_remove_key:
    forall A M k (rm: @rgmap A M), rlength (remove_key k rm) <= rlength rm.
  Proof.
    induction rm; simpl; auto.
    - destruct (decide (k = k0)); simpl; lia.
    - destruct (decide (k = k0)); simpl; lia.
  Qed.

  Equations simpl_rmap {A M: Type} (rm: @rgmap A M): @rgmap A M by wf (rlength rm) lt :=
    simpl_rmap (Ins k a rm) := Ins k a (simpl_rmap (remove_key k rm));
    simpl_rmap (Del k rm) := Del k (simpl_rmap (remove_key k rm));
    simpl_rmap (Symb m) := Symb m.
  Next Obligation.
    generalize (rlength_remove_key _ _ k rm). lia. Qed.
  Next Obligation.
    generalize (rlength_remove_key _ _ k rm). lia. Qed.

  Lemma denote_remove_key_ins:
    forall A (rm: @rgmap A (gmap K A)) k a,
      <[k:=a]> (denote rm) = <[k:=a]> (denote (remove_key k rm)).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite insert_insert. congruence.
      + simpl. rewrite insert_commute; auto.
        rewrite IHrm, insert_commute; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite insert_delete. congruence.
      + simpl. rewrite <- delete_insert_ne; auto.
        rewrite IHrm, delete_insert_ne; auto.
  Qed.

  Lemma denote_remove_key_del:
    forall A (rm: @rgmap A (gmap K A)) k,
      delete k (denote rm) = delete k (denote (remove_key k rm)).
  Proof.
    induction rm; simpl; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0. rewrite delete_insert_delete. congruence.
      + simpl. rewrite delete_insert_ne; auto.
        rewrite IHrm, <- delete_insert_ne; auto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite delete_idemp. congruence.
      + simpl. rewrite delete_commute; auto.
        rewrite IHrm, delete_commute; auto.
  Qed.

  Lemma simpl_rmap_correct':
    forall A n (rm: @rgmap A (gmap K A)),
      rlength rm <= n ->
      denote rm = denote (simpl_rmap rm).
  Proof.
    induction n; intros.
    - destruct rm; simpl in H; try lia.
      reflexivity.
    - destruct rm; [| | reflexivity].
      + rewrite simpl_rmap_equation_1; simpl.
        rewrite <- (IHn (remove_key k rm)).
        * apply denote_remove_key_ins.
        * generalize (rlength_remove_key _ _ k rm). simpl in H; lia.
      + rewrite simpl_rmap_equation_2; simpl.
        rewrite <- (IHn (remove_key k rm)).
        * apply denote_remove_key_del.
        * generalize (rlength_remove_key _ _ k rm). simpl in H; lia.
  Qed.

  Lemma simpl_rmap_correct:
    forall A (rm rm': @rgmap A (gmap K A)),
      simpl_rmap rm = rm' ->
      denote rm = denote rm'.
  Proof.
    intros. subst rm'. apply (simpl_rmap_correct' _ (rlength rm)); auto; lia.
  Qed.

End simpl_gmap.

From Ltac2 Require Import Ltac2 Option Constr.

Ltac2 rec reify_helper kk aa term :=
  lazy_match! term with
  | <[?k := ?a]> ?m => let (rm, h) := reify_helper kk aa m in
                      (constr:(@Ins $kk $aa (gmap $kk $aa) $k $a $rm), h)
  | delete ?k ?m => let (rm, h) := reify_helper kk aa m in
                   (constr:(@Del $kk $aa (gmap $kk $aa) $k $rm), h)
  | ?m => (* let id := Option.get (Ident.of_string "x") in *)
         (* let h := Fresh.in_goal id in *)
         (* remember $m as $h; *)
         (* let x := (Unsafe.make (Unsafe.Var (h))) in *)
         (constr:(@Symb $kk $aa (gmap $kk $aa) $m), m)
end.

Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs) (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).

(* Goal forall (m: gmap nat nat), (<[5 := 3]> m) = (<[5 := 3]> m). *)
(*   etransitivity. *)
(*   lazy_match! goal with *)
(*   | [|- ?x = _] => let (x', h) := reify_helper 'nat 'nat x in *)
(*                  replace_with x '(@denote _ _ _ _ $x') > [()| subst $h; reflexivity] *)
(*   end. *)

(*   lazy_match! goal with *)
(*   | [|- ?x = _] => let (x', h) := reify_helper 'nat 'nat x in *)
(*                  replace $x with  *)


(*                  let c' := Pattern.instantiate c '1 in *)
(*                              Message.print (Message.of_constr c') *)
(*                               (* apply (simpl_rmap_correct _ _ _ _ $x'); vm_compute; subst $h; reflexivity *) *)
(*   end. *)
(*   cbn [denote]. auto. *)
(* Qed. *)

Goal <[5 := 2]> (<[5 := 3]> (∅: gmap nat nat)) = <[5 := 2]> (∅: gmap nat nat).
  lazy_match! goal with
| [|- ?x = _] => let (x', m) := reify_helper 'nat 'nat x in
               Message.print (Message.of_constr x);
               Message.print (Message.of_constr x');
               replace_with x '(@denote _ _ _ _ $x') > [() | reflexivity];
               let id := Option.get (Ident.of_string "x") in
               let h := Fresh.in_goal id in
               remember $m as $h;
               erewrite (@simpl_rmap_correct) > [() | vm_compute; subst $h; reflexivity];
               cbn [denote]; subst $h
  end.
  reflexivity.
Qed.

Set Proof Mode "Classic".




