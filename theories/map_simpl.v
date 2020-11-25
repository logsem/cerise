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
  | ?m => (constr:(@Symb $kk $aa (gmap $kk $aa) $m), m)
end.

Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs) (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).

Goal <[5 := 2]> (<[5 := 3]> (∅: gmap nat nat)) = <[5 := 2]> (∅: gmap nat nat).
  lazy_match! goal with
  | [|- ?x = _] => let (x', m) := reify_helper 'nat 'nat x in
                 replace_with x '(@denote _ _ _ _ $x') > [() | reflexivity];
                 let id := Option.get (Ident.of_string "x") in
                 let h := Fresh.in_goal id in
                 remember $m as $h;
                 erewrite (@simpl_rmap_correct) > [() | vm_compute; subst $h; reflexivity];
                 cbn [denote]; subst $h
  end.
  reflexivity.
Qed.

Ltac2 map_simpl_aux k a x :=
  let (x', m) := reify_helper k a x in
  Message.print (Message.of_constr k);
  Message.print (Message.of_constr a);
  Message.print (Message.of_constr x);
  Message.print (Message.of_constr x');
  Message.print (Message.of_constr '(@denote _ _ _ _ $x'));
  replace_with x '(@denote _ _ _ _ $x') > [() | reflexivity];
  let id := Option.get (Ident.of_string "x") in
  let h := Fresh.in_goal id in
  remember $m as $h;
  erewrite (simpl_rmap_correct) > [() | vm_compute; subst $h; reflexivity];
  cbn [denote]; subst $h.

From iris.proofmode Require Import environments.

Set Default Proof Mode "Classic".

Ltac map_simpl name :=
  match goal with
  | |- context [ Esnoc _ (base.ident.INamed name) ([∗ map] _↦_ ∈ ?m, _)%I ] =>
    match type of m with
    | gmap ?K ?A =>
      let f := ltac2:(k a m |- map_simpl_aux (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m))) in
      f K A m
    end
  end.

From iris.proofmode Require Import tactics.
From cap_machine Require Import rules_base addr_reg_sample.

Section test.
  Context `{memG Σ, regG Σ}.

  Lemma bar (w1 w2 w3: Word):
    (denote RegName reg_eq_dec reg_countable
            (Ins RegName r_t1 w1 (Ins RegName r_t2 w2 (Ins RegName r_t1 w3 (Symb RegName ∅))))) = denote RegName reg_eq_dec reg_countable
    (Ins RegName (R 1 eq_refl) w2 (Ins RegName (R 2 eq_refl) w1 (Symb RegName ∅))).
  Proof.
    remember ∅ as HX.
    erewrite simpl_rmap_correct.
    2:{ vm_compute. subst HX. reflexivity. }
    subst HX. reflexivity.
    Fail Qed.
  Admitted.

  Lemma foo (w1 w2 w3: Word) :
    ([∗ map] k↦y ∈ (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    iIntros "H".
    map_simpl "H".
    iDestruct (regs_of_map_2 with "H") as "H"; auto.
  Admitted.

End test.
