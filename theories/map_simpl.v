From stdpp Require Import gmap.
From cap_machine Require Import stdpp_extra.
From iris.proofmode Require Import proofmode.
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
          { subst k1. rewrite insert_insert H0.
            rewrite insert_insert.
            eapply IHrm. auto.
          }
          { simpl. rewrite insert_commute; auto.
            rewrite H0.
            erewrite IHrm; eauto.
            rewrite insert_commute; eauto. }
        * simpl. rewrite H0. eauto.
    - intros. destruct (decide (k0 = k)).
      + subst k0; rewrite H. rewrite insert_delete_insert. eapply IHrm; eauto.
      + simpl. case_eq (fm k); intros.
        * destruct (decide (k1 = k')).
          { subst k1. rewrite !insert_delete_insert.
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
      + subst k0; rewrite H delete_idemp. eauto.
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

Ltac2 rec make_list_from_unions h x :=
  match! x with
  | union ?a (singleton ?b) =>
    ltac1:(h b |- try (rewrite (delete_notin _ b); [|simplify_map_eq; rewrite -not_elem_of_dom h; set_solver; fail])) (Ltac1.of_constr h) (Ltac1.of_constr b);
    make_list_from_unions h a
  | singleton ?x => ltac1:(h x |- try (rewrite (delete_notin _ x); [|simplify_map_eq; rewrite -not_elem_of_dom h; set_solver+; fail])) (Ltac1.of_constr h) (Ltac1.of_constr x)
  end.

Ltac2 post_process k m :=
  ltac1:(k m |- match goal with
               | [h : dom (gset k) m = _ ∖ ?x |- _ ] =>
                 let f := ltac2:(h x |- make_list_from_unions (Option.get (Ltac1.to_constr h)) (Option.get (Ltac1.to_constr x)))
                 in f h x
               | _ => idtac
               end) (Ltac1.of_constr k) (Ltac1.of_constr m).


(* vm_compute does not work here, as it does to much calculation, so we come up with a more refined way of simplifying `simpl_rmap` expressions *)

(* Clear all hypothesis that do not explicitly feature in the goal, to avoid incorrect substitutions later. *)
Local Ltac clear_all :=
  repeat (match goal with
        | H : _ |- _ => clear H end ).

Definition boxed {A} (P: A): A := P.
Theorem boxed_eq `(P : A): (boxed P) = P. Proof. auto. Qed.
Local Ltac box_all := repeat (match goal with
      |  |- context [Ins ?k ?v] => lazymatch v with
                                 | boxed _ => fail | _ => let name := fresh "name" in remember v as name in * at 1; rewrite -{1}(boxed_eq name) end end).

Ltac simpl_rmap_compute :=
  clear_all; box_all; vm_compute simpl_rmap; subst.

Ltac2 map_simpl_aux k a x encode :=
  let (x', m, fm) := (reify_helper k a x []) in
  let env := make_list fm in
  replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ (fun n => @list_lookup _ n $env))) > [() | ltac1:(simpl_rmap_compute); reflexivity];
  cbn [denote list_lookup lookup];
  post_process k m.

Ltac2 map_simpl_aux_debug k a x encode :=
  let (x', m, fm) := (reify_helper k a x []) in
  let env := make_list fm in
  replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity];
  (erewrite (@simpl_rmap_correct _ _ _ _ (fun n => @list_lookup _ n $env))) > [() | ltac1:(simpl_rmap_compute); reflexivity];
  time (cbn [denote list_lookup lookup]);
  time (post_process k m).

From iris.proofmode Require Import environments.

Set Default Proof Mode "Classic".

Ltac map_simpl name :=
  match goal with
  | |- context [ Esnoc _ (base.ident.INamed name) ([∗ map] _↦_ ∈ ?m, _)%I ] =>
    match type of m with

    | ?t => match eval compute in t with (* type will not compute for very large maps *)
      | gmap ?K ?A =>
        let f := ltac2:(k a m encode |- map_simpl_aux (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) (Option.get (Ltac1.to_constr encode))) in
        f K A m (@encode K _ _)
      end
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

From iris.proofmode Require Import reduction proofmode.

Ltac disjunct_cases m i :=
  match m with
  | <[?k := _]> ?m' => destruct (decide (k = i)); disjunct_cases m' i
  | delete ?k ?m' => destruct (decide (k = i)); disjunct_cases m' i
  | _ => try subst i; try discriminate; simplify_map_eq; try reflexivity
  end.

Ltac solve_map_eq :=
  match goal with
  | |- ?m !! ?i = ?m' !! ?i => disjunct_cases m i
  end.

Ltac iFrameMapSolve' name :=
  lazymatch goal with
  | |- envs_entails ?H ([∗ map] _↦_ ∈ ?m, _)%I =>
    lazymatch pm_eval (envs_lookup name H) with
    | Some (_, ?X) =>
      lazymatch X with
      | ([∗ map] _↦_ ∈ ?m', _)%I =>
        match type of m' with
        | ?t => match eval compute in t with (* type will not compute for very large maps *)
          | gmap ?K ?A =>
            replace m' with m; [iFrame name| apply map_eq_iff; intros; solve_map_eq]
          end
        end
      | _ => idtac "The given hypothesis is not of the form ([∗ map] _↦_ ∈ _, _)"; idtac X
      end
    | _ => idtac "Can't find the given hypothesis"
    end
  | _ => idtac "The goal is not of the form ([∗ map] _↦_ ∈ _, _)"
  end.

Ltac iFrameMapSolve name :=
  map_simpl name; iFrameMapSolve' name.

Tactic Notation "iFrameMapSolve" "+" hyp_list(Hs) constr(name) := clear -Hs; iFrameMapSolve name.
