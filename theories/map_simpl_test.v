From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules_base addr_reg_sample map_simpl.

Section test.
  Context `{memG Σ, regG Σ}.

  Lemma foo rmap:
    ([∗ map] k↦y ∈ <[r_t3:=WInt 0%Z]>
     (<[r_t2:=WInt 0%Z]>
      (<[r_t4:=WInt 0%Z]>
       (<[r_t5:=WInt 0%Z]> (delete r_t5 (<[r_t2:=WInt 0%Z]> (delete r_t3 (delete r_t1 rmap))))))),
     k ↦ᵣ y) -∗ ⌜True⌝.
  Proof.
    iIntros "H".
    map_simpl "H".
  Abort.

  Lemma foo (w1 w2 w3: Word) :
    ([∗ map] k↦y ∈ delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    iIntros "H".
    map_simpl "H".
  Abort.

  Lemma stuck pc_p pc_b pc_e a_first:
    ([∗ map] k↦y ∈  (<[r_t8:= WCap pc_p pc_b pc_e (a_first ^+ 0)%a]>
                                                 ∅),
            k ↦ᵣ y) -∗ ⌜ True ⌝.
  Proof. iIntros "Ht".
         (* map_simpl_debug "Ht". *)
  Abort.
End test.

(* Unfortunately, we cannot generate Hreg, since Iris hypothesis names are strings, and coq does not allow us to convert identifiers to strings without Iris plugin *)
 Ltac extract_pointsto_map_old regs Hmap rname Hrdom Hreg :=
    let rval := fresh "v"rname in
    let Hsome := fresh "Hsome" in
    let str_destr := constr:(("[" ++ Hreg ++ " " ++ Hmap ++ "]")%string) in
    assert (is_Some (regs !! rname)) as [rval Hsome] by (apply Hrdom; repeat constructor);
    iDestruct (big_sepM_delete _ _ rname with Hmap) as str_destr; first by simplify_map_eq.

  Ltac solve_insert_dom :=
  rewrite -(not_elem_of_dom (D := (gset RegName)));
  match goal with
  | [ H : dom (gset RegName) _ = _ |- _ ] =>
    rewrite H end;
  set_solver+.

  Ltac insert_pointsto_map_dom Hmap Hreg:=
    let str_destr := constr:(("[ $" ++ Hmap ++ " $" ++ Hreg ++ "]")%string) in
    iDestruct (big_sepM_insert with str_destr) as Hmap;
    [(repeat rewrite lookup_insert_ne //;[]); solve_insert_dom | ].

  Ltac insert_pointsto_map_del Hmap Hreg :=
    let str_destr := constr:(("[ $" ++ Hmap ++ " $" ++ Hreg ++ "]")%string) in
    iDestruct (big_sepM_insert with str_destr) as Hmap;
    [by simplify_map_eq | repeat (rewrite -delete_insert_ne //;[]); try rewrite insert_delete_insert].
  (* TODO: more elegantly merge the previous 2 tactics, i.e. not using first but actually inspecting the goal, or at least factor out the common iDestruct *)
   Ltac insert_pointsto_map Hmap Hreg :=
     first [insert_pointsto_map_del Hmap Hreg | insert_pointsto_map_dom Hmap Hreg].

Section tacs.
   Variable K: Type.
   Hypothesis HeqdecK: EqDecision K.
   Hypothesis HcountK: Countable K.

   (* if map_simpl is called first, the below will not contain overhead *)
   Fixpoint denote_domain {A : Type} (rm: @rgmap A) (fm: nat -> option K) (mdom : gset K): gset K :=
      match rm with
      | Ins k a rm =>
        match fm k with
        | Some k => {[k]} ∪ denote_domain rm fm mdom
        | None => denote_domain rm fm mdom end
      | Del k rm =>
        match fm k with
        | Some k => denote_domain rm fm mdom ∖ {[k]}
        | None => denote_domain rm fm mdom end
      | Symb => mdom
      end.

   Local Arguments denote {_ _ _ _} _ _ _.
   Lemma denote_domain_correct {A : Type} (rm: @rgmap A) (fm: nat -> option K) (m : gmap K A) (mdom : gset K) : dom (gset K) m = mdom → dom (gset K) (denote rm fm m) = denote_domain rm fm mdom.
     intro Hmdom.
     induction rm; cbn [denote denote_domain].
     - case_eq (fm k); intros; set_solver + IHrm.
     - case_eq (fm k); intros; set_solver + IHrm.
     - done.
   Qed.
End tacs.

Arguments denote_domain {_ _ _ _} _ _ _.
Arguments denote {_ _ _ _} _ _ _.
From Ltac2 Require Import Ltac2 Control Fresh.
Set Default Proof Mode "Classic".
Section tests.

  Context `{memG Σ, regG Σ}.

  Search "dom" "empty".

  Ltac2 get_map_dom_hyp k a m hdom :=
    let (x', m, fm) := (reify_helper k a m []) in
    let env := make_list fm in
    pose (@denote_domain_correct RegName _ _ Word $x' (fun n => @list_lookup _ n $env) $m _ ltac:(first [ assumption | set_solver+]) ) as $hdom;
    cbn [denote denote_domain list_lookup lookup] in $hdom.

 Ltac extract_pointsto_map regs Hmap rname Hrdom Hreg :=
    let rval := fresh "v"rname in
    let Hsome := fresh "Hsome" in
    first [ eassert (regs !! rname = Some _) as Hsome by auto |
    assert (is_Some (regs !! rname)) as [rval Hsome]; by (set_solver + Hrdom) ];
    let str_destr := constr:(("[" ++ Hreg ++ " " ++ Hmap ++ "]")%string) in
    iDestruct (big_sepM_delete _ _ rname with Hmap) as str_destr; first exact Hsome; clear Hsome.

  From iris.proofmode Require Import environments.
  From iris.proofmode Require Import reduction proofmode.
  (* generate a domain hypothesis for a given gmap *)
  Ltac iExtract Hmap rname Hreg :=
    lazymatch goal with
      | |- envs_entails ?H _ =>
        lazymatch pm_eval (envs_lookup Hmap H) with
        | Some (_, ?X) =>
          lazymatch X with
          | ([∗ map] _↦_ ∈ ?m', _)%I =>
            match type of m' with
            | gmap ?K ?A => let f := idtac in
                              f K A m'
            end
          end
        end
      end.
(* ltac2:(k a m hdom |- extract_pointsto_map (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) (Option.get (Ltac1.to_ident hdom))) *)


  Lemma foo (w1 w2 w3: Word) rmap :
    dom (gset RegName) (rmap) = all_registers_s ∖ {[PC]} →
    ([∗ map] k↦y ∈ delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> rmap))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    iIntros (Hdom) "Hregm".
    assert (is_Some (delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> rmap))) !! r_t4) ).
    let f := ltac2:(k a m hdom |- get_map_dom_hyp (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) hdom) in f RegName Word constr:(delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> rmap))) Hdom ).
    rewrite elem_of_gmap_dom Hdomi.
    by set_solver-.
    assert ((dom (gset RegName) (∅ : gmap RegName Word)) = ∅) as H'. admit.
    extract_pointsto_map_test (delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))) : gmap RegName Word) "Hregm" r_t1 H' "Hr_t1"
.
    (* ltac:(set_solver ; fail). *)
    (* get_map_dom_hyp 'RegName 'Word constr:(<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅)) : gmap RegName Word) @Hdomi. *)
    assert ( (delete r_t3 (<[r_t1:=w1]> (<[r_t4:=w2]> (<[r_t2:=w3]> ∅))) : gmap RegName Word) !! r_t2 = Some w3) by (by simpl_map).


    insert_pointsto_map "Hregm" "Hr_t0".
    let hdom := Control.hyp (match! goal with [ hdomsym :  dom (gset _) ?mm = ?d |- _ ] =>
            match (Constr.equal m mm) with
            | false => Control.zero Match_failure
            | _ => hdomsym end
                             end) (* TODO: add catch to have empty hyp *)

    lazy_match! m with
    | ∅ => ltac1:(idtac "empty")
    | _ => ltac1:(idtac "other") end.

    iIntros "H".
    map_simpl "H".
  Abort.



  From iris.proofmode Require Import environments.
  From iris.proofmode Require Import reduction proofmode.
  Ltac2 dom_hyp_aux k a x :=
    let (x', m, fm) := (reify_helper k a x []) in
    let env := make_list fm in
    replace_with x '(@denote _ _ _ _ $x' (fun n => @list_lookup _ n $env) $m) > [() | reflexivity];



  Lemma foo (w1 w2 w3: Word) :
    ([∗ map] k↦y ∈ delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    extract_pointsto_map regs "Hregm" r_t1 Hr_full "Hr_t1".
    insert_pointsto_map "Hregm" "Hr_t0".

    iIntros "H".
    map_simpl "H".
  Abort.

End test.
