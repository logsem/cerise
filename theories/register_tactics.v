From Ltac2 Require Import Ltac2 Control Fresh.
Set Default Proof Mode "Classic".
From iris.proofmode Require Import reduction proofmode.
From iris.proofmode Require Import environments.
From cap_machine Require Import stdpp_extra rules_base map_simpl.

Section denote_domain.
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
   Lemma denote_domain_correct {A : Type} (rm: @rgmap A) (fm: nat -> option K) (m : gmap K A) (mdom : gset K) : dom m = mdom → dom (denote rm fm m) = denote_domain rm fm mdom.
     intro Hmdom.
     induction rm; cbn [denote denote_domain].
     - case_eq (fm k); intros; set_solver + IHrm.
     - case_eq (fm k); intros; set_solver + IHrm.
     - done.
   Qed.
End denote_domain.

Arguments denote_domain {_ _ _ _} _ _ _.
Arguments denote {_ _ _ _} _ _ _.

Ltac2 get_map_dom0 k a m hdom :=
  let (x', m, fm) := (reify_helper k a m []) in
  let env := make_list fm in
  assert ($hdom := denote_domain_correct $k _ _ $x' (fun n => @list_lookup _ n $env) $m _ ltac:(first [ assumption | set_solver+]) );
  rewrite ?dom_empty_L in $hdom;
  cbn [denote denote_domain list_lookup lookup] in $hdom.

Ltac get_map_dom0 k a m hdom :=
  let f := ltac2:(k a m hdom |- get_map_dom0 (Option.get (Ltac1.to_constr k)) (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr m)) (Option.get (Ltac1.to_ident hdom))) in f k a m ident:(hdom).

(* generate a domain hypothesis for a given gmap *)
Tactic Notation "get_map_dom" constr(m) "as" ident(hdom) :=
  match type of m with
  | ?t => match eval compute in t with (* type will not compute for very large maps *)
         | gmap ?K ?A => let hdom' := fresh "hdom" in get_map_dom0 K A m ident:(hdom'); rename hdom' into hdom end end.

(* solving goals with map domains faster than set_solver *)
Tactic Notation "solve_map_dom" :=
  let Hdom := fresh "Hdom" in
  match goal with | |- dom ?m = ?dom => get_map_dom m as Hdom; rewrite Hdom; clear Hdom; set_solver+ end.

(* try to find concrete value in gmap *)
Ltac solve_lookup_some :=
repeat (
    lazymatch goal with
    | |- (<[ ?reg := ?w ]> ?rmap) !! ?reg = Some _ =>
        rewrite lookup_insert; reflexivity
    | |- (<[ ?reg := ?w ]> ?rmap) !! ?reg' = Some _ =>
        rewrite lookup_insert_ne; [ | solve [auto]]
    | |- (delete ?reg ?rmap) !! ?reg' = Some _ =>
        rewrite lookup_delete_ne; [ | solve [auto]]
    | |- _ !! ?reg = Some _ => exact
    end ); fail.

Ltac extract_pointsto_map regs Hmap rname Hrdom Hreg :=
  let rval := fresh "v"rname in
  let Hsome := fresh "Hsome" in
  first [ eassert (regs !! rname = Some _) as Hsome by solve_lookup_some (* Try to reuse existing value, if any *) |
  assert (is_Some (regs !! rname)) as [rval Hsome] by (rewrite elem_of_gmap_dom Hrdom; set_solver +) ];
  let str_destr := constr:(("[" ++ Hreg ++ " " ++ Hmap ++ "]")%string) in
  iDestruct (big_sepM_delete _ _ rname with Hmap) as str_destr; first exact Hsome; clear Hsome.

Ltac iExtract_core m' Hmap rnames Hregs Hrdom :=
  match rnames with
  | nil => idtac
  | ?rname :: ?rtail =>
      match Hregs with
      | nil => idtac
      | ?Hname :: ?Htail =>
          extract_pointsto_map m' Hmap rname Hrdom Hname;
          (* rewrite hrdom with the deleted register `rname` in mind *)
          apply (f_equal (fun x => x ∖ {[rname]})) in Hrdom;
          rewrite -dom_delete_L in Hrdom;
          iExtract_core (delete rname m') Hmap rtail Htail Hrdom
      end
  end.

Ltac iExtract0 Hmap rnames Hregs :=
  lazymatch goal with
    | |- envs_entails ?H _ =>
      lazymatch pm_eval (envs_lookup Hmap H) with
      | Some (_, ?X) =>
        lazymatch X with
        | ([∗ map] _↦_ ∈ ?m', _)%I =>
          let Hrdom := fresh "Hrdom" in
            get_map_dom m' as Hrdom;
            iExtract_core m' Hmap rnames Hregs Hrdom;
            clear Hrdom;
            map_simpl Hmap
        end
      end
    end.

Tactic Notation "iExtract" constr(Hmap) constr(rname) "as" constr(Hreg):=
    iExtract0 Hmap [rname] [Hreg].

Tactic Notation "iExtractList" constr(Hmap) constr(rnames) "as" constr(Hregs):=
    iExtract0 Hmap rnames Hregs.

Ltac insert_pointsto_map regs Hmap rname Hrdom Hreg :=
  let Hsome := fresh "Hsome" in
  assert (regs !! rname = None) as Hsome by (rewrite elem_of_gmap_dom_none Hrdom; set_solver +);
  let str_destr := constr:(("[ $" ++ Hmap ++ " $" ++ Hreg ++ "]")%string) in
  iDestruct (big_sepM_insert _ _ rname with str_destr) as Hmap; first exact Hsome; clear Hsome.

Ltac iInsert_core m' Hmap rnames Hrdom :=
  match rnames with
  | nil => idtac
  | ?rname :: ?rtail =>
      match goal with |- context [ Esnoc _ (INamed ?Hname) ?mtch ] =>
          lazymatch mtch with | context [(rname ↦ᵣ ?rval)%I] =>
            insert_pointsto_map m' Hmap rname Hrdom Hname;
            (* rewrite hrdom with the inserted register `rname` in mind *)
            apply (f_equal (fun x => ({[rname]} ∪ x))) in Hrdom;
            rewrite -(dom_insert_L _ _ rval) in Hrdom;
            iInsert_core (<[rname:=rval]> m') Hmap rtail Hrdom
          end
      end
  end.

Ltac iInsert0 Hmap rnames :=
  lazymatch goal with
    | |- envs_entails ?H _ =>
      lazymatch pm_eval (envs_lookup Hmap H) with
      | Some (_, ?X) =>
        lazymatch X with
        | ([∗ map] _↦_ ∈ ?m', _)%I =>
          let Hrdom := fresh "Hrdom" in
            get_map_dom m' as Hrdom;
            iInsert_core m' Hmap rnames Hrdom;
            clear Hrdom;
            map_simpl Hmap
        end
      end
    end.

Tactic Notation "iInsert" constr(Hmap) constr(rname):=
    iInsert0 Hmap [rname].

Tactic Notation "iInsertList" constr(Hmap) constr(rnames):=
    iInsert0 Hmap rnames.

(* From cap_machine Require Import stdpp_extra rules_base. *)
(* Section test. *)
(*   Context `{memG Σ, regG Σ}. *)

(*   Lemma foo (w1 w2 w3: Word) rmap: *)
(*     dom (gset RegName) rmap = all_registers_s ∖ {[r_t1]}  → *)
(*     ([∗ map] k↦y ∈ (<[r_t3:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> rmap))), k ↦ᵣ y) -∗ *)
(*     r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2. *)
(*   Proof. *)
(*     iIntros (Hdomm) "Hregm". *)
(*     iExtractList "Hregm" [r_t1;r_t2] as ["Hr_t1";"Hr_t2"]. *)
(*   Abort. *)

(*   Lemma extract_opaque rmap : *)
(*     dom (gset RegName) rmap = all_registers_s ∖ {[PC; r_t0]} → *)
(*     ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗ True. *)
(*   Proof. *)
(*     iIntros (Hdomm) "Hregm". *)
(*     iExtract "Hregm" r_t8 as "Hr_t8" . *)
(*   Abort. *)

(*   Definition r_env : RegName := r_t30. *)
(*   Lemma  foo (w1 w2 : Word) b2 e2 rmap: *)
(*     dom (gset RegName) rmap = all_registers_s ∖ {[PC; r_t0; r_env; r_t1; r_t2]} → *)
(*       ([∗ map] r_i↦w_i ∈ <[r_t2:=WInt 0]> (<[r_t3:=WInt 0]> (<[r_t4:=WInt 0]> (<[r_t5:=WInt 0]> (delete r_t1 (<[r_env:=WCap E b2 e2 b2]> (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t6:=w1]> (<[r_t7:=w2]> rmap))))))))), r_i ↦ᵣ w_i) -∗ r_t1 ↦ᵣ w1. *)
(*   Proof. iIntros (Hdom) "Hregs". *)
(*      iExtractList "Hregs" [r_env;r_t2;r_t6;r_t7] as ["Hr_env";"Hr_t2";"Hr_t6";"Hr_t7"]. *)
(*   Abort. *)
(* End test. *)
