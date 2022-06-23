From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import proofmode logrel.
Open Scope Z_scope.

Ltac some_register0 reg w Hw :=
  let nw := fresh w in
  let nHw := fresh Hw in
  match goal with
  | hdom: dom (gset RegName) ?rrmap = ?all_regs |- _ =>
      assert (is_Some (rrmap !! reg))
      as [nw nHw]
           by ( rewrite elem_of_gmap_dom hdom ; set_solver+)
  | hrfull: (∀ x : RegName, is_Some (?rrmap !! x)) |- _ =>
      assert (is_Some (rrmap !! reg))
      as [nw nHw]
           by apply hrfull
  end.

Ltac some_register0' reg rmap w Hw :=
  let nw := fresh w in
  let nHw := fresh Hw in
  match goal with
  | hdom: dom (gset RegName) rmap = ?all_regs |- _ =>
      assert (is_Some (rmap !! reg))
      as [nw nHw]
           by ( rewrite elem_of_gmap_dom hdom ; set_solver+)
  | hrfull: (∀ x : RegName, is_Some (rmap !! x)) |- _ =>
      assert (is_Some (rmap !! reg))
      as [nw nHw]
           by apply hrfull
  | _ => fail
  end.


Tactic Notation "some_register" constr(reg) "as" ident(w) ident(Hw) :=
  some_register0 reg w Hw.

Tactic Notation
       "some_register" constr(reg)
       "with" constr(rmap)
       "as" ident(w) ident(Hw) :=
  some_register0' reg rmap w Hw.

(* TODO add the create_gmap_default cases in the automatic tactic *)
Ltac solve_lookup_none :=
  repeat (
      match goal with
      | h: _ |- (<[ ?reg := ?w ]> ?rmap) !! ?reg = None => fail
      | h: _ |- (<[ ?reg := ?w ]> ?rmap) !! ?reg' = None =>
          erewrite (lookup_insert_ne _)
      | h: _ |- (delete ?reg ?rmap) !! ?reg = None =>
          by rewrite lookup_delete
      | h: _ |- (delete ?reg ?rmap) !! ?reg' = None =>
          erewrite (lookup_delete_ne _)
      | hdom: dom (gset RegName) ?rmap = ?all_regs |-
          _ !! _ = None => apply not_elem_of_dom ; set_solver
      |  _ => idtac
      end ; eauto ).

Ltac solve_lookup_some :=
  repeat (
      match goal with
      | h: _ |- (<[ ?reg := ?w ]> ?rmap) !! ?reg = Some _ =>
          erewrite (lookup_insert _)
      | h: _ |- (<[ ?reg := ?w ]> ?rmap) !! ?reg' = Some _ =>
          erewrite (lookup_insert_ne _)
      | h: _ |- (delete ?reg ?rmap) !! ?reg = Some _ => fail
      | h: _ |- (delete ?reg ?rmap) !! ?reg' = Some _ =>
        erewrite (lookup_delete_ne _)
      |  _ => idtac
      end ; eauto ).

Ltac solve_lookup :=
  try
  (match goal with
  | h: _ |- _ !! _ = Some _ =>
      solve_lookup_some
  | h: _ |- _ !! _ = None =>
      solve_lookup_none
   end) ; eauto.
  (* ; try (simplify_map_eq ; eauto). *)

Ltac extract_register0 reg hrmap hpat:=
  match goal with
  | h: _ |- context[ ( environments.Esnoc _ (INamed hrmap)
                                         (big_opM bi_sep ?Φ ?rmap))]
    => match rmap with
      | <[ reg := ?w ]> ?rmap' =>
          iDestruct (big_sepM_insert_delete with hrmap) as hpat
      | _ => iDestruct (big_sepM_delete _ _ reg with hrmap) as hpat
      end
  end
  ; solve_lookup.

Ltac extract_register0' reg w hw hrmap hpat:=
  match goal with
  | hsome: ?rmap !! reg = Some ?wreg |- _ => idtac
  |  _ => some_register0 reg w hw
  end
  ; extract_register0 reg hrmap hpat.

Tactic Notation "extract_register" constr(reg)
       "with" constr(hrmap)
       "as" "(" ident(w) ident(hw) ")"
       constr(hpat)
  := extract_register0' reg w hw hrmap hpat.

Tactic Notation "extract_register" constr(reg)
       "with" constr(hrmap)
       "as" constr(hpat)
  := extract_register0 reg hrmap hpat.


Ltac clean_rmap :=
  repeat (
      match goal with
      | h: _ |- context [ <[ ?reg := _ ]> (delete ?reg _) ]
        => rewrite insert_delete_insert
      | h: _ |- context [ <[ ?reg := _ ]> ?rmap ]
        => match rmap with
          | context[ (delete reg _) ] =>
              rewrite <- delete_insert_ne; auto
          | _ => fail
          end
      end).

(* Ltac clean_rmap' := *)
(*   (* repeat ( *) *)
(*       match goal with *)
(*       | h: _ |- context [ <[ ?reg := _ ]> (delete ?reg _) ] *)
(*         => set (Hb:= "insert_delete_insert") ; rewrite insert_delete_insert *)
(*       | h: _ |- context [ <[ ?reg := _ ]> ?rmap ] *)
(*         => set (Hb:= "insert") ; *)
(*           match rmap with *)
(*           | context[ (delete reg _) ] => *)
(*               rewrite <- delete_insert_ne; auto *)
(*           | _ => fail *)
(*           end *)
(*       | h: _ |- context [ delete ?reg ?rmap ] => *)
(*           repeat ( *)
(*               try (set (regz:= reg)) ; try (set (rmapz := rmap)) ; *)
(*               subst ; clear; *)
(*         try (set (Hb:= "delete")) ; *)
(*           match rmap with *)
(*           | context[ <[ reg := _ ]> _ ] => (* delete reg (... (<[reg := _]> _))*) *)
(*               try (set (Hb2:= "insert")) ; *)
(*               match rmap with *)
(*               | <[ reg := _ ]> _ => (* delete reg (<[ reg := _ ]> m) --> (delete reg m) *) *)
(*               try (set (Hb3:= "delete")) ; *)
(*                   rewrite (delete_insert_delete _ reg _) *)
(*               (* TODO we need to split here, in case we can use delete_insert *) *)
(*               | delete reg _ => (* delete reg (delete reg _) --> (delete reg _) *) *)
(*               try (set (Hb3:= "idemp")) ; *)
(*                   rewrite (delete_idemp _ reg) *)
(*               | delete ?reg' _ => (* delete reg (delete reg' _) --> delete reg' (delete reg _) *) *)
(*               try (set (Hb3:= "commute")) ; *)
(*                   rewrite (delete_commute _ reg _) *)
(*               | <[ ?reg' := _ ]> _ => (* delete reg (<[ reg' := _ ]> m) -->  *) *)
(*               try (set (Hb3:= "insert_ne")) ; *)
(*                   rewrite (delete_insert_ne _ reg _) ; auto *)
(*               | _ => (* delete reg m) *) *)
(*               try (set (Hb3:= "any")) ; idtac *)
(*               end *)
(*           | _ => *)
(*               try (set (Hb2:= "any")) ; *)
(*               idtac *)
(*           end) *)
(*               ; try (set (regz:= reg)) ; try (set (rmapz := rmap)) *)
(*       end. *)

Ltac insert_register0 reg hpat hrmap :=
  iDestruct (big_sepM_insert _ _ reg with hpat) as hrmap
  ; match goal with
    | h: _ |- environments.envs_entails _ (wp _ _ _ _) => idtac
    | h: _ |- environments.envs_entails _ (big_opM _ _ _) => idtac
    | h: _ |- environments.envs_entails _ ?g =>
        iFrame ; iFrame "#" ;
        match goal with
        | h: _ |- environments.envs_entails _ ?g =>
            match g with
            | ⌜is_cap _ = _⌝%I => iPureIntro ; done
            (* | interp (WInt _) => iApply interp_int *)
            | _ => try (iApply interp_int)
            end
        | _ => idtac
        end
    | h:_ |- context [_ !! _ = None] => solve_lookup
    | _ => fail
    end
  ; clean_rmap.

Tactic Notation "insert_register" constr(reg) "with" constr(hpat)
       "as" constr(hrmap) := insert_register0 reg hpat hrmap.
