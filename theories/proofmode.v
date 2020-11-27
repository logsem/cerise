From iris.proofmode Require Import tactics spec_patterns coq_tactics ltac_tactics reduction.
Require Import Eqdep_dec List.
From cap_machine Require Import classes rules macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample.
From cap_machine Require Export solve_pure solve_addr_extra.
From cap_machine Require Import NamedProp proofmode_instr_rules.
From iris.bi Require Import bi tactics.
Import bi.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Bool Constr.
Set Default Proof Mode "Classic".

Section codefrag.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

(* TODO: move elsewhere: to region.v? *)
Definition codefrag (a0: Addr) (cs: list Word) :=
  ([[ a0, (a0 ^+ length cs)%a ]] ↦ₐ [[ cs ]])%I.

Lemma codefrag_contiguous_region a0 cs :
  codefrag a0 cs -∗
  ⌜ContiguousRegion a0 (length cs)⌝.
Proof using.
  iIntros "Hcs". unfold codefrag.
  iDestruct (big_sepL2_length with "Hcs") as %Hl.
  set an := (a0 + length cs)%a in Hl |- *.
  unfold ContiguousRegion.
  destruct an eqn:Han; subst an; [ by eauto |]. cbn.
  exfalso. rewrite region_addrs_length /region_size in Hl.
  solve_addr.
Qed.

Lemma codefrag_lookup_acc a0 (cs: list Word) (i: nat) w:
  SimplTC (cs !! i) (Some w) →
  codefrag a0 cs -∗
  (a0 ^+ i)%a ↦ₐ w ∗ ((a0 ^+ i)%a ↦ₐ w -∗ codefrag a0 cs).
Proof.
  iIntros (Hi) "Hcs".
  iDestruct (codefrag_contiguous_region with "Hcs") as %Hub.
  rewrite /codefrag.
  destruct Hub as [? Hub].
  iDestruct (big_sepL2_lookup_acc with "Hcs") as "[Hw Hcont]"; only 2: by eauto.
  eapply region_addrs_lookup_middle with (n:=length cs).
  { apply lookup_lt_is_Some_1; eauto. }
  { solve_addr. }
  iFrame.
Qed.

End codefrag.

(* Administrative reduction steps *)
Ltac wp_pure := iApply wp_pure_step_later; [ by auto | iNext ].
Ltac wp_instr :=
  iApply (wp_bind (fill [SeqCtx]));
  (* Reduce the [fill] under the WP... *)
  let X := fresh in
  set X := (fill _);
  cbv in X;
  subst X;
  cbv beta.

(* "iApply with on-demand framing" *)

Lemma envs_clear_spatial_sound_rev {PROP: bi} (Δ: envs PROP) :
  of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ ⊢ of_envs Δ.
Proof.
  rewrite !of_envs_eq /envs_clear_spatial /=.
  rewrite -persistent_and_sep_assoc.
  apply pure_elim_l=> Hwf.
Admitted.

Lemma tac_specialize_assert_delay {PROP: bi} (Δ: envs PROP) j q R P1 P2 P1' F Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 → AddModal P1' P1 Q →
  envs_entails (envs_delete true j q Δ) (P1' ∗ F) →
  match
    envs_app false (Esnoc Enil j P2)
      (envs_clear_spatial (envs_delete true j q Δ))
  with
  | Some Δ1 =>
    envs_entails Δ1 (F -∗ Q)
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ??? HH.
  destruct (envs_app _ _ _) eqn:?; last done.
  intros HQ.
  rewrite envs_lookup_sound //.
  rewrite envs_clear_spatial_sound.
  rewrite (env_spatial_is_nil_intuitionistically (envs_clear_spatial _)) //.
  rewrite intuitionistically_sep_dup.
  rewrite intuitionistic_intuitionistically.
  rewrite -!sep_assoc.
  (* rewrite envs_clear_spatial_sound_rev. *)

  (* rewrite HH (into_wand q false) /= -(add_modal P1' P1 Q). cancel [P1']. *)
  (* apply wand_intro_l. rewrite assoc wand_elim_r. *)
  (* apply envs_app_singleton_sound in Heqo. cbn in Heqo. *)


(*   rewrite envs_app_singleton_sound in Heqo. *)

(*   apply wand_intro_l. rewrite assoc wand_elim_r. *)

(*   destruct (_ ≫= _) as [[Δ1 Δ2']|] eqn:?; last done. *)
(*   destruct HQ as [HP1 HQ]. *)
(*   destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=; *)
(*     destruct (envs_app _ _ _) eqn:?; simplify_eq/=. *)
(*   rewrite envs_lookup_sound // envs_split_sound //. *)
(*   rewrite (envs_app_singleton_sound Δ2) //; simpl. *)
(*   rewrite HP1 (into_wand q false) /= -(add_modal P1' P1 Q). cancel [P1']. *)
(*   apply wand_intro_l. by rewrite assoc !wand_elim_r. *)
(* Qed. *)
Admitted.

(* Typeclasses to look-up framable resources in the goal *)

Class EnvsLookupSpatial {PROP: bi} (Δ: envs PROP) (P: PROP) (i: ident) := {}.
Hint Mode EnvsLookupSpatial + ! ! - : typeclass_instances.

Instance EnvsLookupSpatial_here (PROP: bi) (Γp Γs: env PROP) P c i :
  EnvsLookupSpatial (Envs Γp (Esnoc Γs i P) c) P i.
Qed.

Instance EnvsLookupSpatial_next (PROP: bi) (Γp Γs: env PROP) P Q c i j :
  EnvsLookupSpatial (Envs Γp Γs c) Q j →
  EnvsLookupSpatial (Envs Γp (Esnoc Γs i P) c) Q j.
Qed.

Class FramableMachineResource {Σ: gFunctors} (P: iProp Σ) := {}.
Hint Mode FramableMachineResource + ! : typeclass_instances.

Class LookupFramableMachineResource {Σ: gFunctors} (G: iProp Σ) (P: iProp Σ) := {}.
Hint Mode LookupFramableMachineResource + ! - : typeclass_instances.

Instance LookupFramableMachineResource_framable Σ (P: iProp Σ) :
  FramableMachineResource P →
  LookupFramableMachineResource P P.
Qed.

Instance LookupFramableMachineResource_sep_l Σ (G1 G2 P: iProp Σ) :
  LookupFramableMachineResource G1 P →
  LookupFramableMachineResource (G1 ∗ G2)%I P
| 5.
Qed.

Instance LookupFramableMachineResource_sep_r Σ (G1 G2 P: iProp Σ) :
  LookupFramableMachineResource G2 P →
  LookupFramableMachineResource (G1 ∗ G2)%I P
| 6. (* start looking left *)
Qed.

Instance LookupFramableMachineResource_later Σ (G P: iProp Σ) :
  LookupFramableMachineResource G P →
  LookupFramableMachineResource (▷ G)%I P.
Qed.

Class FramableMachineHyp {Σ} (Δ: envs (uPredI (iResUR Σ))) (G: iProp Σ) (i: ident) := {}.
Hint Mode FramableMachineHyp + ! ! - : typeclass_instances.
Instance FramableMachineHyp_default Σ (Δ: envs (uPredI (iResUR Σ))) G P i:
  LookupFramableMachineResource G P →
  EnvsLookupSpatial Δ P i →
  FramableMachineHyp Δ G i.
Qed.

Class FramableRegisterPointsto (r: RegName) (w: Word) := {}.
Hint Mode FramableRegisterPointsto + - : typeclass_instances.
Class FramableMemoryPointsto (a: Addr) (w: Word) := {}.
Hint Mode FramableMemoryPointsto + - : typeclass_instances.
Class FramableCodefrag (a: Addr) (l: list Word) := {}.
Hint Mode FramableCodefrag + - : typeclass_instances.

Instance FramableRegisterPointsto_default r w :
  FramableRegisterPointsto r w
| 100. Qed.

Instance FramableMemoryPointsto_default a w :
  FramableMemoryPointsto a w
| 100. Qed.

Instance FramableCodefrag_default a l :
  FramableCodefrag a l
| 100. Qed.

Instance FramableMachineResource_reg `{regG Σ} r w :
  FramableRegisterPointsto r w →
  FramableMachineResource (r ↦ᵣ w).
Qed.

Instance FramableMachineResource_mem `{memG Σ} a w :
  FramableMemoryPointsto a w →
  FramableMachineResource (a ↦ₐ w).
Qed.

Instance FramableMachineResource_codefrag `{memG Σ} a l :
  FramableCodefrag a l →
  FramableMachineResource (codefrag a l).
Qed.

Definition framable_machine_hyp `{@FramableMachineHyp Σ Δ P i} := i.


(* The auto-framing tactic *)
Ltac2 Type hyp_table_kind := [ Reg | Mem | Codefrag ].

Ltac2 assert_constr_eq (c1: constr) (c2: constr) :=
  match Constr.equal c1 c2 with
  | false => Control.zero Match_failure (* backtrack *)
  | true => ()
  end.

Ltac2 iFrameCapT (table: (constr * constr * hyp_table_kind) list ref) :=
  lazy_match! goal with
  [ |- envs_entails ?Δ ?p ] =>
    let h := eval unfold framable_machine_hyp in (@framable_machine_hyp _ $Δ $p _ _) in
    match! Δ with context [ Esnoc _ ?h' ?hh ] =>
      assert_constr_eq h h';
      let hname :=
        lazy_match! h with
        | INamed ?s => s
        | IAnon _ => '("?")
        end
      in
      let (lhs, kind) :=
        lazy_match! hh with
        | (?r ↦ᵣ _)%I => (r, Reg)
        | (?a ↦ₐ _)%I => (a, Mem)
        | (codefrag ?a _) => (a, Codefrag)
        end in
      table.(contents) := (hname, lhs, kind) :: table.(contents)
    end;
    ltac1:(h |- iFrame h) (Ltac1.of_constr h)
  end.

Ltac2 iFrameCap () :=
  let table := { contents := [] } in
  let _ := iFrameCapT table in
  ().

Ltac iFrameCap := ltac2:(iFrameCap ()).

(* iApplyCapAuto *)

(* Helpers *)

Ltac solve_to_wand tt :=
    iSolveTC ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand".

Ltac2 iTypeOf (h: constr) :=
  let Δ := match! goal with [ |- envs_entails ?Δ _ ] => Δ end in
  (* XXX should be pm_eval *)
  eval cbv in (envs_lookup $h $Δ).

Ltac2 iFresh () :=
  ltac1:(iStartProof);
  lazy_match! goal with
  | [ |- envs_entails (Envs ?Δp ?Δs ?c) ?q ] =>
    let c' := eval vm_compute in (Pos.succ $c) in
    ltac1:(Δp Δs c' q |-
           convert_concl_no_check (envs_entails (Envs Δp Δs c') q))
      (Ltac1.of_constr Δp) (Ltac1.of_constr Δs) (Ltac1.of_constr c')
      (Ltac1.of_constr q);
    '(IAnon $c)
  end.

Ltac iNamedIntro :=
  let x := iFresh in
  iIntros x; iNamed x.
Ltac2 iNamedIntro () := ltac1:(iNamedIntro).

(* multi-goal repeat *)
Ltac2 rec grepeat (t: unit -> unit) :=
  ifcatch (fun _ => Control.progress t)
    (fun _ => Control.check_interrupt (); grepeat t) (fun _ => ()).

Ltac2 on_lasts tacs :=
  Control.extend [] (fun _ => ()) tacs.


(* iApplyCapAuto_init *)

Ltac2 iSpecializeDelay (h: constr) :=
  refine '(tac_specialize_assert_delay _ $h _ _ _ _ _ _ _ _ _ _ _ _);
  Control.shelve_unifiable ();
  Control.dispatch [
    (fun _ => ltac1:(pm_reflexivity));
    (fun _ => ltac1:(solve_to_wand tt));
    (fun _ => ltac1:(class_apply @add_modal_id));
    (fun _ => ltac1:(pm_reduce));
    (fun _ => ltac1:(pm_reduce))
  ].

Ltac iApplyHypLast H :=
  eapply tac_apply with H _ _ _;
  [pm_reflexivity
  |iSolveTC
  |pm_reduce; pm_prettify].

Ltac2 iApplyCapAutoT_init0 lemma :=
  let tbl := { contents := [] } in
  let x := iFresh () in
  ltac1:(x lem |- once (iPoseProofCore lem as false (fun H => iRename H into x)))
    (Ltac1.of_constr x) (Ltac1.of_constr lemma);
  on_lasts [(fun _ =>
    iSpecializeDelay x > [|
      ltac1:(h |-
        let f := iFresh in
        iIntros f;
        iApplyHypLast h;
        iRevert f) (Ltac1.of_constr x)
    ]
  )];
  tbl.

Ltac2 iApplyCapAuto_init0 lemma :=
  let _ := iApplyCapAutoT_init0 lemma in ().

Ltac2 Notation "iApplyCapAuto_init" lem(constr) :=
  iApplyCapAuto_init0 lem.

Ltac iApplyCapAuto_init lemma :=
  let f := ltac2:(lem |- iApplyCapAuto_init0 (Option.get (Ltac1.to_constr lem))) in
  f lemma.

(* Name resources in the goal according to the table *)

Definition check_addr_eq (a b: Addr) `{AddrEq a b res} := res.

Ltac2 name_cap_resource (name, lhs, kind) :=
  match kind with
  | Reg =>
    match! goal with [ |- context [ (?r ↦ᵣ ?x)%I ] ] =>
      assert_constr_eq r lhs;
      ltac1:(x r name |- change (r ↦ᵣ x)%I with (name ∷ (r ↦ᵣ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr r) (Ltac1.of_constr name)
    end
  | Mem =>
    match! goal with [ |- context [ (?a ↦ₐ ?x)%I ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(x a name |- change (a ↦ₐ x)%I with (name ∷ (a ↦ₐ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | Codefrag =>
    match! goal with [ |- context [ codefrag ?a ?l ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(l a name |- change (codefrag a l) with (name ∷ (codefrag a l)))
        (Ltac1.of_constr l) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  end.

Lemma envs_entails_rew_goal {Σ} (Δ: envs (uPredI (iResUR Σ))) P P' :
  P = P' →
  envs_entails Δ P' →
  envs_entails Δ P.
Proof. intros ->. auto. Qed.

Ltac2 reintro_cap_resources tbl :=
  (refine '(@envs_entails_rew_goal _ _ _ _ _ _);
   Control.shelve_unifiable ()) >
  [ List.iter name_cap_resource (tbl.(contents)); reflexivity | () ];
  iNamedIntro ().

(* cleanup *)

(* TODO: make this extensible *)
Ltac2 iApplyCapAuto_cleanup () :=
  cbn [rules_Get.denote rules_AddSubLt.denote].

(* iApplyCapAutoCore *)

Ltac2 iFrameCapSolve () :=
  grepeat (fun _ =>
    try (Control.plus iFrameCap (fun _ => Control.once solve_pure))).
Ltac iFrameCapSolve := ltac2:(iFrameCapSolve ()).

Ltac iNamedAccu_fail_explain :=
  lazymatch goal with
  | |- envs_entails _ (?remaining ∗ _) =>
    fail "iApplyCapAuto: the following resources could not be found in the context:"
         remaining
  end.

Ltac2 iApplyCapAutoCore lemma :=
  let tbl := iApplyCapAutoT_init0 lemma in
  grepeat (fun _ =>
    Control.extend [] (fun _ => try (Control.once solve_pure))
      [ (fun _ => try (iFrameCapT tbl)); (fun _ => ()) ]);
  on_lasts [ (fun _ => ltac1:(iNamedAccu || iNamedAccu_fail_explain)); (fun _ => ()) ];
  on_lasts [ (fun _ =>
    iNamedIntro ();
    try ltac1:(iNext);
    try (reintro_cap_resources tbl);
    iApplyCapAuto_cleanup ()
  )].

Ltac2 Notation "iApplyCapAuto" lem(constr) := iApplyCapAutoCore lem.
Tactic Notation "iApplyCapAuto" constr(lem) :=
  let f := ltac2:(lem |- iApplyCapAutoCore (Option.get (Ltac1.to_constr lem))) in
  f lem.



(* iInstr *)

Definition as_weak_addr_incr (a b: Addr) (z: Z) `{AsWeakAddrIncr a b z} :=
  (b, Z.to_nat z).

Lemma addr_incr_zero (a: Addr) : (a ^+ 0)%a = a.
Proof. solve_addr. Qed.

Lemma addr_incr_zero_nat (a: Addr) : (a ^+ 0%nat)%a = a.
Proof. solve_addr. Qed.

Ltac iInstr_lookup0 hprog hi hcont :=
  let hprog := constr:(hprog:ident) in
  lazymatch goal with |- context [ Esnoc _ hprog (codefrag ?a_base _) ] =>
  lazymatch goal with |- context [ Esnoc _ ?hpc (PC ↦ᵣ (inr (_, _, _, ?pc_a)))%I ] =>
    let base_off := eval unfold as_weak_addr_incr in (@as_weak_addr_incr pc_a a_base _ _) in
    lazymatch base_off with
    | (?base, ?off) =>
      iPoseProofCore (codefrag_lookup_acc _ _ off with hprog) as false (fun H =>
        eapply tac_and_destruct with H _ hi hcont _ _ _;
        [pm_reflexivity
        |pm_reduce; iSolveTC
        |pm_reduce];
        rewrite ?addr_incr_zero ?addr_incr_zero_nat
      )
     end
  end end.

Tactic Notation "iInstr_lookup" constr(hprog) "as" constr(hi) constr(hcont) :=
  iInstr_lookup0 hprog hi hcont.

Ltac iInstr_get_rule hi cont :=
  lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ encodeInstrW ?instr)%I ] =>
    dispatch_instr_rule instr cont
  end.

Ltac iInstr_close hprog :=
  (* because of iApplyCapAuto's context shuffling, [hi] and [hcont]
     are not valid anymore... recover them. *)
  (* XXX make this a bit more robust *)
  lazymatch goal with |- context [ Esnoc _ ?hi (_ ↦ₐ encodeInstrW _)%I ] =>
  lazymatch goal with |- context [ Esnoc _ ?hcont (_ ↦ₐ encodeInstrW _ -∗ _)%I ] =>
    notypeclasses refine (tac_specialize false _ hi _ hcont _ _ _ _ _ _ _ _ _);
    [pm_reflexivity
    |pm_reflexivity
    |iSolveTC
    |pm_reduce];
    iRename hcont into hprog
  end end.

(* TODO: find a way of displaying an error message if iApplyCapAuto fails,
   displaying the rule it was called on, and without silencing iApplyCapAuto's
   own error messages? *)
Ltac iInstr hprog :=
  let hi := iFresh in
  let hcont := iFresh in
  iInstr_lookup hprog as hi hcont;
  wp_instr;
  iInstr_get_rule hi ltac:(fun rule =>
    iApplyCapAuto rule;
    [ .. | iInstr_close hprog; wp_pure]
  ).

Ltac2 rec iGo hprog :=
  let stop_if_at_least_two_goals () :=
    on_lasts [ (fun _ => ()); (fun _ => ()) ] in
  match Control.case (fun _ => ltac1:(hprog |- iInstr hprog) (Ltac1.of_constr hprog)) with
  | Err (_) => ()
  | Val (_) => Control.plus stop_if_at_least_two_goals (fun _ => iGo hprog)
  end.

Ltac iGo hprog :=
  let f := ltac2:(hprog |- iGo (Option.get (Ltac1.to_constr hprog))) in
  f hprog.