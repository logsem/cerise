From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
Require Import Eqdep_dec List.
From cap_machine Require Import classes rules macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample.
From cap_machine Require Export class_instances solve_pure solve_addr_extra.
From cap_machine Require Import NamedProp proofmode_instr_rules.
From machine_utils Require Export tactics.
From iris.bi Require Import bi.
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
  exfalso. rewrite finz_seq_between_length /finz.dist in Hl.
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
  eapply finz_seq_between_lookup with (n:=length cs).
  { apply lookup_lt_is_Some_1; eauto. }
  { solve_addr. }
  iFrame.
Qed.

End codefrag.

(* Administrative reduction steps *)
Ltac wp_pure := iApply wp_pure_step_later; [ by auto | iNext ; iIntros "_" ].
(* TODO iIntros "_" fixes the lc 1 introduces in Iris 4.0.0, but I'm not sure that is the right place *)
Ltac wp_end := iApply wp_value.
Ltac wp_instr :=
  iApply (wp_bind (fill [SeqCtx]));
  (* Reduce the [fill] under the WP... *)
  let X := fresh in
  set X := (fill _);
  cbv in X;
  subst X;
  cbv beta.

Lemma z_addr_base {fb off off1 off2 : Z} {f0 f1 f2 : finz fb}: (f0 + off1)%f = Some f1 → (f0 + off2)%f = Some f2 → (off2 - off1)%Z = off → (f1 ^+ off)%f = f2.
  Proof. solve_addr. Qed.
Ltac solve_block_move :=
    first [solve_addr+ |
    lazymatch goal with
      | |- (?prev_a ^+ ?off)%f = ?cur_a =>
          match goal with
            | H: (prev_a + ?off1)%a = Some cur_a |- _ => solve_addr+H
            | H1: (?base_a + ?off1)%a = Some prev_a |- _ =>
                match goal with
                | H2 : (base_a + ?off2)%a = Some cur_a |- _ =>
                    apply (z_addr_base H1 H2); solve_addr+
                end
          end
     end ].

(* Ltac specifically meant for switching to the next block. Use `changePCto` to perform more arbitrary moves *)
Ltac changePC_next_block new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↦ᵣ WCap _ _ _ ?prev_a)%I ] =>
                    rewrite (_: prev_a = new_a) ; [ | solve_block_move  ] end.
(* More powerful ltac to change the address of the pc. Might take longer to solve than the more specific alternative above.*)
Ltac changePCto0 new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↦ᵣ WCap _ _ _ ?a)%I ] =>
    rewrite (_: a = new_a); [| solve_addr]
  end.
Tactic Notation "changePCto" constr(a) := changePCto0 a.

Ltac codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (codefrag ?a_base ?code) ] =>
    (match goal with H : ContiguousRegion a_base _ |- _ => idtac end ||
     let HH := fresh in
     iDestruct (codefrag_contiguous_region with h) as %HH;
     cbn [length map encodeInstrsW] in HH
    );
    (match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => idtac end ||
     (try match goal with H : SubBounds ?b ?e _ _ |- _ =>
            let HH := fresh in
            assert (HH: SubBounds b e a_base (a_base ^+ length code)%a) by solve_addr;
            cbn [length map encodeInstrsW] in HH
          end))
  end.

Ltac clear_codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (codefrag ?a_base ?code) ] =>
    try match goal with H : ContiguousRegion a_base _ |- _ => clear H end;
    try match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => clear H end
  end.

(* Classes for the code sub-block focusing tactic *)

Create HintDb proofmode_focus.
#[export] Hint Constants Opaque : proofmode_focus.
#[export] Hint Variables Opaque : proofmode_focus.

Definition App {A} (l1 l2 ll: list A) :=
  ll = l1 ++ l2.
#[export] Hint Mode App - ! ! - : proofmode_focus.

Lemma App_nil_r A (l: list A) : App l [] l.
Proof. rewrite /App app_nil_r //. Qed.
#[export] Hint Resolve App_nil_r : proofmode_focus.

Lemma App_nil_l A (l: list A) : App [] l l.
Proof. reflexivity. Qed.
#[export] Hint Resolve App_nil_l : proofmode_focus.

Lemma App_nil_default A (l1 l2: list A): App l1 l2 (l1 ++ l2).
Proof. reflexivity. Qed.
#[export] Hint Resolve App_nil_default | 100 : proofmode_focus.

Definition NthSubBlock {A} (ll: list A) (n: nat) (l1: list A) (l: list A) (l2: list A) :=
  ll = l1 ++ l ++ l2.
#[export] Hint Mode NthSubBlock + ! + - - - : proofmode_focus.

Lemma NthSubBlock_O_rest A (l1 l2: list A):
  NthSubBlock (l1 ++ l2) 0 [] l1 l2.
Proof. reflexivity. Qed.
#[export] Hint Resolve NthSubBlock_O_rest : proofmode_focus.

Lemma NthSubBlock_O_last A (l1: list A):
  NthSubBlock l1 0 [] l1 [].
Proof. unfold NthSubBlock. rewrite app_nil_r//. Qed.
#[export] Hint Resolve NthSubBlock_O_last | 100 : proofmode_focus.

Lemma NthSubBlock_S A (l0 ll l1 l2 l3 l0l1: list A) n:
  NthSubBlock ll n l1 l2 l3 →
  App l0 l1 l0l1 →
  NthSubBlock (l0 ++ ll) (S n) l0l1 l2 l3.
Proof. unfold NthSubBlock. intros -> ->. rewrite app_assoc //. Qed.
#[export] Hint Resolve NthSubBlock_S : proofmode_focus.

Section codefrag_subblock.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Lemma codefrag_block0_acc a0 (l1 l2: list Word):
    codefrag a0 (l1 ++ l2) -∗
    codefrag a0 l1 ∗
    (codefrag a0 l1 -∗ codefrag a0 (l1 ++ l2)).
  Proof.
    rewrite /codefrag. iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %Hregion.
    destruct Hregion as [an Han]. rewrite app_length in Han |- *.
    iDestruct (region_mapsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    by solve_addr. by rewrite /finz.dist; solve_addr.
    iFrame. iIntros "H1".
    rewrite region_mapsto_split. iFrame. solve_addr. rewrite /finz.dist; solve_addr.
  Qed.

  Lemma codefrag_block_acc (n: nat) a0 (cs: list Word) l1 l l2:
    NthSubBlock cs n l1 l l2 →
    codefrag a0 cs -∗
    ∃ (ai: Addr), ⌜(a0 + length l1)%a = Some ai⌝ ∗
    codefrag ai l ∗
    (codefrag ai l -∗ codefrag a0 cs).
  Proof.
    unfold NthSubBlock. intros ->. rewrite /codefrag. iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %[a1 Ha1].
    rewrite !app_length in Ha1 |- *.
    iDestruct (region_mapsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    solve_addr. rewrite /finz.dist; solve_addr.
    iExists (a0 ^+ length l1)%a. iSplitR. iPureIntro; solve_addr.
    iDestruct (region_mapsto_split _ _ ((a0 ^+ length l1) ^+ length l)%a with "H2") as "[H2 H3]".
    solve_addr. rewrite /finz.dist; solve_addr. iFrame.
    iIntros "H2".
    rewrite region_mapsto_split. iFrame. 2: solve_addr. 2: rewrite /finz.dist; solve_addr.
    rewrite region_mapsto_split. iFrame. solve_addr. rewrite /finz.dist; solve_addr.
  Qed.

End codefrag_subblock.

Lemma focus_block_0_SubBounds (b e b' : Addr) k m :
  SubBounds b e b' (b' ^+ k)%a →
  ContiguousRegion b' m →
  (0 ≤ m)%Z →
  (m ≤ k)%Z →
  SubBounds b e b' (b' ^+ m)%a.
Proof. solve_addr. Qed.

(* More efficient version of codefrag_facts (avoids calling [solve_addr])
   because we have slightly more information when doing focus_block_0 *)
Ltac focus_block_0_codefrag_facts hi a0 :=
  let HCR := fresh in
  iDestruct (codefrag_contiguous_region with hi) as %HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_0_SubBounds _ _ _ _ _ HSB HCR _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block_0 h hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag ?a0 _) ] =>
    iPoseProof (codefrag_block0_acc with h) as x;
    eapply tac_and_destruct with x _ hi hcont _ _ _;
    [pm_reflexivity|pm_reduce;iSolveTC|
     pm_reduce;
     lazymatch goal with
     | |- False =>
       let hi := pretty_ident hi in
       let hcont := pretty_ident hcont in
       fail "focus_block_0:" hi "or" hcont "not fresh"
     | _ => idtac
     end];
    focus_block_0_codefrag_facts hi a0
  end.

Tactic Notation "focus_block_0" constr(h) "as" constr(hi) constr(hcont) :=
  focus_block_0 h hi hcont.

Lemma focus_block_SubBounds (b e b' b'': Addr) k m n :
  SubBounds b e b' (b' ^+ k)%a →
  ContiguousRegion b'' m →
  (b' + n)%a = Some b'' →
  (0 ≤ n)%Z →
  (0 ≤ m)%Z →
  ((n + m) <= k)%Z →
  SubBounds b e b'' (b'' ^+ m)%a.
Proof. solve_addr. Qed.

(* More efficient version of codefrag_facts (avoids calling [solve_addr])
   because we have slightly more information when doing focus_block *)
Ltac focus_block_codefrag_facts hi a0 Ha_base :=
  let HCR := fresh in
  iDestruct (codefrag_contiguous_region with hi) as %HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_SubBounds _ _ _ _ _ _ _ HSB HCR Ha_base _ _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag ?a0 _) ] =>
    iPoseProof ((codefrag_block_acc n) with h) as (a_base) x;
      [ once (typeclasses eauto with proofmode_focus) | ];
    let xbase := iFresh in
    let y := iFresh in
    eapply tac_and_destruct with x _ xbase y _ _ _;
      [pm_reflexivity|pm_reduce;iSolveTC|pm_reduce];
    iPure xbase as Ha_base;
    eapply tac_and_destruct with y _ hi hcont _ _ _;
      [pm_reflexivity|pm_reduce;iSolveTC|pm_reduce];
    focus_block_codefrag_facts hi a0 Ha_base;
    changePC_next_block a_base
  end.

Tactic Notation "focus_block" constr(n) constr(h) "as"
       ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block n h a_base Ha_base hi hcont.

Ltac unfocus_block hi hcont h :=
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let h := constr:(h:ident) in
  clear_codefrag_facts hi;
  iDestruct (hcont with hi) as h.

Tactic Notation "unfocus_block" constr(hi) constr(hcont) "as" constr(h) :=
  unfocus_block hi hcont h.

(* "iApply with on-demand framing" *)

(* TODO: These proofs should probably not use the proof mode tactics *)
Lemma envs_clear_spatial_sound_rev {PROP: bi} (Δ: envs PROP) :
  envs_wf Δ →
  of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ ⊢ of_envs Δ.
Proof.
  intros.
  rewrite !of_envs_eq /envs_clear_spatial /=.
  rewrite -persistent_and_sep_assoc.
  iIntros "H". iDestruct "H" as "[% [[? _] ?]]". iFrame. iSplit; eauto.
Qed.

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
  rewrite envs_entails_unseal. intros ??? HH.
  destruct (envs_app _ _ _) eqn:?; last done.
  intros HQ.
  rewrite envs_lookup_sound //.
  set Δ' := envs_delete true j q Δ in HH Heqo |- *.
  iIntros "[HR HΔ']".
  iAssert (⌜envs_wf Δ'⌝)%I as %?.
  { rewrite of_envs_eq. iDestruct "HΔ'" as "[? ?]". eauto. }
  rewrite envs_clear_spatial_sound.
  set Δ'i := envs_clear_spatial Δ'.
  set Δ's := env_spatial Δ'.
  iDestruct "HΔ'" as "[#HΔ'i Hs]".
  iDestruct (envs_clear_spatial_sound_rev with "[$HΔ'i $Hs]") as "HΔ'"; auto.
  iDestruct (HH with "HΔ'") as "[HP1' HF]".
  iApply add_modal. eauto. iFrame. iIntros "HP1".
  iApply (HQ with "[HR HP1] HF").
  { iApply (envs_app_singleton_sound with "[] [HR HP1]"). eauto. iApply "HΔ'i".
    iApply (into_wand with "[HR]"). eauto. eauto. eauto. }
Qed.

(* Typeclass instances to look-up framable resources in the goal, for
   [FramableMachineResource] from [machine_utils/tactics.v]
*)

Class FramableRegisterPointsto (r: RegName) (w: Word) := {}.
#[export] Hint Mode FramableRegisterPointsto + - : typeclass_instances.
Class FramableMemoryPointsto (a: Addr) (dq: dfrac) (w: Word) := {}.
#[export] Hint Mode FramableMemoryPointsto + - - : typeclass_instances.
Class FramableCodefrag (a: Addr) (l: list Word) := {}.
#[export] Hint Mode FramableCodefrag + - : typeclass_instances.

Instance FramableRegisterPointsto_default r w :
  FramableRegisterPointsto r w
| 100. Qed.

Instance FramableMemoryPointsto_default a dq w :
  FramableMemoryPointsto a dq w
| 100. Qed.

Instance FramableCodefrag_default a l :
  FramableCodefrag a l
| 100. Qed.

Instance FramableMachineResource_reg `{regG Σ} r w :
  FramableRegisterPointsto r w →
  FramableMachineResource (r ↦ᵣ w).
Qed.

Instance FramableMachineResource_mem `{memG Σ} a dq w :
  FramableMemoryPointsto a dq w →
  FramableMachineResource (a ↦ₐ{dq} w).
Qed.

Instance FramableMachineResource_codefrag `{memG Σ} a l :
  FramableCodefrag a l →
  FramableMachineResource (codefrag a l).
Qed.


(* remembering names after auto-framing done by iFrameAuto *)

Ltac2 Type hyp_table_kind := [ Reg | Mem | Codefrag ].

Ltac2 record_framed
      (table: (constr * constr * hyp_table_kind) list ref)
      (framed: constr * constr)
  :=
  let (hname, hh) := framed in
  let (lhs, kind) :=
    lazy_match! hh with
    | (?r ↦ᵣ _)%I => (r, Reg)
    | (?a ↦ₐ{_} _)%I => (a, Mem)
    | (codefrag ?a _) => (a, Codefrag)
    end in
  table.(contents) := (hname, lhs, kind) :: table.(contents).

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
           change_no_check (envs_entails (Envs Δp Δs c') q))
      (Ltac1.of_constr Δp) (Ltac1.of_constr Δs) (Ltac1.of_constr c')
      (Ltac1.of_constr q);
    '(IAnon $c)
  end.

Ltac iNamedIntro :=
  let x := iFresh in
  iIntros x; iNamed x.
Ltac2 iNamedIntro () := ltac1:(iNamedIntro).

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

Definition check_addr_eq (a b: Addr) `{FinZEq _ a b res} := res.

Ltac2 name_cap_resource (name, lhs, kind) :=
  match kind with
  | Reg =>
    match! goal with [ |- context [ (?r ↦ᵣ ?x)%I ] ] =>
      assert_constr_eq r lhs;
      ltac1:(x r name |- change (r ↦ᵣ x)%I with (name ∷ (r ↦ᵣ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr r) (Ltac1.of_constr name)
    end
  | Mem =>
    match! goal with [ |- context [ (?a ↦ₐ{?dq} ?x)%I ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(x dq a name |- change (a ↦ₐ{dq} x)%I with (name ∷ (a ↦ₐ{dq} x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr dq) (Ltac1.of_constr a) (Ltac1.of_constr name)
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
  [ List.iter (fun x => try (name_cap_resource x)) (tbl.(contents)); reflexivity | () ];
  iNamedIntro ().

(* cleanup *)
(* TODO: make this extensible. Remove updatePcPerm? unfolding sometimes causes issues. *)
Ltac2 iApplyCapAuto_cleanup () :=
  cbn [rules_Get.denote rules_AddSubLt.denote updatePcPerm].

(* iApplyCapAutoCore *)

Ltac iNamedAccu_fail_explain :=
  lazymatch goal with
  | |- envs_entails _ (?remaining ∗ _) =>
    fail "iApplyCapAuto: the following resources could not be found in the context:"
         remaining
  end.

Ltac2 iApplyCapAutoCore lemma :=
  let tbl := iApplyCapAutoT_init0 lemma in
  let iFrameCap := fun () => record_framed tbl (iFrameAuto ()) in
  grepeat (fun _ =>
    Control.extend [] (fun _ => try (Control.once solve_pure))
      [ (fun _ => try (iFrameCap ())); (fun _ => ()) ]);
  on_lasts [ (fun _ => ltac1:(iNamedAccu || iNamedAccu_fail_explain)); (fun _ => ()) ];
  on_lasts [ (fun _ =>
    iNamedIntro ();
    try ltac1:(iNext);
    reintro_cap_resources tbl;
    iApplyCapAuto_cleanup ()
  )].

Ltac2 Notation "iApplyCapAuto" lem(constr) := iApplyCapAutoCore lem.
Tactic Notation "iApplyCapAuto" constr(lem) :=
  let f := ltac2:(lem |- iApplyCapAutoCore (Option.get (Ltac1.to_constr lem))) in
  f lem.



(* iInstr *)

Definition as_weak_addr_incr (a b: Addr) (z: Z) `{AsWeakFinZIncr _ a b z} :=
  (b, Z.to_nat z).

Lemma addr_incr_zero (a: Addr) : (a ^+ 0)%a = a.
Proof. solve_addr. Qed.

Lemma addr_incr_zero_nat (a: Addr) : (a ^+ 0%nat)%a = a.
Proof. solve_addr. Qed.

Ltac iInstr_lookup0 hprog hi hcont :=
  let hprog := constr:(hprog:ident) in
  lazymatch goal with |- context [ Esnoc _ hprog (codefrag ?a_base _) ] =>
  lazymatch goal with |- context [ Esnoc _ ?hpc (PC ↦ᵣ (WCap _ _ _ ?pc_a))%I ] =>
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

Ltac iInstr_get_rule0 hi cont :=
  let hi := constr:(hi:ident) in
  once (
    (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ encodeInstrW ?instr)%I ] => idtac end
     + (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ ?instr)%I ] =>
           fail 1 "Next instruction is not of the form (encodeInstrW _):" instr
         end + fail "" hi "not found"))
  );
  lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ encodeInstrW ?instr)%I ] =>
    dispatch_instr_rule instr cont
  end.

Tactic Notation "iInstr_get_rule" constr(hi) tactic(cont) := iInstr_get_rule0 hi cont.

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
  try wp_instr;
  iInstr_get_rule hi ltac:(fun rule =>
    iApplyCapAuto rule;
    [ .. | iInstr_close hprog; try wp_pure]
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
