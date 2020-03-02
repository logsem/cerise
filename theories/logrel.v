From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export lang region region_invariants.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

Class logrel_na_invs Σ :=
  {
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name;
    wγ : gname
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
   λne (W : WORLD) (reg : leibnizO Reg), (full_map reg ∧
                                          ∀ (r : RegName), (⌜r ≠ PC⌝ → interp W (reg !r! r)))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf W : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r W', full_map r ∧ registers_mapsto r
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world sts_std W'
                   ∗ region W' }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne W w, (interp_reg interp W r ∗ registers_mapsto (<[PC:=w]> r)
                                     ∗ region W
                                     ∗ sts_full_world sts_std W
                                     ∗ na_own logrel_nais ⊤ -∗
                                     ⌜match w with inr _ => True | _ => False end⌝ ∧ interp_conf W))%I.
  Solve All Obligations with solve_proper.

  (* condition definitions *)
  Program Definition read_write_cond l p (interp : D) : iProp Σ :=
    rel l p (λne Wv, interp Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) read_write_cond.
  Proof.
    rewrite /read_write_cond rel_eq /rel. solve_proper_prepare.
    f_equiv =>γ. f_equiv.
    apply saved_anything_ne.
    solve_proper.
  Qed.

  Definition future_world g W W' : iProp Σ :=
    (match g with
    | Local => ⌜related_sts_pub_world W W'⌝
    | Global => ⌜related_sts_priv_world W W'⌝
     end)%I.

  Global Instance future_world_persistent g W W': Persistent (future_world g W W').
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.

  Definition exec_cond W b e g p (interp : D) : iProp Σ :=
    (∀ a r W', ⌜a ∈ₐ [[ b , e ]]⌝ → future_world g W W' →
            ▷ interp_expr interp r W' (inr ((p,g),b, e,a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof. unfold exec_cond. solve_proper. Qed.

  Definition enter_cond W b e a g (interp : D) : iProp Σ :=
    (∀ r W', future_world g W W' →
        ▷ interp_expr interp r W' (inr ((RX,g),b,e,a)))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. unfold enter_cond. solve_proper. Qed.

  (* interp definitions *)
  Definition interp_z : D := λne _ w, ⌜match w with inl z => True | _ => False end⌝%I.

  Definition interp_cap_O : D := λne _ _, True%I.

  Definition region_state_pwl W (a : Addr) : Prop :=
    (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary).

  Definition region_state_nwl W (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)
               ∨ (std_sta W) !! (countable.encode a) = Some (countable.encode Permanent)
    | Global => (std_sta W) !! (countable.encode a) = Some (countable.encode Permanent)
    end.

  (* For simplicity we might want to have the following statement in valididy of caps. However, it is strictly not
     necessary since it can be derived form full_sts_world *)
  Definition region_std W (a : Addr) : Prop := rel_is_std_i W (countable.encode a).

  Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | inr ((RO,g),b,e,a) =>
                ∃ p, ⌜PermFlows RO p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.

  Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | inr ((RW,g),b,e,a) =>
                ∃ p, ⌜PermFlows RW p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.

  Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | inr ((RWL,Local),b,e,a) =>
                ∃ p, ⌜PermFlows RWL p⌝ ∗
                      [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp) ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝
              | _ => False
              end)%I.

  Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with inr ((RX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝)
                                 ∗ □ exec_cond W b e g RX interp
             | _ => False end)%I.

  Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | inr ((E,g),b,e,a) => □ enter_cond W b e a g interp
              | _ => False
              end)%I.

  Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with inr ((RWX,g),b,e,a) =>
                           ∃ p, ⌜PermFlows RWX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝ ∧ ⌜region_std W a⌝)
                                 ∗ □ exec_cond W b e g RWX interp
             | _ => False end)%I.

  Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with inr ((RWLX,Local),b,e,a) =>
                           ∃ p, ⌜PermFlows RWLX p⌝ ∗
                                 ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_pwl W a⌝ ∧ ⌜region_std W a⌝)
                                 ∗ □ exec_cond W b e Local RWLX interp
             | _ => False end)%I.

  Definition interp1 (interp : D) : D :=
    (λne W w,
    match w return _ with
    | inl _ => interp_z W w
    | inr ((O, g), b, e, a) => interp_cap_O W w
    | inr ((RO, g), b, e, a) => interp_cap_RO interp W w
    | inr ((RW, g), b, e, a) => interp_cap_RW interp W w
    | inr ((RWL, g), b, e, a) => interp_cap_RWL interp W w
    | inr ((RX, g), b, e, a) => interp_cap_RX interp W w
    | inr ((E, g), b, e, a) => interp_cap_E interp W w
    | inr ((RWLX, g), b, e, a) => interp_cap_RWLX interp W w
    | inr ((RWX, g), b, e, a) => interp_cap_RWX interp W w
    end)%I.

  (* Global Instance interp_expr_contractive : *)
  (*   Contractive (interp_expr). *)
  (* Proof. solve_contractive. Qed.  *)
  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne; auto.
         apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare. destruct x1; auto. destruct c, p, p, p, p; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p, l; auto.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance exec_cond_contractive W b e g pl :
    Contractive (λ interp, exec_cond W b e g pl interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance enter_cond_contractive W b e a g :
    Contractive (λ interp, enter_cond W b e a g interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    rewrite /interp_cap_RX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne; auto.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive.
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    rewrite /interp_cap_E.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply enter_cond_contractive.
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    rewrite /interp_cap_RWX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive.
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p, l; auto.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. apply sep_ne.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn W w.
    rewrite /interp1.
    destruct w; [auto|].
    destruct c,p,p,p,p; first auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RWL_contractive.
    - by apply interp_cap_RX_contractive.
    - by apply interp_cap_E_contractive.
    - by apply interp_cap_RWX_contractive.
    - by apply interp_cap_RWLX_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (W : WORLD) (x : leibnizO Word) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x.
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Definition interp : D :=
    λne W w, (fixpoint (interp1)) W w.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp W w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _.
         destruct c,p,p,p,p; destruct l; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Instance ne_interpC : NonExpansive
                           (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), (interp Wv.1) Wv.2).
  Proof. intros. solve_proper. Qed.

  (* Non-curried version of interp *)
  Definition interpC :=
    (λne Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), (interp Wv.1) Wv.2).


  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p → (interp W (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a' p' interp)))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try contradiction;
    try (iDestruct "Hinterp" as (p) "[Hleast Hinterp]");
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    iExists _; iFrame;
    try (iDestruct (extract_from_region_inv_2 with "Hinterp") as (w) "[ [Hinv _] _]"; eauto);
    try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv _]"; eauto).
    - done.
    - done.
      Unshelve. exact RWL. exact RWLX.
  Qed.

  Lemma writeLocalAllowed_implies_local W p l b e a:
    pwl p = true ->
    interp W (inr (p, l, b, e, a)) -∗ ⌜isLocal l = true⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H3; try congruence; destruct l; eauto.
  Qed.

  Lemma readAllowed_valid_cap_implies W p l b e a:
    readAllowed p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a)) -∗
           ⌜region_std W a /\ ∃ ρ, std_sta W !! countable.encode a = Some (countable.encode ρ) /\ ρ <> Revoked⌝.
  Proof.
    intros. iIntros "Hvalid".
    eapply withinBounds_le_addr in H4.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H3; try congruence.
    - iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - destruct l; auto.
      iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
    - iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
      iPureIntro. split; eauto.
      destruct l; simpl in H6; eauto.
      destruct H6; eauto.
    - destruct l; auto.
      iDestruct "Hvalid" as (p) "[% [H H']]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
  Qed.

  Definition region_conditions W p g b e:=
  (∃ p', ⌜PermFlows p p'⌝ ∧
           ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p' interp)
                                             ∧ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
                                             ∧ ⌜region_std W a⌝))%I.

  Lemma readAllowed_implies_region_conditions W p l b e a:
    readAllowed p = true ->
    interp W (inr (p, l, b, e, a)) -∗ region_conditions W p l b e.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    unfold region_conditions.
    destruct p; simpl in H3; try congruence; destruct l; auto.
    all: iDestruct "Hvalid" as (p) "[% Hvalid]"; iExists p; iSplitR; auto.
    all: iDestruct "Hvalid" as "[Hvalid _]"; auto.
  Qed.


  Lemma writeLocalAllowed_valid_cap_implies W p l b e a:
    pwl p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a)) -∗
           ⌜region_std W a /\ std_sta W !! countable.encode a = Some (countable.encode Temporary)⌝.
  Proof.
    intros. iIntros "Hvalid".
    iAssert (⌜isLocal l = true⌝)%I as "%". by iApply writeLocalAllowed_implies_local.
    eapply withinBounds_le_addr in H4.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H3; try congruence; destruct l.
    - by exfalso.
    - iDestruct "Hvalid" as (p) "[% H]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
    - by exfalso.
    - iDestruct "Hvalid" as (p) "[% [H _] ]".
      iDestruct (extract_from_region_inv with "H") as "[_ [% %]]"; eauto.
  Qed.

End logrel.

(* Notation "𝕍( W )" := (interp W) (at level 70). *)
(* Notation "𝔼( W )" := (λ r, interp_expression r W). *)
(* Notation "ℝ( W )" := (interp_registers W). *)
(* Notation "𝕆( W )" := (interp_conf W.1 W.2).  *)
