From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region region_invariants.
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
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
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
                   ∗ sts_full_world W'
                   ∗ region W' }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne W w, (interp_reg interp W r ∗ registers_mapsto (<[PC:=w]> r)
                                     ∗ region W
                                     ∗ sts_full_world W
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
    (std W) !! a = Some Temporary.

  Definition region_state_nwl W (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std W) !! a = Some Temporary
               ∨ (std W) !! a = Some Permanent
    | Global => (std W) !! a = Some Permanent
    end.

  Definition region_state_U W (a : Addr) : Prop :=
    (std W) !! a = Some Temporary
    \/ (std W) !! a = Some Permanent
    ∨ (exists w, (std W) !! a = Some (Static {[a:=w]})).

  Definition region_state_U_pwl W (a : Addr) : Prop :=
    (std W) !! a = Some Temporary
    ∨ (exists w, (std W) !! a = Some (Static {[a:=w]})).

  (* For simplicity we might want to have the following statement in valididy of caps. However, it is strictly not
     necessary since it can be derived form full_sts_world *)
  (* Definition region_std W (a : Addr) : Prop := rel_is_std_i W (countable.encode a). *)

  Program Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | inr ((RO,g),b,e,a) =>
                [∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RO p⌝ ∗ (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.
     

  Program Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | inr ((RW,g),b,e,a) =>
                [∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RW p⌝ ∗ (read_write_cond a p interp) ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | inr ((RWL,Local),b,e,a) =>
                      [∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RWL p⌝ ∗ (read_write_cond a p interp) ∧ ⌜region_state_pwl W a⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with inr ((RX,g),b,e,a) =>
                           ([∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RX p⌝ ∗ (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝)
                                 (* ∗ □ exec_cond W b e g RX interp *)
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | inr ((E,g),b,e,a) => □ enter_cond W b e a g interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with inr ((RWX,g),b,e,a) =>
                           ([∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RWX p⌝ ∗ (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_nwl W a g⌝)
                                 (* ∗ □ exec_cond W b e g RWX interp *)
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with inr ((RWLX,Local),b,e,a) =>
                           ([∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RWLX p⌝ ∗ (read_write_cond a p interp)
                                                                   ∧ ⌜region_state_pwl W a⌝)
                                 (* ∗ □ exec_cond W b e Local RWLX interp *)
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_URW (interp : D) : D :=
    λne W w, (match w with
              | inr ((URW,Local),b,e,a) =>
                ([∗ list] a' ∈ (region_addrs b (min a e)), ∃ p, ⌜PermFlows (promote_perm URW) p⌝ ∗ (read_write_cond a' p interp)
                                                                 ∧ ⌜region_state_nwl W a' Local⌝) ∗
                ([∗ list] a' ∈ (region_addrs (max b a) e), ∃ p, ⌜PermFlows (promote_perm URW) p⌝ ∗ (read_write_cond a' p interp) ∧ ⌜region_state_U W a'⌝)
              | inr ((URW,Global),b,e,a) =>
                [∗ list] a' ∈ (region_addrs b e), ∃ p, ⌜PermFlows (promote_perm URW) p⌝ ∗ (read_write_cond a' p interp) ∧ ⌜region_state_nwl W a' Global⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.
  
  Program Definition interp_cap_URWL (interp : D) : D :=
    λne W w, (match w with
              | inr ((URWL,Local),b,e,a) =>
                ([∗ list] a' ∈ (region_addrs b (min a e)), ∃ p, ⌜PermFlows (promote_perm URWL) p⌝ ∗ (read_write_cond a' p interp)
                                                                 ∧ ⌜region_state_pwl W a'⌝) ∗
                ([∗ list] a' ∈ (region_addrs (max b a) e), ∃ p, ⌜PermFlows (promote_perm URWL) p⌝ ∗ (read_write_cond a' p interp) ∧
                                                                 ⌜region_state_U_pwl W a'⌝)
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_URWX (interp : D) : D :=
    λne W w, (match w with
              | inr ((URWX,Local),b,e,a) =>
                ([∗ list] a' ∈ (region_addrs b (min a e)), ∃ p, ⌜PermFlows (promote_perm URWX) p⌝ ∗ (read_write_cond a' p interp)
                                                                 ∧ ⌜region_state_nwl W a' Local⌝)
                      (* ∗ □ exec_cond W b (min a e) Local RWX interp *)
               ∗ ([∗ list] a' ∈ (region_addrs (max b a) e), ∃ p, ⌜PermFlows (promote_perm URWX) p⌝ ∗ (read_write_cond a' p interp)
                                                                   ∧ ⌜region_state_U W a'⌝)
              | inr ((URWX,Global),b,e,a) =>
                ([∗ list] a' ∈ (region_addrs b e), ∃ p, ⌜PermFlows (promote_perm URWX) p⌝ ∗ (read_write_cond a' p interp)
                                                                 ∧ ⌜region_state_nwl W a' Global⌝)
                      (* ∗ □ exec_cond W b e Global RWX interp *)
             | _ => False end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_URWLX (interp : D) : D :=
    λne W w, (match w with
              | inr ((URWLX,Local),b,e,a) =>
                ([∗ list] a' ∈ (region_addrs b (min a e)), ∃ p, ⌜PermFlows (promote_perm URWLX) p⌝ ∗ (read_write_cond a' p interp)
                                                                 ∧ ⌜region_state_pwl W a'⌝)
                      (* ∗ □ exec_cond W b (min a e) Local RWLX interp *)
                ∗ ([∗ list] a' ∈ (region_addrs (max b a) e), ∃ p, ⌜PermFlows (promote_perm URWLX) p⌝ ∗ (read_write_cond a' p interp) ∧
                                                                   ⌜region_state_U_pwl W a'⌝)
             | _ => False end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp1 (interp : D) : D :=
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
    | inr ((URW, g), b, e, a) => interp_cap_URW interp W w
    | inr ((URWL, g), b, e, a) => interp_cap_URWL interp W w
    | inr ((URWLX, g), b, e, a) => interp_cap_URWLX interp W w
    | inr ((URWX, g), b, e, a) => interp_cap_URWX interp W w
    end)%I.
  Solve All Obligations with solve_proper.

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
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne; auto.
         apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare. destruct x1; auto. destruct c, p, p, p, p; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct c, p, p, p, p, l; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
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
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. (* apply sep_ne; auto. *)
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    (* - solve_proper_prepare. *)
    (*   by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. *)
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
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. (* apply sep_ne. *)
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    (* - solve_proper_prepare. *)
    (*   by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. *)
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct c, p, p, p, p, l; auto.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. (* apply sep_ne. *)
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    (* - solve_proper_prepare. *)
    (*   by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. *)
  Qed.
  Global Instance interp_cap_URW_contractive :
    Contractive (interp_cap_URW).
  Proof. solve_proper_prepare. destruct x1; auto. destruct_cap c; destruct c; destruct c3; auto.
         - apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
           apply exist_ne. rewrite /pointwise_relation; intros.
           apply sep_ne; auto.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
           simpl. f_equiv. solve_contractive.
         - apply sep_ne; auto.
           apply big_opL_ne; auto; rewrite /pointwise_relation; intros.
           apply exist_ne. rewrite /pointwise_relation; intros.
           apply sep_ne; auto.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
           simpl. f_equiv. solve_contractive.
           apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply exist_ne. rewrite /pointwise_relation; intros.
           apply sep_ne; auto.
           apply and_ne; auto. apply exist_ne => γ. apply sep_ne; auto.
           simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWL_contractive :
    Contractive (interp_cap_URWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct_cap c. destruct c; auto. destruct c3; auto.
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto. rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto. 
         apply and_ne; auto. apply exist_ne => γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWX_contractive :
    Contractive (interp_cap_URWX).
  Proof.
    rewrite /interp_cap_URWX.
    solve_proper_prepare.
    destruct x1; auto. destruct_cap c; destruct c; destruct c3; auto.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto.
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    - apply sep_ne; auto.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        apply exist_ne. rewrite /pointwise_relation; intros.
        apply sep_ne; auto.
        rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply and_ne; auto. apply exist_ne =>γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        apply exist_ne. rewrite /pointwise_relation; intros.
        apply sep_ne; auto. 
        rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply and_ne; auto. apply exist_ne => γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWLX_contractive :
    Contractive (interp_cap_URWLX).
  Proof.
    rewrite /interp_cap_URWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct_cap c; destruct c; auto. destruct c3; auto.
    apply sep_ne.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ?.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. 
      apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
    - apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
      apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. 
      rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply and_ne; auto. apply exist_ne => γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
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
    - by apply interp_cap_URW_contractive.
    - by apply interp_cap_URWL_contractive.
    - by apply interp_cap_URWX_contractive.
    - by apply interp_cap_URWLX_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (W : WORLD) (x : leibnizO Word) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x.
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Program Definition interp : D :=
    λne W w, (fixpoint (interp1)) W w.
  Solve All Obligations with solve_proper.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp W w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _.
         destruct c,p,p,p,p; destruct l; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Instance ne_interpC : NonExpansive
                           (λ Wv : (WORLD * (leibnizO Word)), (interp Wv.1) Wv.2).
  Proof. intros. solve_proper. Qed.

  (* Non-curried version of interp *)
  Definition interpC :=
    (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).

  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p → (interp W (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a' p' interp)))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try contradiction;
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    try (iDestruct (extract_from_region_inv with "Hinterp") as (p Hflows) "[Hinv _]"; [eauto|iExists _;iSplit;eauto]).
    - done.
    - done.
  Qed.
  
  Lemma writeLocalAllowed_implies_local W p l b e a:
    pwl p = true ->
    interp W (inr (p, l, b, e, a)) -∗ ⌜isLocal l = true⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H; try congruence; destruct l; eauto.
  Qed.

  Lemma readAllowed_valid_cap_implies W p l b e a:
    readAllowed p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a)) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ g, ρ ≠ Static g)⌝.
  Proof.
    intros Hp Hb. iIntros "H".
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence.
    - iDestruct (extract_from_region_inv with "H") as (p ?) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH; eauto.
    - iDestruct (extract_from_region_inv with "H") as (p ?) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH; eauto.
    - destruct l; auto.
      iDestruct (extract_from_region_inv with "H") as (p ?) "[_ %]"; eauto.
    - iDestruct (extract_from_region_inv with "H") as (p ?) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH; eauto.
    - iDestruct (extract_from_region_inv with "H") as (p ?) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH; eauto.
    - destruct l;auto.
      iDestruct (extract_from_region_inv with "H") as (p ?) "[_ %]"; eauto.
  Qed.

  Definition region_conditions W p g b e:=
  ([∗ list] a ∈ (region_addrs b e), ∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a p' interp)
                                             ∧ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝)%I.

  Lemma readAllowed_implies_region_conditions W p l b e a:
    readAllowed p = true ->
    interp W (inr (p, l, b, e, a)) -∗ region_conditions W p l b e.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    unfold region_conditions.
    destruct p; simpl in *; try congruence; destruct l; simpl; auto.
  Qed.


  Lemma writeLocalAllowed_valid_cap_implies W p l b e a:
    pwl p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a)) -∗
           ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hvalid".
    iAssert (⌜isLocal l = true⌝)%I as "%". by iApply writeLocalAllowed_implies_local.
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence; destruct l.
    - by exfalso.
    - iDestruct (extract_from_region_inv with "Hvalid") as (? ?) "[_ %]"; eauto.
    - by exfalso.
    - iDestruct (extract_from_region_inv with "Hvalid") as (? ?) "[_ %]"; eauto.
  Qed.

  Lemma interp1_eq interp (W: WORLD) p l b e a:
    ((interp1 interp W (inr (p, l, b, e, a))) ≡
             (if perm_eq_dec p O then True else
             if perm_eq_dec p E then □ enter_cond W b e a l interp else
               ([∗ list] a ∈ region_addrs b (if isU p && isLocal l then (min a e) else e),
                ∃ p', ⌜PermFlows (promote_perm p) p'⌝ ∗
                 (read_write_cond a p' interp) ∧
                 ⌜if pwlU p then region_state_pwl W a else region_state_nwl W a l⌝) ∗
                (*(□ match p with RX | RWX | RWLX => exec_cond W b e l p interp | URWX | URWLX => exec_cond W b (if isLocal l then min a e else e) l (promote_perm p) interp | _ => True end) ∗*)
                (⌜if pwlU p then l = Local else True⌝) ∗
                (if isU p && isLocal l then [∗ list] a ∈ region_addrs (max b a) e,
                                            ∃ p', ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a p' interp ∧ ⌜if pwlU p then region_state_U_pwl W a else region_state_U W a⌝ else emp%I))%I).
  Proof.
    iSplit.
    { iIntros "HA".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      destruct p; simpl; try congruence; auto; destruct l;auto. 
      - iDestruct "HA" as "[HA HB]"; eauto.
      - iDestruct "HA" as "[HA HB]"; eauto.
      - iDestruct "HA" as "[Ha HB]"; eauto.
      - iDestruct "HA" as "[HB HC]"; eauto. }
    { iIntros "A".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      iDestruct "A" as "(B & % & C)".
      destruct p; simpl in *; try congruence; subst; eauto; destruct l; eauto. }
  Qed.

End logrel.

(* Notation "𝕍( W )" := (interp W) (at level 70). *)
(* Notation "𝔼( W )" := (λ r, interp_expression r W). *)
(* Notation "ℝ( W )" := (interp_registers W). *)
(* Notation "𝕆( W )" := (interp_conf W.1 W.2).  *)
