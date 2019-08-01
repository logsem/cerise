From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants na_invariants.
From cap_machine Require Export lang rules region sts.
From iris.algebra Require Import list frac excl.
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
    logrel_nais : na_inv_pool_name
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Notation STS := (prodC (leibnizC STS_states) (prodC (leibnizC STS_rels)
                                                      (leibnizC STS_rels))).
  Notation D := (STS -n> (leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Notation NS := (leibnizC coPset).  
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : (NS -n> D). 
  Implicit Types stsf : (prodC (leibnizC STS_states) (prodC (leibnizC STS_rels)
                                                      (leibnizC STS_rels))).
  
  (* -------------------------------------------------------------------------------- *)
  
  Definition related_sts_l fs fs' fr_pub fr_pub' fr_priv fr_priv' g : iProp Σ :=
    (match g with
    | Global => ⌜related_sts fs fs' fr_priv fr_priv'⌝
    | Local => ⌜related_sts fs fs' fr_pub fr_pub'⌝
    end)%I. 
  
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition read_only_cond b e ws stsf E (interp : NS -n> D) := 
    ([[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, ▷ interp E stsf w)%I.
  Global Instance read_only_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) read_only_cond. 
  Proof. unfold read_only_cond. solve_proper. Qed.
  
  Definition read_write_cond b e stsf E (interp : NS -n> D) := 
    (∃ ws, [[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, ▷ (interp E stsf w
                                                          ∗ ⌜isLocalWord w = false⌝))%I.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) read_write_cond. 
  Proof. unfold read_write_cond. solve_proper. Qed. 

  Definition read_write_local_cond b e stsf E (interp : NS -n> D) := 
    (∃ ws, [[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, ▷ interp E stsf w)%I. 
  Global Instance read_write_local_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) read_write_local_cond. 
  Proof. unfold read_write_local_cond. solve_proper. Qed. 
  
  Definition exec_cond b e g p (stsf : STS)
             (interp_expr : D) : iProp Σ :=
    (∀ a fs' fr_pub' fr_priv', 
                  ⌜a ∈ₐ [[ b , e ]]⌝ →
                  related_sts_l stsf.1 fs' stsf.2.1 fr_pub' stsf.2.2 fr_priv' g →
                  ▷ interp_expr (fs',(fr_pub',fr_priv')) (inr ((p,g),b, e,a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond. 
  Proof. unfold exec_cond. solve_proper. Qed. 
    
  Definition enter_cond b e a g (stsf : STS)
             (interp_expr : D) : iProp Σ :=
    (∀ fs' fr_pub' fr_priv',
      related_sts_l stsf.1 fs' stsf.2.1 fr_pub' stsf.2.2 fr_priv' g →
      ▷ interp_expr (fs',(fr_pub',fr_priv')) (inr ((RX,g),b,e,a)))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond. 
  Proof. unfold enter_cond. solve_proper. Qed.
  
  (* interp definitions *)
  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Definition interp_reg (interp : NS -n> D) stsf E : R :=
   λne (reg : leibnizC Reg), (full_map reg ∧ 
       ∀ (r : RegName), (⌜r ≠ PC⌝ → interp E stsf (reg !r! r)))%I.

  Definition interp_conf fs fr_priv E : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r fs' fr_pub' fr_priv', full_map r ∧ registers_mapsto r
                                      ∗ ⌜related_sts fs fs' fr_priv fr_priv'⌝
                                      ∗ na_own logrel_nais E                           
                                      ∗ sts_full fs' fr_pub' fr_priv' }})%I.

  Definition get_namespace (w : Word) : option namespace :=
    match w with
    | inl _ => None
    | inr ((_,_),b,e,_) => Some (logN.@(b, e))
    end. 
  Program Definition interp_expr (interp : NS -n> D) (E : coPset) r : D :=
    (λne stsf w, ∃ fs fr_pub fr_priv, ⌜fs = stsf.1⌝
                         ∧ ⌜fr_pub = stsf.2.1⌝
                         ∧ ⌜fr_priv = stsf.2.2⌝ ∧
                     (interp_reg interp stsf E r ∗ registers_mapsto (<[PC:=w]> r)
                      ∗ sts_full fs fr_pub fr_priv
                      ∗ na_own logrel_nais E
                      ∗ (⌜∀ ns, get_namespace w = Some ns → ↑ns ⊆ E⌝) →
                  ∃ p g b e a, ⌜w = (inr ((p,g),b,e,a))⌝ ∧
                               interp_conf fs fr_priv E))%I.
  Solve Obligations with solve_proper.  

  Definition interp_z : (NS -n> D) := λne E stsf w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : (NS -n> D) := λne E stsf w, True%I.

  Program Definition interp_cap_RO (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a ws, ⌜w = inr ((RO,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws stsf E interp))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RW (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e stsf E interp))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RWL (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e stsf E interp))%I.
  Solve Obligations with solve_proper.
           
  Program Definition interp_cap_RX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ p g b e a ws, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws stsf E interp)
            ∗ ∀ E' r, □ exec_cond b e g RX stsf (interp_expr (interp) E' r))%I.  
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_E (interp : NS -n> D) : (NS -n> D) :=
    λne _ stsf w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝
            ∗ ∀ E' r, □ enter_cond b e a g stsf (interp_expr interp E' r))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RWX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e stsf E interp)
            ∗ ∀ E' r, □ exec_cond b e g RWX stsf (interp_expr interp E' r))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RWLX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            ⌜↑logN.@(b,e) ⊆ E⌝ ∗
            na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e stsf E interp)   
            ∗ ∀ E' r, □ exec_cond b e g RWLX stsf (interp_expr interp E' r))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp1 (interp : NS -n> D) : (NS -n> D) :=
    (λne E stsf w,
    match w return _ with
    | inl _ => interp_z E stsf w
    | inr ((O, g), b, e, a) => interp_cap_O E stsf w
    | inr ((RO, g), b, e, a) => interp_cap_RO interp E stsf w
    | inr ((RW, g), b, e, a) => interp_cap_RW interp E stsf w
    | inr ((RWL, g), b, e, a) => interp_cap_RWL interp E stsf w
    | inr ((RX, g), b, e, a) => interp_cap_RX interp E stsf w
    | inr ((E, g), b, e, a) => interp_cap_E interp E stsf w
    | inr ((RWLX, g), b, e, a) => interp_cap_RWLX interp E stsf w
    | inr ((RWX, g), b, e, a) => interp_cap_RWX interp E stsf w
    end)%I.
  Solve Obligations with solve_proper.

  (* Global Instance interp_expr_contractive : *)
  (*   Contractive (interp_expr). *)
  (* Proof. solve_contractive. Qed.  *)
  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof. solve_proper_prepare.
         rewrite /na_inv. 
         solve_contractive. Qed. 
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare.
         rewrite /na_inv.
         solve_contractive. Qed. 
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         rewrite /na_inv.
         solve_contractive. Qed. 
  Global Instance exec_cond_contractive b e g pl s E r:
    Contractive (λ interp, exec_cond b e g pl s (interp_expr interp E r)).
  Proof. 
    solve_proper_prepare.
    repeat (apply forall_ne; rewrite /pointwise_relation; intros).
    repeat (apply impl_ne; [auto|]).
    solve_contractive. 
  Qed.
  Global Instance enter_cond_contractive b e a g s E r :
    Contractive (λ interp, enter_cond b e a g s (interp_expr interp E r)). 
  Proof.
    solve_proper_prepare. 
    repeat (apply forall_ne; rewrite /pointwise_relation; intros).
    apply impl_ne; [auto|].  
    solve_contractive.
  Qed. 
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof. 
    rewrite /interp_cap_RX.
    solve_proper_prepare. 
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    do 2 (apply sep_ne; [auto|]).
    apply sep_ne. 
    - rewrite /na_inv. 
      solve_contractive. 
    - do 2 (f_equiv; intros; rewrite /pointwise_relation; intros).
      f_equiv. by apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    rewrite /interp_cap_E.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation;intros).
    apply sep_ne;[auto|].
    do 2 (f_equiv;rewrite /pointwise_relation; intros).
    f_equiv. by apply enter_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    rewrite /interp_cap_RWX.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    do 2 (apply sep_ne;[auto|]).
    apply sep_ne.
    - rewrite /na_inv. solve_contractive.  
    - do 2 (f_equiv;rewrite /pointwise_relation; intros).
      f_equiv. by apply exec_cond_contractive.
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    do 2 (apply sep_ne;[auto|]).
    apply sep_ne.
    - rewrite /na_inv. 
      solve_contractive.
    - do 2 (f_equiv; rewrite /pointwise_relation; intros).
      f_equiv. by apply exec_cond_contractive. 
  Qed.     
    
  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    solve_proper_prepare.
    destruct x2;[auto|].
    destruct c,p,p,p,p; first auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RWL_contractive.
    - by apply interp_cap_RX_contractive.    
    - rewrite /interp_cap_E.
      solve_proper_prepare.
      repeat (apply exist_ne; rewrite /pointwise_relation;intros).
      apply sep_ne;[auto|].
      do 2 (f_equiv;rewrite /pointwise_relation; intros).
      f_equiv. by apply enter_cond_contractive. 
    - by apply interp_cap_RWX_contractive.
    - by apply interp_cap_RWLX_contractive.
  Qed. 

  
  Lemma fixpoint_interp1_eq (E : NS) (stsf : STS) (x : leibnizC Word) :
    fixpoint (interp1) E stsf x ≡ interp1 (fixpoint (interp1)) E stsf x. 
  Proof. exact: (fixpoint_unfold (interp1) E stsf x). Qed.
    
  Program Definition interp : (NS -n> D) :=
    λne E stsf w, (fixpoint (interp1)) E stsf w.
  Solve Obligations with solve_proper.
  Program Definition interp_expression E r : D := interp_expr interp E r.
  Program Definition interp_registers E stsf : R := interp_reg interp stsf E.

  Global Instance interp_persistent : Persistent (interp E' stsf w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl. 
         apply _.
         destruct c,p,p,p,p; repeat (apply exist_persistent; intros); try apply _;
           destruct x0; try apply _. 
  Qed. 

  Lemma read_allowed_inv p g b e a E stsf :
    readAllowed p → (interp E stsf (inr ((p,g),b,e,a)) →
      ((∃ ws, na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws stsf E interp)) ∨
      na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e stsf E interp) ∨
      na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e stsf E interp)) ∧
      ⌜↑logN.@(b,e) ⊆ E⌝ )%I.
  Proof.
    iIntros (Ra) "Hinterp".
    rewrite /interp. cbn.
    destruct p; cbn; try contradiction; rewrite fixpoint_interp1_eq /=;
     [iDestruct "Hinterp" as (g0 b0 e0 a0 ws) "[% [% Hinterpr] ]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [% Hinterprw] ]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [% Hinterprwl] ]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0 ws) "[% [% [Hinterpr Hinterpe]]]" | 
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [% [Hinterprw Hinterpe]]]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [% [Hinterprwl Hinterpe]]]" ];
    inversion H3; subst; iSplit; auto.
  Qed.
  
End logrel.

Notation "⟦ w ⟧" := (λ E stsf, interp E stsf w).
Notation "⟦ w ⟧ₑ" := (λ stsf E r, interp_expression E r stsf w).
Notation "⟦ r ⟧ᵣ" := (λ E stsf, interp_registers E stsf r).
Notation "⟦ [ s , r , E ] ⟧ₒ" := (interp_conf s r E). 