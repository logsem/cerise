From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export lang rules region sts.
From iris.algebra Require Import list frac excl.
From iris.base_logic Require Export invariants na_invariants.
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
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            MonPerm: MonRefG (leibnizO _) PermFlows Σ}.
  Notation STS := (prodO (leibnizO STS_states) (leibnizO STS_rels)).
  Notation D := (STS -n> (leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Notation NS := (leibnizO coPset).
  Notation P := (leibnizO Perm). 
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (NS -n> D). 
  Implicit Types stsf : (prodO (leibnizO STS_states) (leibnizO STS_rels)).
  
  (* -------------------------------------------------------------------------------- *)
  
  Definition related_sts_l stsf stsf' g : iProp Σ :=
    (match g with
    | Global => ⌜related_sts_priv stsf.1 stsf'.1 stsf.2 stsf'.2⌝
    | Local => ⌜related_sts_pub stsf.1 stsf'.1 stsf.2 stsf'.2⌝
    end)%I. 
  
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition read_write_cond l p (interp : NS -n> D) : iProp Σ :=
    (∃ w, l ↦ₐ[p] w ∗ ∀ stsf E, ▷ interp E stsf w)%I.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) read_write_cond.
  Proof. unfold read_write_cond. solve_proper. Qed.

  Definition exec_cond b e g p (stsf : STS)
             (interp_expr : D) : iProp Σ :=
    (∀ a stsf', ⌜a ∈ₐ [[ b , e ]]⌝ →
                related_sts_l stsf stsf' g →
                ▷ interp_expr stsf' (inr ((p,g),b, e,a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond. 
  Proof. unfold exec_cond. solve_proper. Qed. 
    
  Definition enter_cond b e a g (stsf : STS)
             (interp_expr : D) : iProp Σ :=
    (∀ stsf', related_sts_l stsf stsf' g →
              ▷ interp_expr stsf' (inr ((RX,g),b,e,a)))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond. 
  Proof. unfold enter_cond. solve_proper. Qed.
  
  (* interp definitions *)
  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Definition interp_reg (interp : NS -n> D) stsf E : R :=
   λne (reg : leibnizO Reg), (full_map reg ∧ 
       ∀ (r : RegName), (⌜r ≠ PC⌝ → interp E stsf (reg !r! r)))%I.

  Definition interp_conf fs fr E : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r fs' fr', full_map r ∧ registers_mapsto r
                                      ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                      ∗ na_own logrel_nais E                           
                                      ∗ sts_full fs' fr' }})%I.

  Definition namespace_incl (w : Word) (E : coPset) : Prop :=
    match w with
    | inl _ => False
    | inr ((_,_),b,e,_) => ∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E
    end. 
  Program Definition interp_expr (interp : NS -n> D) (E : coPset) r : D :=
    (λne stsf w, ∃ fs fr, ⌜fs = stsf.1⌝
                         ∧ ⌜fr = stsf.2⌝ ∧
                     (interp_reg interp stsf E r ∗ registers_mapsto (<[PC:=w]> r)
                      ∗ sts_full fs fr
                      ∗ na_own logrel_nais E
                      ∗ ⌜namespace_incl w E⌝ -∗
                  ∃ p g b e a, ⌜w = (inr ((p,g),b,e,a))⌝ ∧
                               interp_conf fs fr E))%I.
  Solve Obligations with solve_proper.  

  Definition interp_z : (NS -n> D) := λne E stsf w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : (NS -n> D) := λne E stsf w, True%I.

  Program Definition interp_cap_RO (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RO,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RO p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                        (read_write_cond a p interp))%I.

  Program Definition interp_cap_RW (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RW,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RW p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                      (read_write_cond a p interp))%I. 
  
  Program Definition interp_cap_RWL (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RWL,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RWL p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                 (read_write_cond a p interp))%I. 
           
  Program Definition interp_cap_RX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RX,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                         (read_write_cond a p interp)) 
            ∗ ∀ E' r, □ exec_cond b e g RX stsf (interp_expr (interp) E' r))%I.  
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_E (interp : NS -n> D) : (NS -n> D) :=
    λne _ stsf w, (∃ g b e a, ⌜w = inr ((E,g),b,e,a)⌝
            ∗ ∀ E' r, □ enter_cond b e a g stsf (interp_expr interp E' r))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RWX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RWX,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RWX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                      (read_write_cond a p interp))
            ∗ ∀ E' r, □ exec_cond b e g RWX stsf (interp_expr interp E' r))%I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_cap_RWLX (interp : NS -n> D) : (NS -n> D) :=
    λne E stsf w, (∃ g b e a, ⌜w = inr ((RWLX,g),b,e,a)⌝ ∗
            ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ ∗
            ∃ p, ⌜PermFlows RWLX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), na_inv logrel_nais (logN .@ a)
                                                 (read_write_cond a p interp))
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
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
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
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
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
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
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
    - solve_proper_prepare.
      rewrite /na_inv. 
      solve_contractive.
    - solve_proper_prepare.
      rewrite /na_inv. 
      solve_contractive.
    - solve_proper_prepare.
      rewrite /na_inv. 
      solve_contractive.
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

  
  Lemma fixpoint_interp1_eq (E : NS) (stsf : STS) (x : leibnizO Word) :
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

  Lemma read_allowed_inv (a' a b e: Addr) p g E stsf :
    (b ≤ a' ∧ a' ≤ e)%Z →
    readAllowed p → (interp E stsf (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ na_inv logrel_nais (logN .@ a') (read_write_cond a' p' interp)) ∧
      ⌜∀ (a' : Addr), (b ≤ a' ∧ a' ≤ e)%Z → ↑logN.@a' ⊆ E⌝ )%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn.
    destruct p; cbn; try contradiction; rewrite fixpoint_interp1_eq /=; 
     [iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp] ]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp] ]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp] ]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp]]" | 
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp]]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% [% Hinterp]]" ];
    iDestruct "Hinterp" as (p) "[Hleast Hinterp]";
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); 
    inversion H3; subst; iSplit;auto; iExists _; iFrame; 
      try (iDestruct (extract_from_region_inv_2 with "Hinterp") as (w) "[Hinv _]";
           eauto); 
      try (iDestruct (extract_from_region_inv with "Hinterp") as "Hinv"; eauto).
  Qed.
  
End logrel.

Notation "⟦ w ⟧" := (λ E stsf, interp E stsf w).
Notation "⟦ w ⟧ₑ" := (λ stsf E r, interp_expression E r stsf w).
Notation "⟦ r ⟧ᵣ" := (λ E stsf, interp_registers E stsf r).
Notation "⟦ [ s , r , E ] ⟧ₒ" := (interp_conf s r E). 