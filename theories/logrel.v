From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine.rules Require Export rules. 
From cap_machine Require Export lang region.
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
    logrel_nais : na_inv_pool_name;
    wγ : gname
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  
  Notation WORLD_S := (leibnizO ((STS_states * STS_rels) * bool)).
  Implicit Types M : WORLD_S. 
  Implicit Types W : (STS_states * STS_rels). 
  
  (* -------------------------------------------------------------------------------- *)
  
  (* Definition related_sts_l stsf stsf' g : iProp Σ := *)
  (*   (match g with *)
  (*   | Global => ⌜related_sts_priv stsf.1 stsf'.1 stsf.2 stsf'.2⌝ *)
  (*   | Local => ⌜related_sts_pub stsf.1 stsf'.1 stsf.2 stsf'.2⌝ *)
  (*   end)%I.  *)

  (* interp expression definitions *)
  Definition W_toM g W : WORLD_S :=
    (match g with
     | Global => (W,true)
     | Local => (W,false)
     end)%I.
  
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Definition interp_reg (interp : D) : R :=
   λne (reg : leibnizO Reg), (full_map reg ∧ 
       ∀ (r : RegName), (⌜r ≠ PC⌝ → interp (reg !r! r)))%I.

  Definition interp_conf fs fr : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r fs' fr', full_map r ∧ registers_mapsto r
                                      ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                      ∗ na_own logrel_nais ⊤                           
                                      ∗ sts_full fs' fr' }})%I.

  Program Definition interp_expr (interp : D) M r : D :=
    (λne w, ∃ fs fr, ⌜fs = M.1.1⌝
                     ∧ ⌜fr = M.1.2⌝ ∧
                     (interp_reg interp r ∗ registers_mapsto (<[PC:=w]> r)
                      ∗ Exact_w wγ M
                      ∗ sts_full fs fr
                      ∗ na_own logrel_nais ⊤ -∗
                  ∃ p g b e a, ⌜w = (inr ((p,g),b,e,a))⌝ ∧
                               interp_conf fs fr))%I.

  (* condition definitions *)
  Definition read_write_cond l p (interp : D) : iProp Σ :=
    na_inv logrel_nais (logN.@l) (∃ w, l ↦ₐ[p] w ∗ ▷ interp w)%I.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) read_write_cond.
  Proof. unfold read_write_cond. solve_proper. Qed.

  Definition exec_cond b e g p (interp : D) : iProp Σ :=
    (∀ a W r, ⌜a ∈ₐ [[ b , e ]]⌝ →
            ▷ interp_expr interp (W_toM g W) r (inr ((p,g),b, e,a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond. 
  Proof. unfold exec_cond. solve_proper. Qed. 
    
  Definition enter_cond b e a g (interp : D) : iProp Σ :=
    (∀ W r, ▷ interp_expr interp (W_toM g W) r (inr ((RX,g),b,e,a)))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond. 
  Proof. unfold enter_cond. solve_proper. Qed.  
  
  (* interp definitions *)
  Definition interp_z : D := λne w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : D := λne w, True%I.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RO,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RO p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))%I.
  
  Program Definition interp_cap_RW (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RW,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RW p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))%I.
  
  Program Definition interp_cap_RWL (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RWL,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RWL p⌝ ∗
            [∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp))%I.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RX,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
            ∗ □ exec_cond b e g RX interp)%I.  

  Program Definition interp_cap_E (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((E,g),b,e,a)⌝
            ∗ □ enter_cond b e a g interp)%I.
  
  Program Definition interp_cap_RWX (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RWX,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RWX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
            ∗ □ exec_cond b e g RWX interp)%I.
  
  Program Definition interp_cap_RWLX (interp : D) : D :=
    λne w, (∃ g b e a, ⌜w = inr ((RWLX,g),b,e,a)⌝ ∗
            ∃ p, ⌜PermFlows RWLX p⌝ ∗
            ([∗ list] a ∈ (region_addrs b e), (read_write_cond a p interp)) 
            ∗ □ exec_cond b e g RWLX interp)%I.
  
  Program Definition interp1 (interp : D) : D :=
    (λne w,
    match w return _ with
    | inl _ => interp_z w
    | inr ((O, g), b, e, a) => interp_cap_O w
    | inr ((RO, g), b, e, a) => interp_cap_RO interp w
    | inr ((RW, g), b, e, a) => interp_cap_RW interp w
    | inr ((RWL, g), b, e, a) => interp_cap_RWL interp w
    | inr ((RX, g), b, e, a) => interp_cap_RX interp w
    | inr ((E, g), b, e, a) => interp_cap_E interp w
    | inr ((RWLX, g), b, e, a) => interp_cap_RWLX interp w
    | inr ((RWX, g), b, e, a) => interp_cap_RWX interp w
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
         repeat (apply exist_ne; rewrite /pointwise_relation;intros).
         repeat (apply sep_ne;auto).
         apply exist_ne; rewrite /pointwise_relation;intros.
         apply sep_ne; auto. 
         rewrite /read_write_cond. solve_contractive. 
  Qed. 
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare.
         repeat (apply exist_ne; rewrite /pointwise_relation;intros).
         repeat (apply sep_ne;auto).
         apply exist_ne; rewrite /pointwise_relation;intros.
         apply sep_ne; auto.
         rewrite /read_write_cond. solve_contractive.
  Qed. 
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         repeat (apply exist_ne; rewrite /pointwise_relation;intros).
         repeat (apply sep_ne;auto).
         apply exist_ne; rewrite /pointwise_relation;intros.
         apply sep_ne; auto.
         rewrite /read_write_cond. solve_contractive. 
  Qed. 
  Global Instance exec_cond_contractive b e g pl :
    Contractive (λ interp, exec_cond b e g pl interp).
  Proof. 
    solve_contractive. 
  Qed.
  Global Instance enter_cond_contractive b e a g :
    Contractive (λ interp, enter_cond b e a g interp). 
  Proof.
    solve_contractive. 
  Qed. 
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    rewrite /interp_cap_RX.
    solve_proper_prepare. 
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    repeat (apply sep_ne; [auto|]).
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
    apply sep_ne. 
    - rewrite /read_write_cond. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    rewrite /interp_cap_E.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation;intros).
    apply sep_ne;[auto|].
    solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply enter_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    rewrite /interp_cap_RWX.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    repeat (apply sep_ne;[auto|]).
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
    apply sep_ne. 
    - rewrite /read_write_cond. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    repeat (apply sep_ne;[auto|]).
    repeat (apply exist_ne; rewrite /pointwise_relation; intros).
    apply sep_ne;[auto|].
    apply sep_ne. 
    - rewrite /read_write_cond. solve_contractive. 
    - solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. 
  Qed.     
    
  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    solve_proper_prepare.
    destruct x0;[auto|].
    destruct c,p,p,p,p; first auto.
    - solve_proper_prepare.
      rewrite /read_write_cond. solve_contractive. 
    - solve_proper_prepare.
      rewrite /read_write_cond. solve_contractive. 
    - solve_proper_prepare.
      rewrite /read_write_cond. solve_contractive.
    - by apply interp_cap_RX_contractive.    
    - rewrite /interp_cap_E.
      solve_proper_prepare.
      repeat (apply exist_ne; rewrite /pointwise_relation;intros).
      apply sep_ne;[auto|].
      solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply enter_cond_contractive. 
    - by apply interp_cap_RWX_contractive.
    - by apply interp_cap_RWLX_contractive.
  Qed. 

  
  Lemma fixpoint_interp1_eq (x : leibnizO Word) :
    fixpoint (interp1) x ≡ interp1 (fixpoint (interp1)) x. 
  Proof. exact: (fixpoint_unfold (interp1) x). Qed.
    
  Program Definition interp : D :=
    λne w, (fixpoint (interp1)) w.
  Program Definition interp_expression M r : D := interp_expr interp M r.
  Program Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl. 
         apply _. 
         destruct c,p,p,p,p; repeat (apply exist_persistent; intros); try apply _.
  Qed. 

  Lemma read_allowed_inv (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' ≤ e)%Z →
    readAllowed p → (interp (inr ((p,g),b,e,a)) →
      (∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a' p' interp)))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn.
    destruct p; cbn; try contradiction; rewrite fixpoint_interp1_eq /=; 
     [iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" | 
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" |
      iDestruct "Hinterp" as (g0 b0 e0 a0) "[% Hinterp]" ];
    iDestruct "Hinterp" as (p) "[Hleast Hinterp]";
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); 
    inversion H3; subst; iExists _; iFrame; 
      try (iDestruct (extract_from_region_inv_2 with "Hinterp") as (w) "[Hinv _]";
           eauto); 
      try (iDestruct (extract_from_region_inv with "Hinterp") as "Hinv"; eauto). 
  Qed.
  
End logrel.

Notation "⟦ w ⟧" := (interp w).
Notation "⟦ w ⟧ₑ" := (λ M r, interp_expression M r w).
Notation "⟦ r ⟧ᵣ" := (interp_registers r).
Notation "⟦ [ s , r ] ⟧ₒ" := (interp_conf s r). 