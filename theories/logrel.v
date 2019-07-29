From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export lang rules region sts.
From iris.algebra Require Import list frac excl.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, STSG Σ}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ). 
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition read_only_cond b e ws (interp : D) := 
    ([[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, interp w)%I.

  Definition read_write_cond b e (interp : D) := 
    (∃ ws, [[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, (interp w ∗ ⌜isLocalWord w = false⌝))%I.

  Definition read_write_local_cond b e (interp : D) := 
    (∃ ws, [[ b, e ]] ↦ₐ [[ ws ]] ∗ [∗ list] w ∈ ws, interp w)%I. 
  
  Definition exec_cond b e g (P : list Perm) (interp_expr : D) : iProp Σ :=
    (∀ a b' e' p, [[ b', e' ]] ⊂ₐ [[ b, e ]] ∧
                  a ∈ₐ [[ b' , e' ]] ∧
                  (⌜In p P⌝ → ▷ interp_expr (inr ((p,g),b', e',a))))%I. 
    
  Definition enter_cond b e a g (interp_expr : D) : iProp Σ :=
    (▷ interp_expr (inr ((RX,g),b,e,a)))%I. 
  
  (* interp definitions *)
  Definition interp_reg (interp : D) : R :=
    λne (reg : leibnizC Reg), (∀ (r : RegName),
              ⌜is_Some (reg !! r)⌝ ∧ (⌜r ≠ PC⌝ → interp (reg !r! r)))%I. 

  Definition interp_conf (conf : Reg * Mem) fs fr : iProp Σ :=
    (WP Seq (Instr Executable) {{ λne v, ∃ reg fs' fr', registers_mapsto reg ∗ (∀ r, ⌜is_Some (reg !! r)⌝)%I ∗
                                ⌜related_sts fs fs' fr fr'⌝ ∗ sts_full fs' fr' }})%I.

  (* Public future world relation is baked into the definition of interp. 
     After execution, the given state of the STS must respect the future world relation
     given by related_sts. Internally (i.e. when proving WP), the STS may go through 
     arbitrary change: that is it may go through private state transitions *)
  Definition interp_expr (interp : D) : D :=
    λne w, (∀ r m fs fr, interp_reg interp r ∗ registers_mapsto (<[PC:=w]> r)
                                    ∗ sts_full fs fr →
                  ∃ p g b e a, ⌜w = (inr ((p,g),b,e,a))⌝ ∧
                               interp_conf (update_reg (r,m) PC w) fs fr)%I. 
              
  Definition interp_z : D := λne w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : D := λne w, True%I.

  Definition interp_cap_RO (interp : D) : D :=
    λne w, (∃ g b e a ws, ⌜w = inr ((RO,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_only_cond b e ws interp))%I.
  
  Definition interp_cap_RW (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_write_cond b e interp))%I.

  Definition interp_cap_RWL (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_write_local_cond b e interp))%I.
           
  Definition interp_cap_RX (interp : D) : D :=
    λne w, (∃ p g b e a ws, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_only_cond b e ws interp)            
            ∗ □ exec_cond b e g [RX] (interp_expr interp))%I.  

  Definition interp_cap_E (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝
            ∗ □ enter_cond b e a g (interp_expr interp))%I.

  Definition interp_cap_RWX (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_write_cond b e interp)
            ∗ □ exec_cond b e g [RWX;RX] (interp_expr interp))%I.

  Definition interp_cap_RWLX (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗
            inv (logN .@ (b,e)) (read_write_local_cond b e interp)  
            ∗ □ exec_cond b e g [RWX;RX;RWLX] (interp_expr interp))%I.
  
  Definition interp1 (interp : D) : D :=
    λne w,
    match w return _ with
    | inl _ => interp_z w
    | inr ((O, g), b, e, a) => interp_cap_O w
    | inr ((RO, g), b, e, a) => interp_cap_RO interp w
    | inr ((RW, g), b, e, a) => interp_cap_RW interp w
    | inr ((RWL, g), b, e, a) => interp_cap_RWL interp w
    | inr ((RX, g), b, e, a) => interp_cap_RX interp w
    | inr ((E, g), b, e, a) => interp_cap_E interp w
    | inr ((RWX, g), b, e, a) => interp_cap_RWX interp w
    | inr ((RWLX, g), b, e, a) => interp_cap_RWLX interp w
    end.

  (* this takes very long to compile! *)
  Global Instance interp1_contractive : Contractive (interp1).
  Proof. Admitted.
    (* rewrite /interp1 /interp_cap_RO /interp_cap_RW /interp_cap_RWL *)
  (*           /interp_cap_RX /interp_cap_E /interp_cap_RWX /interp_cap_RWLX. *)
  (*   rewrite /read_only_cond /read_write_cond /read_write_local_cond /enter_cond /exec_cond. *)
  (*   solve_contractive. *)
  (* Qed. *)
   
  Lemma fixpoint_interp1_eq (x : leibnizC Word) :
    fixpoint interp1 x ≡ interp1 (fixpoint interp1) x.
  Proof. exact: (fixpoint_unfold (interp1) x). Qed. 

  Program Definition interp : D := λne w, fixpoint interp1 w.
  Program Definition interp_expression : D := interp_expr interp.
  Program Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl. 
         apply _.
         destruct c,p,p,p,p; repeat (apply exist_persistent; intros); try apply _;
           destruct x0; try apply _. 
  Qed. 

  Lemma read_allowed_inv p g b e a :
    readAllowed p → (interp (inr ((p,g),b,e,a)) →
                     (∃ ws, inv (logN .@ (b,e)) (read_only_cond b e ws interp)) ∨
                     inv (logN .@ (b,e)) (read_write_cond b e interp) ∨
                     inv (logN .@ (b,e)) (read_write_local_cond b e interp))%I.
  Proof.
    iIntros (Ra) "Hinterp".
    rewrite /interp. cbn.
    destruct p; cbn; try contradiction; rewrite fixpoint_interp1_eq /=;
     [iDestruct "Hinterp" as (g0 b0 e0 a0 ws) "[% Hinterpr]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% Hinterprw]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% Hinterprwl]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0 ws) "[% [Hinterpr Hinterpe]]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [Hinterprw Hinterpe]]" |
      iDestruct "Hinterp" as (p g0 b0 e0 a0) "[% [Hinterprwl Hinterpe]]" ];
    inversion H2; subst;
      [iLeft|iRight;iLeft|iRight;iRight|iLeft|iRight;iLeft|iRight;iRight]; 
      try iExists ws; iFrame. 
  Qed.
  
End logrel.

Notation "⟦ w ⟧" := (interp w).
Notation "⟦ w ⟧ₑ" := (interp_expression w).
Notation "⟦ r ⟧ᵣ" := (interp_registers r).
Notation "⟦ conf ⟧ₒ" := (interp_conf conf). 