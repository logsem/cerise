From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export lang rules region.
From iris.algebra Require Import list frac excl.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, inG Σ fracR}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ). 
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  (* capability conditions *)
  Definition read_cond (b e : Addr) (g : Locality) (γ : gname) (interp : D) : iProp Σ := 
    match g with
    | Local => inv_cap T (∃ ws, {[ b, e ]} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, interp w)%I
                        (logN .@ (b,e)) γ
    | Global => inv_cap P (∃ ws, {[ b, e ]} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, interp w)%I
                        (logN .@ (b,e)) γ
  end.

  Definition write_cond b e (g : Locality) (γ : gname) (interp : D) φ : iProp Σ := 
    match g with
    | Local => inv_cap T (∃ ws, {[ b, e ]} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, φ w ∗ interp w)%I (logN .@ (b,e)) γ
    | Global => inv_cap P (∃ ws, {[ b, e ]} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, φ w ∗ interp w)%I (logN .@ (b,e)) γ
  end.

  (* we distinguish between private and public future world by discarding all inv keys *)
  (* in the public future world case. In other words, public future worlds may not     *)
  (* depend on currently available temporary invariants *)
  Definition exec_cond b e g (P : list Perm) (interp_expr : D) : iProp Σ :=
    match g with
    | Local =>
      (∀ a b' e' p, {[ b', e' ]} ⊂ₐ {[ b, e ]} ∧
                    a ∈ₐ {[ b' , e' ]} ∧ ⌜In p P⌝ ∧
                    ▷ interp_expr (inr ((p,g),b', e',a)))%I
    | Global =>
      (□ ∀ a b' e' p, {[ b', e' ]} ⊂ₐ {[ b, e ]} ∧
                      a ∈ₐ {[ b' , e' ]} ∧ ⌜In p P⌝ ∧
                    ▷ interp_expr (inr ((p,g),b', e',a)))%I
    end. 
    
  Definition enter_cond b e a g (interp_expr : D) : iProp Σ :=
    match g with
    | Local => (▷ interp_expr (inr ((RX,g),b,e,a)))%I
    | Global => (□ ▷ interp_expr (inr ((RX,g),b,e,a)))%I 
    end.
  
  (* interp definitions *)
  Definition interp_reg (interp : D) : R :=
    λne (reg : leibnizC Reg), (∀ (r : RegName), ⌜r ≠ PC⌝ →
              ⌜is_Some (reg !! r)⌝ ∧ interp (reg !r! r))%I. 

  Definition interp_conf (conf : Reg * Mem) : iProp Σ :=
    (registers_mapsto conf.1 -∗ WP Seq (Instr Executable) {{ λne v, ∃ r, registers_mapsto r }})%I.

  (* a PC is in the expression relation if we can execute the configuration with that PC.
     If the permission of the PC is local, the relation requires a key to use the 
     local region. *)
  Definition interp_expr (interp : D) : D :=
    λne w, (∀ r m, interp_reg interp r -∗
             ∃ p g b e a, ⌜w = (inr ((p,g),b,e,a))⌝ ∧
               match g with
               | Local => ∃ γ, own γ 1%Qp -∗ interp_conf (update_reg (r,m) PC w)
               | Global => interp_conf (update_reg (r,m) PC w)
               end)%I. 
  
  Definition interp_z : D := λne w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : D := λne w, True%I.

  Definition interp_cap_RO (interp : D) : D :=
    λne w, (∃ g b e a γ, ⌜w = inr ((RO,g),b,e,a)⌝ ∗
                                  read_cond b e g γ interp)%I.

  Definition interp_cap_RW (interp : D) : D :=
    λne w, (∃ p g b e a γ, ⌜w = inr ((p,g),b,e,a)⌝ ∗ read_cond b e g γ interp
                          ∗ write_cond b e g γ interp (λne w, ⌜isLocalWord w = false⌝))%I.

  Definition interp_cap_RWL (interp : D) : D :=
    λne w, (∃ p g b e a γ, ⌜w = inr ((p,g),b,e,a)⌝ ∗ read_cond b e g γ interp
                                    ∗ write_cond b e g γ interp (λne w, True))%I.

  Definition interp_cap_RX (interp : D) : D :=
    λne w, (∃ p g b e a γ, ⌜w = inr ((p,g),b,e,a)⌝ ∗ read_cond b e g γ interp
      ∗ exec_cond b e g [RX] (interp_expr interp))%I.  

  Definition interp_cap_E (interp : D) : D :=
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝
      ∗ enter_cond b e a g (interp_expr interp))%I.

  Definition interp_cap_RWX (interp : D) : D :=
    λne w, (∃ p g b e a γ, ⌜w = inr ((p,g),b,e,a)⌝ ∗ read_cond b e g γ interp
                          ∗ write_cond b e g γ interp (λne w, ⌜isLocalWord w = false⌝)
                          ∗ exec_cond b e g [RWX;RX] (interp_expr interp))%I.

  Definition interp_cap_RWLX (interp : D) : D :=
    λne w, (∃ p g b e a γ, ⌜w = inr ((p,g),b,e,a)⌝ ∗ read_cond b e g γ interp
                          ∗ write_cond b e g γ interp (λne w, True)
                          ∗ exec_cond b e g [RWX;RX;RWLX] (interp_expr interp))%I.
  
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
    (*         /interp_cap_RX /interp_cap_E /interp_cap_RWX /interp_cap_RWLX. *)
    (* rewrite /read_cond /write_cond /enter_cond /exec_cond. *)
    (* solve_contractive. *)
  (* Qed. *)
   
  Lemma fixpoint_interp1_eq (x : leibnizC Word) :
    fixpoint interp1 x ≡ interp1 (fixpoint interp1) x.
  Proof. exact: (fixpoint_unfold (interp1) x). Qed. 

  Program Definition interp : D := λne w, fixpoint interp1 w.
  Program Definition interp_expression : D := interp_expr interp.
  Program Definition interp_registers : R := interp_reg interp.

  Global Instance read_cond_persistent : Persistent (read_cond a e g γ interp).
  Proof. intros. rewrite /read_cond. destruct g; apply _. Qed. 

  Global Instance write_cond_persistent : Persistent (write_cond a e g γ interp Φ).
  Proof. intros. rewrite /read_cond. destruct g; apply _. Qed. 
  
End logrel.

Notation "⟦ w ⟧" := (interp w).
Notation "⟦ w ⟧ₑ" := (interp_expression w).
Notation "⟦ r ⟧ᵣ" := (interp_registers r).
Notation "⟦ conf ⟧ₒ" := (interp_conf conf). 