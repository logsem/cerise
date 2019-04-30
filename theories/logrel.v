From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export lang rules.
From iris.algebra Require Import list frac excl.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{memG Σ, regG Σ, inG Σ fracR, inG Σ (exclR (leibnizR RegName))}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ). 
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  (* Region predicate. Size of region needs to match up exactly to size of list *)
  Fixpoint region_mapsto (b e : option Addr) (ws : list Word) : iProp Σ :=  
    match b,e with
    | Some ba, Some ea =>
      match ws with
      | w :: ws' =>
        if (ba <=? ea)%a then (ba ↦ₐ w ∗ region_mapsto (ba + 1)%a e ws')%I
        else False%I
      | [] => if (ba <=? ea)%a then False%I else True%I
      end
    | Some ba, None =>
      match ws with
      | w :: ws' => (ba ↦ₐ w ∗ region_mapsto (ba + 1)%a e ws')%I
      | [] => False%I
      end
    | _,_ => if ((length ws) =? 0)%nat then True%I else False%I
    end. 
  Notation "{[ b , e ]} ↦ₐ {[ ws ]}" := (region_mapsto (Some b) e ws)
   (at level 50, format "{[ b , e ]} ↦ₐ {[ ws ]}") : bi_scope.

  Definition included (b' : Addr) (e' : option Addr)
             (b : Addr) (e : option Addr) : iProp Σ :=
    (⌜(b' <=? b)%a⌝ ∧ ((⌜e = None⌝ ∧ ⌜e' = None⌝) ∨
                  (∃ a a', ⌜e = Some a⌝ ∧ ⌜e' = Some a'⌝ ∧ ⌜(a <=? a')%a⌝)))%I.
  Notation "{[ b , e ]} ⊂ₐ {[ b' , e' ]}" := (included b e b' e')
   (at level 50, format "{[ b , e ]} ⊂ₐ {[ b' , e' ]}") : bi_scope.

  Fixpoint in_range (a b : Addr) (e : option Addr) : iProp Σ :=
    match e with
    | None => (⌜(b <=? a)%a⌝)%I
    | Some e' => (⌜(b <=? a)%a⌝ ∧ ⌜(a <? e')%a⌝)%I
    end.
  Notation "a ∈ₐ {[ b , e ]}" := (in_range a b e)
   (at level 50, format "a ∈ₐ {[ b , e ]}") : bi_scope.

  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  (* Definition remaining_mapsto (r : Reg) (m : Mem) : iProp Σ := *)
    

  (* Definition configuration_mapsto_init (reg : Reg) : iProp Σ := *)
  (*   (∀ (r : RegName), *)
  (*       (⌜reg !! r = None⌝ ∗ own (gen_heap_name reg_gen_regG) (Excl (cmra_car r))))%I.  *)

  (* capability conditions *)
  Definition read_cond b e (g : Locality) (γ : gname) (interp : D) : iProp Σ := 
    match g with
    | Local =>
      (∃ b' e', {[ b, e ]} ⊂ₐ {[ b', e' ]} ∧
         □ (∀ q:Qp, own γ q -∗
                inv_cap T (∃ ws, {[ b', e']} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, interp w)%I
                        (logN .@ (b',e')) γ))%I
    | Global =>
      (∃ b' e', {[ b, e ]} ⊂ₐ {[ b', e' ]} ∧
                inv_cap P (∃ ws, {[ b', e']} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, interp w)%I
                        (logN .@ (b',e')) γ)%I
  end.

  Definition write_cond b e (g : Locality) (γ : gname) (interp : D) φ : iProp Σ := 
    match g with
    | Local =>
      (∃ b' e', {[ b, e ]} ⊂ₐ {[ b', e' ]} ∧
         □ (∀ q:Qp, own γ q -∗
            inv_cap T (∃ ws, {[ b', e']} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, φ w ∗ interp w)%I
                    (logN .@ (b',e')) γ))%I
    | Global =>
      (∃ b' e', {[ b, e ]} ⊂ₐ {[ b', e' ]} ∧
            inv_cap P (∃ ws, {[ b', e']} ↦ₐ {[ ws ]} ∗ [∗ list] w ∈ ws, φ w ∗ interp w)%I
                    (logN .@ (b',e')) γ)%I
  end.

  Definition exec_cond b e g (P : list Perm) (interp_expr : D) : iProp Σ :=
    (∀ a b' e' p, {[ b', e' ]} ⊂ₐ {[ b, e ]} ∧ a ∈ₐ {[ b' , e' ]} ∧ ⌜In p P⌝ ∧
                  ▷ interp_expr (inr ((p,g),b',e',a)))%I.

  Definition enter_cond b e a g (interp_expr : D) : iProp Σ :=
    (▷ interp_expr (inr ((RX,g),b,e,a)))%I.
  
  (* interp definitions *)
  Definition interp_reg (interp : D) : R :=
    λne (reg : leibnizC Reg), (∀ (r : RegName), ⌜r ≠ PC⌝ →
              ⌜is_Some (reg !! r)⌝ ∧ interp (reg !r! r))%I. 

  Definition interp_conf (conf : Reg * Mem) : iProp Σ :=
    (registers_mapsto conf.1 -∗ WP Executable {{ λne v, True }})%I.

  (* TODO: have two of the following, one for public and one for private FWs *)
  Definition interp_expr (interp : D) : D :=
    λne w, (□ ∀ r m, interp_reg interp r -∗
                                interp_conf (update_reg (r,m) PC w))%I.
  
  Definition interp_z : D := λne w, ⌜∃ z, w = inl z⌝%I.
  
  Definition interp_cap_O : D := λne w, True%I.

  Definition interp_cap_RO (interp : D) : D :=
    λne w, (∃ g b e a γ, ⌜w = inr ((RO,g),b,e,a)⌝ ∗ read_cond b e g γ interp)%I.

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
    λne w, (∃ p g b e a, ⌜w = inr ((p,g),b,e,a)⌝ ∗ enter_cond b e a g interp)%I.

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
  Proof.
    rewrite /interp1 /interp_cap_RO /interp_cap_RW /interp_cap_RWL
            /interp_cap_RX /interp_cap_E /interp_cap_RWX /interp_cap_RWLX.
    rewrite /read_cond /write_cond /enter_cond /exec_cond.
    solve_contractive.
  Qed. 
   
  Lemma fixpoint_interp1_eq (x : leibnizC Word) :
    fixpoint interp1 x ≡ interp1 (fixpoint interp1) x.
  Proof. exact: (fixpoint_unfold (interp1) x). Qed. 

  Program Definition interp : D := λne w, fixpoint interp1 w.
  Program Definition interp_expression : D := interp_expr interp. 
  Program Definition interp_registers : R := interp_reg interp.
End logrel.

Notation "⟦ w ⟧" := (interp w).
Notation "⟦ w ⟧ₑ" := (interp_expression w).
Notation "⟦ r ⟧ᵣ" := (interp_registers r).
Notation "⟦ conf ⟧ₒ" := (interp_conf conf). 