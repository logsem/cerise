From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region.
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
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
   λne (reg : leibnizO Reg), (full_map reg ∧
                              ∀ (r : RegName), (⌜r ≠ PC⌝ → interp (reg !r! r)))%I.

  Definition interp_conf : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ∃ r, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  
  Program Definition interp_expr (interp : D) r : D :=
    (λne w, (interp_reg interp r ∗ registers_mapsto (<[PC:=w]> r) ∗ na_own logrel_nais ⊤ -∗
                        ⌜match w with inr _ => True | _ => False end⌝ ∧ interp_conf))%I.
  Solve All Obligations with solve_proper.
  
  (* condition definitions *)
  Program Definition read_cond (P : D) : D -n> iProp Σ :=
    λne interp, (▷ □ ∀ (w : Word), P w -∗ interp w)%I.
  Solve Obligations with solve_proper.
  Global Instance read_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) read_cond.
  Proof. solve_proper. Qed.
  
  Program Definition write_cond (P : D) : D -n> iProp Σ :=
    λne interp, (▷ □ ∀ (w : Word), interp w -∗ P w)%I.
  Solve Obligations with solve_proper.
  Global Instance write_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) write_cond.
  Proof. solve_proper. Qed.
  
  Program Definition enter_cond b e a : D -n> iProp Σ :=
    λne interp, (∀ r, ▷ interp_expr interp r (inr (RX,b,e,a)))%I.
  Solve Obligations with solve_proper.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. solve_proper. Qed.

  (* interp definitions *)
  Program Definition interp_ref_inv (a : Addr) : D -n> iProp Σ := λne P, (∃ w, a ↦ₐ w ∗ P w)%I.
  Solve Obligations with solve_proper.

  Definition logN : namespace := nroot .@ "logN".
  
  Definition interp_z : D := λne w, ⌜match w with inl z => True | _ => False end⌝%I.

  Definition interp_cap_O : D := λne _, True%I.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne w, (match w with
              | inr (RO,b,e,a) =>
                [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.     

  Program Definition interp_cap_RW (interp : D) : D :=
    λne w, (match w with
              | inr (RW,b,e,a) =>
                [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne w, (match w with inr (RX,b,e,a) =>
                         [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne w, (match w with
              | inr (E,b,e,a) => □ enter_cond b e a interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne w, (match w with inr (RWX,b,e,a) =>
                           [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  
  Program Definition interp1 (interp : D) : D :=
    (λne w,
    match w return _ with
    | inl _ => interp_z w
    | inr (O, b, e, a) => interp_cap_O w
    | inr (RO, b, e, a) => interp_cap_RO interp w
    | inr (RW, b, e, a) => interp_cap_RW interp w
    | inr (RX, b, e, a) => interp_cap_RX interp w
    | inr (E, b, e, a) => interp_cap_E interp w
    | inr (RWX, b, e, a) => interp_cap_RWX interp w
    end)%I.

  
  Global Instance read_cond_contractive :
    Contractive (read_cond).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct c, p, p, p; auto.
    solve_contractive. 
  Qed.   
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct c, p, p, p; auto.     
    solve_contractive. 
  Qed.
  Global Instance enter_cond_contractive b e a :
    Contractive (λ interp, enter_cond b e a interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct c, p, p, p; auto.
    solve_contractive. 
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct c, p, p, p; auto.
    solve_contractive. 
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct c, p, p, p; auto.
    solve_contractive. 
  Qed.
  

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn w.
    rewrite /interp1.
    destruct w; [auto|].
    destruct c,p,p,p; first auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RX_contractive.
    - by apply interp_cap_E_contractive.
    - by apply interp_cap_RWX_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (x : leibnizO Word) :
    fixpoint (interp1) x ≡ interp1 (fixpoint (interp1)) x.
  Proof. exact: (fixpoint_unfold (interp1) x). Qed.

  Definition interp : D := λne w, (fixpoint (interp1)) w.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _. destruct c,p,p,p; repeat (apply exist_persistent; intros); try apply _.
  Qed.
  
  Lemma read_allowed_inv (a' a b e: Addr) p :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    (interp (inr (p,b,e,a)) →
     (∃ P, inv (logN .@ a') (interp_ref_inv a' P) ∗ read_cond P interp))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
    - iDestruct "Hiff" as "[Hread Hwrite]". iFrame. 
    - iDestruct "Hiff" as "[Hread Hwrite]". iFrame. 
  Qed.

  Lemma write_allowed_inv (a' a b e: Addr) p :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    (interp (inr (p,b,e,a)) →
     inv (logN .@ a') (interp_ref_inv a' interp))%I.
  Proof.
    iIntros (Hin Wa) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "[] Hinv"). 
      iNext. iAlways. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "[] Hinv"). 
      iNext. iAlways. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
  Qed.
  
End logrel.
