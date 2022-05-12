From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants saved_prop.
From cap_machine.rules Require Import rules_base.
From Coq Require Import Eqdep_dec.
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

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) (i : CoreN) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! (i,r))⌝)%I.
  Program Definition interp_reg (interp : D) (i : CoreN) : R :=
   λne (reg : leibnizO Reg), (full_map reg i ∧
                              ∀ (j : CoreN) (r : RegName) (v : Word)
                              , (⌜r ≠ PC⌝
                                 → ⌜reg !! (j, r) = Some v⌝
                                 → interp v))%I.

  Definition interp_conf (i: CoreN) : iProp Σ :=
    (WP (i, Seq (Instr Executable)) {{ v, ⌜v = (i, HaltedV)⌝ → ∃ r , full_map r i ∧ registers_mapsto r }})%I.

  Program Definition interp_expr (interp : D) r (i : CoreN) : D :=
    (λne w, (interp_reg interp i r ∗ registers_mapsto (<[(i, PC):=w]> r) -∗
             interp_conf i))%I.
  Solve All Obligations with solve_proper.

  (* condition definitions *)
  Program Definition read_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (w : Word), P w -∗ interp w)%I.
  Solve Obligations with solve_proper.
  Global Instance read_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) read_cond.
  Proof. solve_proper. Qed.

  Program Definition write_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (w : Word), interp w -∗ P w)%I.
  Solve Obligations with solve_proper.
  Global Instance write_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) write_cond.
  Proof. solve_proper. Qed.

  Program Definition enter_cond b e a : D -n> iPropO Σ :=
    λne interp, (∀ r i, ▷ □ interp_expr interp r i (WCap RX b e a))%I.
  Solve Obligations with solve_proper.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. solve_proper. Qed.

  (* interp definitions *)
  Program Definition interp_ref_inv (a : Addr) : D -n> iPropO Σ := λne P, (∃ w, a ↦ₐ w ∗ P w)%I.
  Solve Obligations with solve_proper.

  Definition logN : namespace := nroot .@ "logN".

  Definition interp_z : D := λne w, ⌜match w with WInt z => True | _ => False end⌝%I.

  Definition interp_cap_O : D := λne _, True%I.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne w, (match w with
              | WCap RO b e a =>
                [∗ list] a ∈ (finz.seq_between b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RW (interp : D) : D :=
    λne w, (match w with
              | WCap RW b e a =>
                [∗ list] a ∈ (finz.seq_between b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne w, (match w with WCap RX b e a =>
                         [∗ list] a ∈ (finz.seq_between b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne w, (match w with
              | WCap E b e a => enter_cond b e a interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne w, (match w with WCap RWX b e a =>
                           [∗ list] a ∈ (finz.seq_between b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.


  Program Definition interp1 (interp : D) : D :=
    (λne w,
    match w return _ with
    | WInt _ => interp_z w
    | WCap O b e a => interp_cap_O w
    | WCap RO b e a => interp_cap_RO interp w
    | WCap RW b e a => interp_cap_RW interp w
    | WCap RX b e a => interp_cap_RX interp w
    | WCap E b e a => interp_cap_E interp w
    | WCap RWX b e a => interp_cap_RWX interp w
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
    destruct x0; auto. destruct p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct p; auto.
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
    destruct x0; auto. destruct p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct p; auto.
    solve_contractive.
  Qed.


  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn w.
    rewrite /interp1.
    destruct w; [auto|].
    destruct p; first auto.
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
  Definition interp_expression r i : D := interp_expr interp r i.
  Definition interp_registers i : R := interp_reg interp i.

  Global Instance interp_persistent w : Persistent (interp w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _. destruct p; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Lemma interp_int n : ⊢ interp (WInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  Lemma interp_cap_range p b e a :
    forall a', p ≠ E -> ⊢ interp (WCap p b e a) -∗ interp (WCap p b e a') .
  Proof.
    iIntros (? ?) "#Hinterp".
    rewrite /interp /= (fixpoint_interp1_eq (WCap _ _ _ _)) /= ; cbn.
    destruct p ; try contradiction ;
    rewrite (fixpoint_interp1_eq (WCap _ _ _ _)) /= ; cbn ; eauto.
  Qed.

  Lemma read_allowed_inv (a' a b e: Addr) p :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp (WCap p b e a) →
      (∃ P, inv (logN .@ a') (interp_ref_inv a' P) ∗ read_cond P interp ∗ if writeAllowed p then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
  Qed.

  Lemma write_allowed_inv (a' a b e: Addr) p :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp (WCap p b e a) →
      inv (logN .@ a') (interp_ref_inv a' interp))%I.
  Proof.
    iIntros (Hin Wa) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "Hinv").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "Hinv").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
  Qed.

  Definition writeAllowedWord (w : Word) : Prop :=
    match w with
    | WInt _ => False
    | WCap p _ _ _ => writeAllowed p = true
    end.

  Definition hasValidAddress (w : Word) (a : Addr) : Prop :=
    match w with
    | WInt _ => False
    | WCap p b e a' => (b ≤ a' ∧ a' < e)%Z ∧ a = a'
    end.

  Definition writeAllowed_in_r_a (r : Reg) i a :=
    ∃ (reg : RegName) (w : Word),
      r !! (i,reg) = Some w ∧ writeAllowedWord w ∧ hasValidAddress w a.

  Global Instance reg_finite : finite.Finite RegName.
  Proof. apply (finite.enc_finite (λ r : RegName, match r with
                                                  | PC => S RegNum
                                                  | addr_reg.R n fin => n
                                                  end)
                                   (λ n : nat, match n_to_regname n with | Some r => r | None => PC end)
                                   (S (S RegNum))).
         - intros x. destruct x;auto.
           unfold n_to_regname.
           destruct (nat_le_dec n RegNum).
           + do 2 f_equal. apply eq_proofs_unicity. decide equality.
           + exfalso. by apply (Nat.leb_le n RegNum) in fin.
         - intros x.
           + destruct x;[lia|]. apply leb_le in fin. lia.
         - intros i Hlt. unfold n_to_regname.
           destruct (nat_le_dec i RegNum);auto.
           lia.
  Qed.


  Global Instance coren_finite : finite.Finite CoreN.
  Proof. eapply (finite.enc_finite (λ i : CoreN, Z.to_nat i)
                   (λ n : nat,
                       match (finz.of_z (Z.of_nat n)) with
                       | Some i => i
                       | None => _
                       end)
                   (Z.to_nat machine_base.CoreNum)).
         - intros x. destruct x;auto.
  Admitted.

  Global Instance writeAllowedWord_dec w: Decision (writeAllowedWord w).
  Proof. destruct w;[right;auto|]. destruct p;simpl;apply _. Qed.

  Global Instance hasValidAddress_dec w a: Decision (hasValidAddress w a).
  Proof. destruct w;[right;auto|]. destruct p;simpl;apply _. Qed.

  Global Instance writeAllowed_in_r_a_Decidable r i a
    : Decision (writeAllowed_in_r_a r i a).
  Proof.
    eapply finite.exists_dec.
    intros x. destruct (r !! (i, x)) eqn:Hsome;
    first destruct (decide (writeAllowedWord w)), (decide (hasValidAddress w a)).
    left. eexists _; auto.
    all : (right; intros [w1 (Heq & ? & ?)]; inversion Heq; try congruence ).
  Qed.

  Global Instance writeAllowed_in_r_a_Persistent P r i a
    : Persistent (if decide (writeAllowed_in_r_a r i a) then write_cond P interp else emp)%I.
  Proof. intros. case_decide; apply _. Qed.

  Lemma read_allowed_inv_regs (a' a b e: Addr) p r i :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ ((interp_registers i) r -∗
      interp (WCap p b e a) -∗
      (∃ P, inv (logN .@ a') (interp_ref_inv a' P) ∗ read_cond P interp
            ∗ if decide (writeAllowed_in_r_a (<[(i, PC):=WCap p b e a]> r) i a')
              then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "#Hregs #Hinterp".
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[Hfull Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as (reg & w & (Hw & Hwa & Ha) ).
      destruct (decide ((i, reg) = (i, PC))).
      + simplify_map_eq.
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p; try contradiction; inversion Hwa;
          try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
      + simplify_map_eq.
        destruct (r !! (i, reg)) eqn:Hsome; rewrite Hsome in Hw; inversion Hw.
        destruct w;[inversion Ha|]. destruct Ha as [Hwba ->].
        assert (reg ≠ PC) by (intros ->; simplify_pair_eq).
        iSpecialize ("Hregvalid" $! _ _ _ H0 Hsome). simplify_eq. iClear "Hinterp".
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p0; try contradiction; inversion Hwa;
        try (iDestruct (extract_from_region_inv with "Hregvalid") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
    - rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
      destruct p; try contradiction;
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv [Hiff _] ]"; [eauto|iExists P;iSplit;eauto]);
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
  Qed.

  (* Lemma for allocating invariants in a region *)
  Lemma region_inv_alloc E l1 l2 :
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ interp v) ={E}=∗
    ([∗ list] k;_ ∈ l1;l2, inv (logN .@ k) (interp_ref_inv k interp)).
  Proof.
    revert l2. induction l1.
    - iIntros (l2) "Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      destruct l2;[|inversion Hlen].
      simpl. done.
    - iIntros (l2) "Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      destruct l2;[inversion Hlen|].
      iDestruct "Hl" as "[Ha Hl]".
      simpl. iMod (IHl1 with "Hl") as "Hl".
      iFrame. iApply inv_alloc. iNext. iExists w. iFrame.
  Qed.

  (* Get the validity of a region containing only integers *)
  Lemma region_integers_alloc E (b e a: Addr) l p :
    Forall (λ w, is_cap w = false) l →
    PermFlowsTo RO p →
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hl Hp) "H".
    iMod (region_inv_alloc with "[H]") as "H".
    { iApply (big_sepL2_mono with "H").
      intros k v1 v2 ? Hlk. cbn. iIntros. iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hl Hlk) as HH.
      cbn in HH. destruct v2; [| by inversion HH].
      rewrite fixpoint_interp1_eq //. }
    iDestruct (big_sepL2_length with "H") as %?.
    iDestruct (big_sepL2_to_big_sepL_l with "H") as "H"; auto.

    iModIntro. rewrite fixpoint_interp1_eq //.
    destruct p; cbn; eauto; try by inversion Hp.
    all: iApply (big_sepL_mono with "H").
    all: iIntros (k a' Hk) "H"; cbn.
    all: iExists (fixpoint interp1); iFrame.
    all: try iSplit; iNext; iModIntro; eauto.
  Qed.

End logrel.
