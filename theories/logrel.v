From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
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

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
   λne (reg : leibnizO Reg), (full_map reg ∧
                              ∀ (r : RegName) (v : Word), (⌜r ≠ PC⌝ → ⌜reg !! r = Some v⌝ → interp v))%I.

  Definition interp_conf : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ∃ r, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne w, (interp_reg interp r ∗ registers_mapsto (<[PC:=w]> r) ∗ na_own logrel_nais ⊤ -∗
             interp_conf))%I.
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
    λne interp, (∀ r, ▷ □ interp_expr interp r (WCap RX b e a))%I.
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
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent w : Persistent (interp w).
  Proof. intros. destruct w; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _. destruct p; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Lemma interp_int n : ⊢ interp (WInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

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

  Definition writeAllowed_in_r_a (r : Reg) a :=
    ∃ reg (w : Word), r !! reg = Some w ∧ writeAllowedWord w ∧ hasValidAddress w a.

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

  Global Instance writeAllowedWord_dec w: Decision (writeAllowedWord w).
  Proof. destruct w;[right;auto|]. destruct p;simpl;apply _. Qed.

  Global Instance hasValidAddress_dec w a: Decision (hasValidAddress w a).
  Proof. destruct w;[right;auto|]. destruct p;simpl;apply _. Qed.

  Global Instance writeAllowed_in_r_a_Decidable r a: Decision (writeAllowed_in_r_a r a).
  Proof.
    apply finite.exists_dec.
    intros x. destruct (r !! x) eqn:Hsome;
    first destruct (decide (writeAllowedWord w)), (decide (hasValidAddress w a)).
    left. eexists _; auto.
    all : (right; intros [w1 (Heq & ? & ?)]; inversion Heq; try congruence ).
  Qed.

  Global Instance writeAllowed_in_r_a_Persistent P r a: Persistent (if decide (writeAllowed_in_r_a r a) then write_cond P interp else emp)%I.
  Proof. intros. case_decide; apply _. Qed.

  Lemma read_allowed_inv_regs (a' a b e: Addr) p r :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers r -∗
      interp (WCap p b e a) -∗
      (∃ P, inv (logN .@ a') (interp_ref_inv a' P) ∗ read_cond P interp ∗ if decide (writeAllowed_in_r_a (<[PC:=WCap p b e a]> r) a') then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "#Hregs #Hinterp".
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[Hfull Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as (reg & w & (Hw & Hwa & Ha) ).
      destruct (decide (reg = PC)).
      + simplify_map_eq.
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p; try contradiction; inversion Hwa;
          try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
      + simplify_map_eq.
        destruct (r !! reg) eqn:Hsome; rewrite Hsome in Hw; inversion Hw.
        destruct w;[inversion Ha|]. destruct Ha as [Hwba ->].
        iSpecialize ("Hregvalid" $! _ _ n Hsome). simplify_eq. iClear "Hinterp".
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
    
  (* Get the validity of a region containing only valid words *)
  Lemma region_valid_alloc E (b e a: Addr) l p  :
    PermFlowsTo RO p →
    ([∗ list] w ∈ l, interp w) -∗
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hp) "#Hl H".
    iMod (region_inv_alloc with "[H]") as "H".
    { iDestruct (big_sepL2_length with "H") as %Hlen.
      iDestruct (big_sepL2_to_big_sepL_r with "Hl") as "Hl'";[apply Hlen|].
      iDestruct (big_sepL2_sep with "[H]") as "H";[iSplitL;[iFrame "H"|iFrame "Hl'"]|].
      iApply (big_sepL2_mono with "H").
      intros k v1 v2 ? Hlk. cbn. iIntros. iFrame. }
    iDestruct (big_sepL2_length with "H") as %?.
    iDestruct (big_sepL2_to_big_sepL_l with "H") as "H"; auto.

    iModIntro. rewrite fixpoint_interp1_eq //.
    destruct p; cbn; eauto; try by inversion Hp.
    all: iApply (big_sepL_mono with "H").
    all: iIntros (k a' Hk) "H"; cbn.
    all: iExists (fixpoint interp1); iFrame.
    all: try iSplit; iNext; iModIntro; eauto.
  Qed.

  Instance fin_set : FinSet Addr (gset Addr) := (@gset_fin_set Addr (@finz_eq_dec MemNum) (@finz_countable MemNum)).

  (* Lemma from newer version of stdpp applied to types used in compute_mask *)
  (* Lemma set_fold_disj_union_compute_mask (E : coPset) (x : Addr) (X : gset Addr) : *)
  (*   {[x]} ## X -> *)
  (*   @set_fold Addr (gset Addr) (@gset_elements Addr (@finz_eq_dec MemNum) (@finz_countable MemNum)) coPset (λ (l : Addr) (E0 : coPset), E0 ∖ (↑logN.@l)) E ({[x]} ∪ X) *)
  (*   = @set_fold _ (gset Addr) _ _ (λ (l : Addr) (E0 : coPset), E0 ∖ (↑logN.@l)) (@set_fold _ (gset Addr) _ _ (λ (l : Addr) (E0 : coPset), E0 ∖ ↑logN.@l) E {[x]}) X. *)
  (* Proof. *)
  (*   intros Hdisj. unfold set_fold. simpl. *)
  (*   rewrite <-foldr_app. apply foldr_permutation;try apply _. *)
  (*   - intros j1 x1 j2 x2 b' Hj Hj1 Hj2. set_solver. *)
  (*   - rewrite elements_disj_union //. apply Permutation_app_comm. *)
  (* Qed. *)
  Lemma set_fold_disj_union_compute_mask (E : coPset) (Y X : gset Addr) :
    Y ## X ->
    @set_fold Addr (gset Addr) (@gset_elements Addr (@finz_eq_dec MemNum) (@finz_countable MemNum)) coPset (λ (l : Addr) (E0 : coPset), E0 ∖ (↑logN.@l)) E (Y ∪ X)
    = @set_fold _ (gset Addr) _ _ (λ (l : Addr) (E0 : coPset), E0 ∖ (↑logN.@l)) (@set_fold _ (gset Addr) _ _ (λ (l : Addr) (E0 : coPset), E0 ∖ ↑logN.@l) E Y) X.
  Proof.
    intros Hdisj. unfold set_fold. simpl.
    rewrite <-foldr_app. apply foldr_permutation;try apply _.
    - intros j1 x1 j2 x2 b' Hj Hj1 Hj2. set_solver.
    - rewrite elements_disj_union //. apply Permutation_app_comm.
  Qed.

  Definition compute_mask (E : coPset) (ls : gset Addr) :=
    @set_fold _ (gset Addr) (@gset_elements Addr (@finz_eq_dec MemNum) (@finz_countable MemNum))
      coPset (λ (l : Addr) (E : coPset), E ∖ (↑logN .@ l)) E ls.
    
  
  Lemma compute_mask_mono E ls :
    compute_mask E ls ⊆ E.
  Proof.
    rewrite /compute_mask. revert E.
    induction ls using set_ind_L; intros E.
    { by rewrite set_fold_empty. }
    rewrite (set_fold_disj_union_compute_mask E {[x]} X);[|set_solver].
    rewrite set_fold_singleton.
    etransitivity; [apply IHls|].
    set_solver.
  Qed.
  
  Lemma compute_mask_subseteq E (ls1 ls2 : gset Addr) :
    ls2 ⊆ ls1 → compute_mask E ls1 ⊆ compute_mask E ls2.
  Proof.    
    rewrite /compute_mask.
    revert E ls1.
    induction ls2 using set_ind_L.
    { intros E ls1 Hle. rewrite set_fold_empty. apply compute_mask_mono. }
    intros E ls1 Hle.
    rewrite set_fold_disj_union_compute_mask ; [|set_solver..].
    rewrite set_fold_singleton.
    assert (∃ Y, ls1 = {[x]} ∪ Y ∧ {[x]} ## Y) as [Y [-> Hdisj] ].
    { apply subseteq_disjoint_union_L. set_solver. }
    rewrite set_fold_disj_union_compute_mask; [|set_solver..].
    rewrite set_fold_singleton. 
    apply IHls2. set_solver.
  Qed.

  Lemma compute_mask_elem_of E l ls :
    ↑(logN .@ l) ⊆ E → l ∉ ls → ↑logN.@l ⊆ compute_mask E ls.
  Proof.
    rewrite /compute_mask.
    revert E.
    induction ls using set_ind_L.
    { set_solver. }
    intros E HE Hnin.
    rewrite set_fold_disj_union_compute_mask; [|set_solver..].
    rewrite set_fold_singleton.
    revert Hnin; rewrite not_elem_of_union => Hnin. destruct Hnin as [Hnin1 Hnin2].
    apply IHls; [|done].
    assert (logN.@l ## logN.@x).
    { apply ndot_ne_disjoint. set_solver. }
    set_solver.
  Qed.

  Lemma compute_mask_id E :
    compute_mask E ∅ = E.
  Proof. auto. Qed.

  Definition in_region (w : Word) (b e : Addr) :=
    match w with
    | WCap p b' e' a => PermFlows RO p /\ (b <= b')%a /\ (e' <= e)%a
    | _ => False
    end.

  Definition in_region_list (w : Word) (ls: list Addr) :=
    match w with
    | WCap p b' e' a => PermFlows RO p /\ (forall x, b' <= x < e' -> x ∈ ls)%a
    | _ => False
    end.
  
  Lemma region_valid_in_region_ind E (l1 l2 : list Addr) :
    Forall (λ a, ↑logN.@a ⊆ E) (l1 ++ l2) ->
    NoDup l1 -> NoDup l2 ->
    l2 ## l1 ->
    ([∗ list] a ∈ l1, inv (logN .@ a) (interp_ref_inv a interp)) -∗
    ([∗ list] a ∈ l2, ∃ w, a ↦ₐ w ∗ ⌜is_cap w = false \/ in_region_list w (l1 ++ l2)⌝) -∗
    |={compute_mask E (list_to_set l1)}=> ([∗ list] a ∈ l1 ++ l2, inv (logN .@ a) (interp_ref_inv a interp)).
  Proof.
    iIntros (Hforall Hdup1 Hdup2 Hdisj) "Hval Hl2".
    iInduction l2 as [|] "IH"
  forall (l1 Hdup2 Hforall Hdup1 Hdisj);iDestruct "Hval" as "#Hval".
    { simpl. rewrite app_nil_r. iFrame "#". iModIntro. done. }
    iDestruct "Hl2" as "[Hl Hl2]".
    iDestruct "Hl" as (w) "[Hl %]".
    rename H0 into Hcond.
    apply NoDup_cons in Hdup2 as [Hni Hdup2].
    apply disjoint_cons in Hdisj as Hni'.
    apply disjoint_swap in Hdisj;auto.
    destruct Hcond as [Hint | Hin].
    - destruct w;try done.
      iMod (inv_alloc (logN .@ a) _ (interp_ref_inv a interp) with "[Hl]") as "#Hlval".
      { iNext. iExists _. iFrame. iApply fixpoint_interp1_eq. eauto. }
      iMod (fupd_mask_subseteq (compute_mask E (list_to_set (a :: l1)))) as "Hclose";
        [apply compute_mask_subseteq; set_solver|].
      iMod ("IH" $! (a :: l1) with "[] [] [] [] [] [Hl2]") as "HH";auto.
      { iPureIntro. simpl. rewrite Permutation_middle. auto. }
      { iPureIntro. apply NoDup_cons;auto. }
      { iSimpl. iFrame "#". }
      { iApply (big_sepL_mono with "Hl2"). iIntros (k x Hx) "Hc".
        iDestruct "Hc" as (w) "[Hx [Hw|%]]";iExists _;iFrame;[iLeft;auto|].
        iRight. iPureIntro. destruct w;try done.
        destruct H0 as [Hro Hb]. split;auto.
        intros y Hy. simpl. rewrite Permutation_middle. apply Hb;auto. }
      iDestruct (big_sepL_app with "HH") as "[#Hl1 #Hl2]".
      iFrame "∗ #". iMod ("Hclose"). auto.
    - destruct w;try done. destruct Hin as [Hro Hin].
      iApply big_sepL_app. iFrame "#".
      iMod (inv_alloc_open (logN .@ a) _ (interp_ref_inv a interp)) as "[#Ha Hcls]".
      { apply compute_mask_elem_of.
        { revert Hforall; rewrite Forall_forall =>Hforall. apply Hforall.
          apply elem_of_app;right;apply elem_of_cons;auto. }
        apply not_elem_of_list_to_set. auto. }
      iFrame "#".
      iMod (fupd_mask_subseteq (compute_mask E (list_to_set (a :: l1)))) as "Hclose".
      { rewrite /compute_mask.
        rewrite list_to_set_cons union_comm_L.
        rewrite (set_fold_disj_union_compute_mask _ (list_to_set l1) {[a]}).
        - rewrite set_fold_singleton. done.
        - set_solver. }
      iMod ("IH" $! (a :: l1) with "[] [] [] [] [] [Hl2]") as "HH";auto.
      { iPureIntro. simpl. rewrite Permutation_middle. auto. }
      { iPureIntro. apply NoDup_cons;auto. }
      { iSimpl. iFrame "#". }
      { iApply (big_sepL_mono with "Hl2"). iIntros (k x Hx) "Hc".
        iDestruct "Hc" as (w) "[Hx [Hw|%]]";iExists _;iFrame;[iLeft;auto|].
        iRight. iPureIntro. destruct w;try done.
        destruct H0 as [Hro' Hb]. split;auto.
        intros y Hy. simpl. rewrite Permutation_middle. apply Hb;auto. }
      iMod "Hclose".
      iSimpl in "HH";iDestruct "HH" as "[#Hav HH]".
      iDestruct (big_sepL_app with "HH") as "[#Hl1v #Hl2v]".
      iMod ("Hcls" with "[Hl]");[|by iFrame "#"].
      iNext. iExists _. iFrame.
      iApply fixpoint_interp1_eq. destruct p;try done.
      all: iApply big_sepL_forall; iIntros (k x Hlook); iExists interp.
      all: iSplit;[|(try iSplitR);iIntros (?);iNext;iModIntro;auto].
      all: apply elem_of_list_lookup_2,elem_of_finz_seq_between,Hin,elem_of_app in Hlook.
      all: destruct Hlook as [Hl1 | [->|Hl2]%elem_of_cons];
          [iDestruct (big_sepL_elem_of with "Hl1v") as "$";auto|iFrame "#"|
            iDestruct (big_sepL_elem_of with "Hl2v") as "$";auto].
      Unshelve. all: apply _.
  Qed.

  Lemma region_valid_in_region E (b e a: Addr) l p  :
    Forall (λ a0 : Addr, ↑logN.@a0 ⊆ E) (finz.seq_between b e) ->
    PermFlowsTo RO p →
    Forall (λ w, is_cap w = false \/ in_region w b e) l ->
    ([∗ list] a;w ∈ finz.seq_between b e;l, a ↦ₐ w) ={E}=∗
    interp (WCap p b e a).
  Proof.
    iIntros (Hsub Hperm Hl) "Hl".
    iDestruct (region_valid_in_region_ind E [] (finz.seq_between b e) with "[] [Hl]") as "HH".
    { rewrite app_nil_l. auto. }
    { apply NoDup_nil. auto. }
    { apply finz_seq_between_NoDup. }
    { apply disjoint_nil_r. exact 0%a. }
    { auto. }
    { rewrite app_nil_l.
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iApply big_sepL2_to_big_sepL_l;[apply Hlen|].
      iApply (big_sepL2_mono with "Hl").
      iIntros (k y1 y2 Hy1 Hy2) "Hl".
      iExists _; iFrame. iPureIntro.
      revert Hl. rewrite Forall_lookup => Hl.
      apply Hl in Hy2 as [Hy2|Hy2];auto.
      right. destruct y2;try done.
      destruct Hy2 as [Hro Hin].
      split;auto. intros x Hx. apply elem_of_finz_seq_between.
      solve_addr. }
    { rewrite list_to_set_nil compute_mask_id app_nil_l. iMod "HH".
      iModIntro.
      iApply fixpoint_interp1_eq. destruct p;try done.
      all: iApply (big_sepL_mono with "HH");iIntros (k y Hy) "Hl";
        try iExists _;iFrame;try iSplit;iIntros (?);auto. }
  Qed.

End logrel.
