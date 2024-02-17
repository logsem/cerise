From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region seal_store.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine.rules Require Import rules_base.
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
    logrel_na_invG :: na_invG Σ;
    logrel_nais : na_inv_pool_name;
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition registers_mapsto (lregs : LReg) : iProp Σ :=
    ([∗ map] r↦lw ∈ lregs, r ↦ᵣ lw)%I.

  Definition full_map (lregs : LReg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (lregs !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
   λne (lregs : leibnizO LReg), (full_map lregs ∧
                              ∀ (r : RegName) (lv : LWord), (⌜r ≠ PC⌝ → ⌜lregs !! r = Some lv⌝ → interp lv))%I.

  Definition interp_conf : iProp Σ :=
    (WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ →
             ∃ lregs, full_map lregs ∧ registers_mapsto lregs ∗ na_own logrel_nais ⊤ }})%I.

  Program Definition interp_expr (interp : D) lregs : D :=
    (λne lw, (interp_reg interp lregs ∗ registers_mapsto (<[PC:=lw]> lregs) ∗ na_own logrel_nais ⊤ -∗
             interp_conf))%I.
  Solve All Obligations with solve_proper.

  (* condition definitions *)
  Program Definition read_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (lw : LWord), P lw -∗ interp lw)%I.
  Solve Obligations with solve_proper.
  Global Instance read_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) read_cond.
  Proof. solve_proper. Qed.

  Program Definition write_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (lw : LWord), interp lw -∗ P lw)%I.
  Solve Obligations with solve_proper.
  Global Instance write_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) write_cond.
  Proof. solve_proper. Qed.

  Program Definition enter_cond b e a v : D -n> iPropO Σ :=
    λne interp, (∀ lregs, ▷ □ interp_expr interp lregs (LCap RX b e a v))%I.
  Solve Obligations with solve_proper.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. solve_proper. Qed.

  Program Definition persistent_cond (P : D) : iPropO Σ := (⌜∀ w, Persistent (P w)⌝)%I.

  (* interp definitions *)
  Program Definition interp_ref_inv (a : Addr) (v : Version): D -n> iPropO Σ :=
    λne P, (∃ lw, (a,v) ↦ₐ lw ∗ P lw)%I.
  Solve Obligations with solve_proper.

  Notation interp_ref_invL la := (interp_ref_inv (laddr_get_addr la) (laddr_get_version la)).

  Definition logN : namespace := nroot .@ "logN".

  Definition interp_z : D := λne lw, ⌜match lw with LInt z => True | _ => False end⌝%I.

  Definition interp_cap_O : D := λne _, True%I.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne lw, (match lw with
              | LCap RO b e a v =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ P, inv (logN .@ (a,v)) (interp_ref_inv a v P)
                         ∗ persistent_cond P
                         ∗ read_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RW (interp : D) : D :=
    λne lw, (match lw with
              | LCap RW b e a v =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ P, inv (logN .@ (a,v)) (interp_ref_inv a v P)
                         ∗ persistent_cond P
                         ∗ read_cond P interp ∗ write_cond P interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne lw, (match lw with LCap RX b e a v =>
                         [∗ list] a ∈ (finz.seq_between b e),
                             ∃ P, inv (logN .@ (a,v)) (interp_ref_inv a v P)
                                    ∗ persistent_cond P
                                    ∗ read_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne lw, (match lw with
              | LCap E b e a v => enter_cond b e a v interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne lw, (match lw with LCap RWX b e a v =>
                           [∗ list] a ∈ (finz.seq_between b e),
                             ∃ P, inv (logN .@ (a,v)) (interp_ref_inv a v P)
                                    ∗ persistent_cond P
                                    ∗ read_cond P interp ∗ write_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
      ∃ P : D,  ⌜∀ w, Persistent (P w)⌝ ∗ seal_pred a P ∗ write_cond P interp)%I.
  Definition safe_to_unseal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e), ∃ P : D, seal_pred a P ∗ read_cond P interp)%I.

  Program Definition interp_sr (interp : D) : D :=
    λne lw, (match lw with
    | LSealRange p b e a =>
    (if permit_seal p then safe_to_seal interp b e else True) ∗ (if permit_unseal p then safe_to_unseal interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  Program Definition interp_sb (o : OType) (lw : LWord) :=
    (∃ P : LWord → iPropI Σ,  ⌜∀ lw, Persistent (P lw)⌝ ∗ seal_pred o P ∗ ▷ P lw)%I.

  Program Definition interp1 (interp : D) : D :=
    (λne lw,
    match lw return _ with
    | LInt _ => interp_z lw
    | LCap O b e a v => interp_cap_O lw
    | LCap RO b e a v => interp_cap_RO interp lw
    | LCap RW b e a v => interp_cap_RW interp lw
    | LCap RX b e a v => interp_cap_RX interp lw
    | LCap E b e a v => interp_cap_E interp lw
    | LCap RWX b e a v => interp_cap_RWX interp lw
    | LSealRange p b e a => interp_sr interp lw
    | LWSealed o sb => interp_sb o (LWSealable sb)
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
    destruct_word x0; auto. destruct c; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct_word x0; auto. destruct c; auto.
    solve_contractive.
  Qed.
  Global Instance enter_cond_contractive b e a v :
    Contractive (λ interp, enter_cond b e a v interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    solve_proper_prepare.
    destruct_word x0; auto. destruct c; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct_word x0; auto. destruct c; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct_word x0; auto. destruct c; auto.
    solve_contractive.
  Qed.
  Global Instance interp_sr_contractive :
    Contractive (interp_sr).
  Proof.
    solve_proper_prepare.
    destruct_word x0; auto.
    destruct (permit_seal sr), (permit_unseal sr);
    rewrite /safe_to_seal /safe_to_unseal;
    solve_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn lw.
    rewrite /interp1.
    destruct_word lw; [auto|..].
    + destruct c; first auto.
      - by apply interp_cap_RO_contractive.
      - by apply interp_cap_RW_contractive.
      - by apply interp_cap_RX_contractive.
      - by apply interp_cap_E_contractive.
      - by apply interp_cap_RWX_contractive.
   + by apply interp_sr_contractive.
   + rewrite /interp_sb. solve_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (lw : leibnizO LWord) :
    fixpoint (interp1) lw ≡ interp1 (fixpoint (interp1)) lw.
  Proof. exact: (fixpoint_unfold (interp1) lw). Qed.

  Definition interp : D := λne lw, (fixpoint (interp1)) lw.
  Definition interp_expression lregs : D := interp_expr interp lregs.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent lw : Persistent (interp lw).
  Proof. intros. destruct_word lw; simpl; rewrite fixpoint_interp1_eq; simpl.
         - apply _.
         - destruct c; repeat (apply exist_persistent; intros); try apply _.
         - destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ .
         - apply exist_persistent; intros P.
           unfold Persistent. iIntros "(Hpers & #Hs & HP)". iDestruct "Hpers" as %Hpers.
           (* use knowledge about persistence *)
           iAssert (<pers> ▷ P (LWSealable l))%I with "[ HP ]" as "HP".
           { iApply later_persistently_1. by iApply Hpers.  }
           iApply persistently_sep_2; iSplitR; auto.
           iApply persistently_sep_2; auto.
  Qed.

  Lemma interp_int n : ⊢ interp (LInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  Lemma read_allowed_inv (a' a b e: Addr) v p :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp (LCap p b e a v) →
      (∃ P, inv (logN .@ (a',v)) (interp_ref_inv a' v P) ∗ read_cond P interp ∗ if writeAllowed p then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
    try (iDestruct "Hinterp" as "[Hinterp Hinterpe]");
    try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "(Hinv & Hpers & Hiff)"
         ; [eauto|iExists P;iSplit;eauto]).
  Qed.

  Lemma read_allowed_region_inv (p : Perm) (b e a: Addr) (v : Version) :
    readAllowed p →
    ⊢ (interp (LCap p b e a v) →
       [∗ list] a ∈ (finz.seq_between b e),
        ∃ P, inv (logN .@ (a,v)) (interp_ref_inv a v P)
               ∗ read_cond P interp
               ∗ persistent_cond P
               ∗ (if writeAllowed p then write_cond P interp else emp))%I.
  Proof.
    iIntros (Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction;
      try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); cbn;
      try iFrame "Hinterp".
    all: iApply (big_sepL_impl with "Hinterp").
    all: iModIntro; iIntros (k x) "% H".
    all: iDestruct "H" as (P) "(? & ? & ?)"; iExists P; iFrame.
    all: iFrame.
  Qed.

  Lemma write_allowed_inv (a' a b e: Addr) v p :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp (LCap p b e a v) →
      inv (logN .@ (a', v)) (interp_ref_inv a' v interp))%I.
  Proof.
    iIntros (Hin Wa) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p; try contradiction.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #(Hpers & Hread & Hwrite) ]";[eauto|].
      iApply (inv_iff with "Hinv").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
    - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #(Hpers & Hread & Hwrite) ]";[eauto|].
      iApply (inv_iff with "Hinv").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]".
        iExists w. iFrame. iApply "Hwrite". iFrame.
  Qed.

  Definition writeAllowedWord (lw : LWord) : Prop :=
    match lw with
    | LCap p _ _ _ _ => writeAllowed p = true
    | _ => False
    end.

  Definition hasValidLAddress (lw : LWord) (a : Addr) (v : Version) : Prop :=
    match lw with
    | LCap p b e a' v' => (b ≤ a' ∧ a' < e)%Z ∧ a = a' ∧ v = v'
    | _ => False
    end.

  Definition writeAllowed_in_r_av (lregs : LReg) a v :=
    ∃ r (lw : LWord), lregs !! r = Some lw ∧ writeAllowedWord lw ∧ hasValidLAddress lw a v.

  Global Instance writeAllowedWord_dec lw: Decision (writeAllowedWord lw).
  Proof. destruct_word lw; try (right; solve [auto]). destruct c;simpl;apply _. Qed.

  Global Instance hasValidAddress_dec lw a v: Decision (hasValidLAddress lw a v).
  Proof. destruct_word lw; try (right; solve [auto]). destruct c;simpl;apply _. Qed.

  Global Instance writeAllowed_in_r_av_Decidable r a v: Decision (writeAllowed_in_r_av r a v).
  Proof.
    apply finite.exists_dec.
    intros x. destruct (r !! x) eqn:Hsome;
    first destruct (decide (writeAllowedWord l)), (decide (hasValidLAddress l a v)).
    left. eexists _; auto.
    all : (right; intros [w1 (Heq & ? & ?)]; inversion Heq; try congruence ).
  Qed.

  Global Instance writeAllowed_in_r_av_Persistent P r a v :
    Persistent (if decide (writeAllowed_in_r_av r a v) then write_cond P interp else emp)%I.
  Proof. intros. case_decide; apply _. Qed.

  Lemma read_allowed_inv_regs (a' a b e: Addr) v p lregs :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers lregs -∗
      interp (LCap p b e a v) -∗
      (∃ P, inv (logN .@ (a',v)) (interp_ref_inv a' v P) ∗ read_cond P interp
              ∗ (if decide (writeAllowed_in_r_av (<[PC:=LCap p b e a v]> lregs) a' v)
                 then write_cond P interp
                 else emp)
              ∗ persistent_cond P))%I.
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
          try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "(Hinv & Hpers & Hread & Hwrite)"
               ; [eauto|iExists P;eauto]).
      + simplify_map_eq.
        destruct (lregs !! reg) eqn:Hsome; rewrite Hsome in Hw; inversion Hw.
        destruct_word w; try by inversion Ha. destruct Ha as (Hwba & -> & ->).
        iSpecialize ("Hregvalid" $! _ _ n Hsome). simplify_eq. iClear "Hinterp".
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct c; try contradiction; inversion Hwa;
        try (iDestruct (extract_from_region_inv with "Hregvalid") as (P) "(Hinv & Hpers & Hread & Hwrite)";
             [eauto|iExists P;eauto]).
    - rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
      destruct p; try contradiction;
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "(Hinv & Hpers & [Hiff _ ] )"; [eauto|iExists P;iSplit;eauto]);
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "(Hinv & Hpers & Hiff)"; [eauto|iExists P;iSplit;eauto]).
  Qed.

  (* Lemma for allocating invariants in a region *)
  Lemma region_inv_alloc E l1 l2 :
    ([∗ list] la;lw ∈ l1;l2, la ↦ₐ lw ∗ interp lw) ={E}=∗
    ([∗ list] la;_ ∈ l1;l2, inv (logN .@ la) (interp_ref_invL la interp)).
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
      iFrame. iApply inv_alloc. iNext.
      iExists o. destruct a.
      iFrame.
  Qed.

  (* Get the validity of a region containing only integers *)
  Lemma region_integers_alloc E (b e a: Addr) v l p :
    Forall (λ lw, is_zL lw = true) l →
    PermFlowsTo RO p →
    ([∗ list] la;lw ∈ (fun a => (a,v)) <$> (finz.seq_between b e);l, la ↦ₐ lw) ={E}=∗
    interp (LCap p b e a v).
  Proof.
    iIntros (Hl Hp) "H".
    iMod (region_inv_alloc with "[H]") as "H".
    { iApply (big_sepL2_mono with "H").
      intros k v1 v2 ? Hlk. cbn. iIntros. iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hl Hlk) as HH.
      cbn in HH. destruct_word v2; try by inversion HH.
      rewrite fixpoint_interp1_eq //. }
    iDestruct (big_sepL2_length with "H") as %?.
    iDestruct (big_sepL2_to_big_sepL_l with "H") as "H"; auto.

    iModIntro. rewrite fixpoint_interp1_eq //.
    iDestruct (big_sepL_fmap (λ x : Addr, (x, v)) with "H") as "H".
    destruct p; cbn; eauto; try by inversion Hp.
    all: iApply (big_sepL_mono with "[H]"); iFrame.
    all: iIntros (k a' Hk) "H"; cbn.
    all: iExists (fixpoint interp1); iFrame.
    all: iSplit; [iPureIntro ; intros; apply interp_persistent|].
    all: try iSplit; iNext; iModIntro; eauto.
  Qed.

  (* Get the validity of a region containing only valid words *)
  Lemma region_valid_alloc E (b e a: Addr) v l p  :
    PermFlowsTo RO p →
    ([∗ list] w ∈ l, interp w) -∗
    ([∗ list] la;lw ∈ (fun a => (a,v)) <$> (finz.seq_between b e);l, la ↦ₐ lw) ={E}=∗
    interp (LCap p b e a v).
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
    iDestruct (big_sepL_fmap (λ x : Addr, (x, v)) with "H") as "H".
    destruct p; cbn; eauto; try by inversion Hp.
    all: iApply (big_sepL_mono with "H").
    all: iIntros (k a' Hk) "H"; cbn.
    all: iExists (fixpoint interp1); iFrame.
    all: iSplit; [iPureIntro ; intros; apply interp_persistent|].
    all: try iSplit; iNext; iModIntro; eauto.
  Qed.

  Definition compute_mask (E : coPset) (ls : gset LAddr) :=
    set_fold (λ l E, E ∖ ↑logN .@ l) E ls.

  Lemma compute_mask_difference (E : coPset) (la : gset LAddr) (a : LAddr) :
    a ∉ la ->
    (compute_mask E la) ∖ (↑logN .@ a) = (compute_mask (E  ∖ (↑logN .@ a)) la).
  Proof.
    rewrite /compute_mask. revert E a.
    induction la using set_ind_L; intros E a Ha_notin_la.
    { by rewrite !set_fold_empty. }
    do 2 (rewrite set_fold_disj_union_strong; [|set_solver..]).
    do 2 (rewrite set_fold_singleton).
    apply not_elem_of_union in Ha_notin_la; destruct_and ! Ha_notin_la.
    rewrite IHla; eauto.
    rewrite !difference_difference_l_L.
    by rewrite union_comm_L.
  Qed.

  Lemma compute_mask_union (E : coPset) (la : gset LAddr) (a : LAddr) :
    a ∉ la ->
    compute_mask E ({[a]} ∪ la) = (compute_mask E la) ∖ (↑logN .@ a).
  Proof.
    rewrite /compute_mask. revert E a.
    induction la using set_ind_L; intros E a Ha_notin_la.
    { by rewrite union_empty_r_L set_fold_empty set_fold_singleton. }
    rewrite IHla; eauto.
    apply not_elem_of_union in Ha_notin_la; destruct_and ! Ha_notin_la.
    do 2 (rewrite set_fold_disj_union_strong; [|set_solver..]).
    do 2 (rewrite set_fold_singleton).
    do 2 (rewrite -/(compute_mask _ X)).
    do 2 (rewrite compute_mask_difference //).
    rewrite !difference_difference_l_L.
    by rewrite union_comm_L.
  Qed.

  Lemma compute_mask_mono E ls :
    compute_mask E ls ⊆ E.
  Proof.
    rewrite /compute_mask. revert E.
    induction ls using set_ind_L; intros E.
    { by rewrite set_fold_empty. }
    rewrite set_fold_disj_union_strong; [|set_solver..].
    rewrite set_fold_singleton.
    etransitivity; [apply IHls|].
    set_solver.
  Qed.

  Lemma compute_mask_subseteq (E : coPset) (ls1 ls2 : gset LAddr) :
    ls2 ⊆ ls1 → compute_mask E ls1 ⊆ compute_mask E ls2.
  Proof.
    rewrite /compute_mask.
    revert E ls1.
    induction ls2 using set_ind_L.
    { intros E ls1 Hle. rewrite set_fold_empty. apply compute_mask_mono. }
    intros E ls1 Hle.
    rewrite set_fold_disj_union_strong; [|set_solver..].
    rewrite set_fold_singleton.
    assert (∃ Y, ls1 = {[x]} ∪ Y ∧ {[x]} ## Y) as [Y [-> Hdisj] ].
    { apply subseteq_disjoint_union_L. set_solver. }
    rewrite set_fold_disj_union_strong; [|set_solver..].
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
    rewrite set_fold_disj_union_strong; [|set_solver..].
    rewrite set_fold_singleton.
    rewrite not_elem_of_union in Hnin. destruct Hnin as [Hnin1 Hnin2].
    apply IHls; [|done].
    assert (logN.@l ## logN.@x).
    { apply ndot_ne_disjoint. set_solver. }
    set_solver.
  Qed.

  Lemma compute_mask_id E :
    compute_mask E ∅ = E.
  Proof. auto. Qed.

  Definition in_region (lw : LWord) (b e : Addr) (v : Version) :=
    match lw with
    | LCap p b' e' a v' => PermFlows RO p /\ (b <= b')%a /\ (e' <= e)%a /\ v = v'
    | _ => False
    end.

  Definition in_region_list (lw : LWord) (ls: list Addr) (v : Version) :=
    match lw with
    | LCap p b' e' a v' => PermFlows RO p /\ (forall x, b' <= x < e' -> x ∈ ls)%a /\ v = v'
    | _ => False
    end.

  Lemma region_valid_in_region_ind E (l1 l2 : list Addr) (v : Version) :
    Forall (λ a, ↑logN.@(a,v) ⊆ E) (l1 ++ l2) ->
    NoDup l1 -> NoDup l2 ->
    l2 ## l1 ->
    ([∗ list] a ∈ l1, inv (logN .@ (a,v)) (interp_ref_inv a v interp)) -∗
    ([∗ list] a ∈ l2, ∃ lw, (a,v) ↦ₐ lw ∗ ⌜is_zL lw = true \/ in_region_list lw (l1 ++ l2) v⌝) -∗
    |={compute_mask E (list_to_set ((λ a, (a,v)) <$> l1))}=>
          ([∗ list] a ∈ l1 ++ l2, inv (logN .@ (a,v)) (interp_ref_inv a v interp)).
  Proof.
    iIntros (Hforall Hdup1 Hdup2 Hdisj) "Hval Hl2".
    iInduction l2 as [|] "IH"
  forall (l1 Hdup2 Hforall Hdup1 Hdisj);iDestruct "Hval" as "#Hval".
    { simpl. rewrite app_nil_r. iFrame "#". iModIntro. done. }
    iDestruct "Hl2" as "[Hl Hl2]".
    iDestruct "Hl" as (w) "[Hl %Hcond]".
    apply NoDup_cons in Hdup2 as [Hni Hdup2].
    apply disjoint_cons in Hdisj as Hni'.
    apply disjoint_swap in Hdisj;auto.
    destruct Hcond as [Hint | Hin].
    - destruct w;try done.
      iMod (inv_alloc (logN .@ (a,v)) _ (interp_ref_inv a v interp) with "[Hl]") as "#Hlval".
      { iNext. iExists _. iFrame. iApply fixpoint_interp1_eq. eauto. }
      iMod (fupd_mask_subseteq (compute_mask E (list_to_set ( (λ a0 : Addr, (a0, v)) <$> (a :: l1))))) as "Hclose";
        [apply compute_mask_subseteq; set_solver|].
      iMod ("IH" $! (a :: l1) with "[] [] [] [] [] [Hl2]") as "HH";auto.
      { iPureIntro. simpl. rewrite Permutation_middle. auto. }
      { iPureIntro. apply NoDup_cons;auto. }
      { iSimpl. iFrame "#". }
      { iApply (big_sepL_mono with "Hl2"). iIntros (k x Hx) "Hc".
        iDestruct "Hc" as (w) "[Hx [Hw|%Hw]]";iExists _;iFrame;[iLeft;auto|].
        iRight. iPureIntro. destruct w;try done. destruct sb;try done.
        destruct Hw as (Hro & Hb & Hv). do 2 (split;auto).
        intros y Hy. simpl. rewrite Permutation_middle. apply Hb;auto. }
      iDestruct (big_sepL_app with "HH") as "[#Hl1 #Hl2]".
      iFrame "∗ #". iMod ("Hclose"). auto.
    - destruct w;try done. destruct sb;try done. destruct Hin as (Hro & Hin & <-).
      iApply big_sepL_app. iFrame "#".
      iMod (inv_alloc_open (logN .@ (a,v)) _ (interp_ref_inv a v interp)) as "[#Ha Hcls]".
      { apply compute_mask_elem_of.
        { revert Hforall; rewrite Forall_forall =>Hforall. apply Hforall.
          apply elem_of_app;right;apply elem_of_cons;auto. }
        apply not_elem_of_list_to_set.
        intro Hcontra. apply elem_of_list_fmap in Hcontra.
        destruct Hcontra as (a' & Heq & Hcontra); simplify_pair_eq; auto.
      }
      iFrame "#".
      iMod (fupd_mask_subseteq (compute_mask E (list_to_set ( (λ a0 : Addr, (a0, v)) <$> (a :: l1))))) as "Hclose".
      { rewrite /compute_mask.
        rewrite list_to_set_cons union_comm_L.
        replace ((fix go (l : list Addr) : list (Addr * Version) :=
           match l with
           | [] => []
           | x :: l0 => (x, v) :: go l0
           end) l1) with ((λ a0 : Addr, (a0, v)) <$> l1) by reflexivity.
        rewrite (set_fold_disj_union_strong _ _ _ (list_to_set ((λ a0 : Addr, (a0, v)) <$> l1)) {[(a,v)]}).
        - rewrite set_fold_singleton. done.
        - set_solver.
        - set_solver. }
      iMod ("IH" $! (a :: l1) with "[] [] [] [] [] [Hl2]") as "HH";auto.
      { iPureIntro. simpl. rewrite Permutation_middle. auto. }
      { iPureIntro. apply NoDup_cons;auto. }
      { iSimpl. iFrame "#". }
      { iApply (big_sepL_mono with "Hl2"). iIntros (k x Hx) "Hc".
        iDestruct "Hc" as (w) "[Hx [Hw|%Hw]]";iExists _;iFrame;[iLeft;auto|].
        iRight. iPureIntro. destruct w;try done. destruct sb;try done.
        destruct Hw as (Hro' & Hb & Hv). do 2 (split;auto).
        intros y Hy. simpl. rewrite Permutation_middle. apply Hb;auto. }
      iMod "Hclose".
      iSimpl in "HH";iDestruct "HH" as "[#Hav HH]".
      iDestruct (big_sepL_app with "HH") as "[#Hl1v #Hl2v]".
      iMod ("Hcls" with "[Hl]");[|by iFrame "#"].
      iNext. iExists _. iFrame.
      iApply fixpoint_interp1_eq. destruct p;try done.
      all: iApply big_sepL_forall; iIntros (k x Hlook); iExists interp.
      all: iSplit;
        [ | iSplit; [iPureIntro ; intros; apply interp_persistent|] ]
      ; [|(try iSplitR);iIntros (?);iNext;iModIntro;auto].
      all: apply elem_of_list_lookup_2,elem_of_finz_seq_between,Hin,elem_of_app in Hlook.
      all: destruct Hlook as [Hl1 | [->|Hl2]%elem_of_cons];
          [iDestruct (big_sepL_elem_of with "Hl1v") as "?";eauto|iFrame "#"|
            iDestruct (big_sepL_elem_of with "Hl2v") as "?";eauto].
      Unshelve. all: apply _.
  Qed.

  Lemma region_valid_in_region E (b e a: Addr) v l p  :
    Forall (λ a0 : Addr, ↑logN.@(a0, v) ⊆ E) (finz.seq_between b e) ->
    PermFlowsTo RO p →
    Forall (λ lw, is_zL lw = true \/ in_region lw b e v) l ->
    ([∗ list] a;w ∈ finz.seq_between b e;l, (a,v) ↦ₐ w) ={E}=∗
    interp (LCap p b e a v).
  Proof.
    iIntros (Hsub Hperm Hl) "Hl".
    iDestruct (region_valid_in_region_ind E [] (finz.seq_between b e) v with "[] [Hl]") as "HH".
    { rewrite app_nil_l. auto. }
    { apply NoDup_nil. auto. }
    { apply finz_seq_between_NoDup. }
    { eapply disjoint_nil_r. exact 0%a. }
    { auto. }
    { rewrite app_nil_l.
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iApply big_sepL2_to_big_sepL_l;[apply Hlen|].
      iApply (big_sepL2_mono with "Hl").
      iIntros (k y1 y2 Hy1 Hy2) "Hl".
      iExists _; iFrame. iPureIntro.
      rewrite Forall_lookup in Hl.
      apply Hl in Hy2 as [Hy2|Hy2];auto.
      right. destruct y2;try done. destruct sb;try done.
      destruct Hy2 as (Hro' & Hb & Hv & ->). do 2 (split;auto).
      intros x Hx. apply elem_of_finz_seq_between.
      solve_addr. }
    { rewrite list_to_set_nil compute_mask_id app_nil_l. iMod "HH".
      iModIntro.
      iApply fixpoint_interp1_eq. destruct p;try done.
     all: iApply (big_sepL_mono with "HH");iIntros (k y Hy) "Hl";
        try iExists _;iFrame;iSplit;[iPureIntro; apply interp_persistent|];try iSplit;iIntros (?);auto. }
  Qed.

  Lemma region_seal_pred_interp E (b e a: OType) b1 b2 :
    ([∗ list] o ∈ finz.seq_between b e, seal_pred o interp) ={E}=∗
    interp (LSealRange (b1,b2) b e a).
  Proof.
    remember (finz.seq_between b e) as l eqn:Hgen. rewrite Hgen; revert Hgen.
    generalize b e. clear b e.
    induction l as [|hd tl IH].
    - iIntros (b e Hfinz) "_ !>".
      rewrite /interp fixpoint_interp1_eq /= /safe_to_seal /safe_to_unseal.
      rewrite -Hfinz. destruct b1, b2; iSplit; done.
    - iIntros (b e Hfinz).
      assert (b < e)%ot as Hlbe.
      {destruct (decide (b < e)%ot) as [|HF]; first auto. rewrite finz_seq_between_empty in Hfinz; [inversion Hfinz | solve_addr  ]. }
      apply finz_cons_tl in Hfinz as (b' & Hplus & Hfinz).
      specialize (IH b' e Hfinz). rewrite (finz_seq_between_split _ b' _).
      2 : split; solve_addr.
      iIntros "[#Hfirst Hca]".
      iMod (IH with "Hca") as "Hca". iModIntro.
      rewrite /interp !fixpoint_interp1_eq /= /safe_to_seal /safe_to_unseal.
      rewrite !(finz_seq_between_split b b' e). 2: { split ; solve_addr. }
      iDestruct "Hca" as "[Hseal Hunseal]".
      iSplitL "Hseal"; [destruct b1| destruct b2]; iFrame.
      all: iApply (big_sepL_mono with "Hfirst").
      all: iIntros (k a' Hk) "H"; cbn.
      all: iExists _; iFrame; auto.
      iSplit; auto. iPureIntro; apply _.
  Qed.

  (* Get the validity of sealing capabilities if we can allocate an arbitrary predicate, and can hence choose interp itself as the sealing predicate *)
  Lemma region_can_alloc_interp E (b e a: OType) b1 b2:
    ([∗ list] o ∈ finz.seq_between b e, can_alloc_pred o) ={E}=∗
    interp (LSealRange (b1,b2) b e a).
  Proof.
    iIntros "Hca".
    iDestruct (big_sepL_mono with "Hca") as "Hca".
    iIntros (k a' Hk) "H". iDestruct (seal_store_update_alloc _ interp  with "H") as "H". iExact "H".

    iDestruct (big_sepL_bupd with "Hca") as "Hca".
    iMod "Hca".
    by iApply region_seal_pred_interp.
  Qed.

End logrel.
