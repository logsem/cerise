From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region logrel rules_binary_base.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.


Ltac auto_equiv_binary :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | H : _ = _ ∧ _ = _ |- _ => destruct H as [? ?]
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv_binary).

(** interpb : is a binary logical relation. *)
Section logrel.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types w : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition spec_registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↣ᵣ w)%I.

  Definition full_map (regpair : Reg * Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (regpair.1 !! r) ∧ is_Some (regpair.2 !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
    λne (regpair : prodO (leibnizO Reg) (leibnizO Reg)), (full_map regpair ∧
                                                          ∀ (r : RegName), (⌜r ≠ PC⌝ → interp (regpair.1 !r! r,regpair.2 !r! r)))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ∃ r, ⤇ of_val HaltedV ∗ full_map r ∧ registers_mapsto r.1 ∗ spec_registers_mapsto r.2 ∗ na_own logrel_nais ⊤ }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne w, (interp_reg interp r
             ∗ registers_mapsto (<[PC:=w.1]> r.1)
             ∗ spec_registers_mapsto (<[PC:=w.2]> r.2)
             ∗ na_own logrel_nais ⊤
             ∗ ⤇ Seq (Instr Executable) -∗
             ⌜match w.1,w.2 with WCap _,WCap _ => True | _,_ => False end⌝ ∧ interp_conf))%I.
  Solve All Obligations with solve_proper.

  (* condition definitions *)
  Program Definition read_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (w w' : Word), P (w,w') -∗ interp (w,w'))%I.
  Solve Obligations with solve_proper.
  Global Instance read_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) read_cond.
  Proof. solve_proper. Qed.

  Program Definition write_cond (P : D) : D -n> iPropO Σ :=
    λne interp, (▷ □ ∀ (w w' : Word), interp (w,w') -∗ P (w,w'))%I.
  Solve Obligations with solve_proper.
  Global Instance write_cond_ne n :
    Proper (dist n ==> dist n ==> dist n) write_cond.
  Proof. solve_proper. Qed.

  Program Definition enter_cond b e a b' e' a' : D -n> iPropO Σ :=
    λne interp, (∀ r, ▷ □ interp_expr interp r (WCap (RX,b,e,a),WCap (RX,b',e',a')))%I.
  Solve Obligations with solve_proper.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. solve_proper. Qed.

  (* interp definitions *)
  Program Definition interp_ref_inv (a : Addr) : D -n> iPropO Σ := λne P, (∃ (w w': Word), a ↦ₐ w ∗ a ↣ₐ w' ∗ P (w,w'))%I.
  Solve Obligations with solve_proper.

  Definition logN : namespace := nroot .@ "logN".

  Definition z_cond : (Word * Word) -> Prop := λ w, match w with (WInt z,WInt z') => (z = z')%Z | _ => False end.
  Program Definition interp_z : D := λne w, ⌜z_cond w⌝%I.
  Solve Obligations with solve_proper.

  Program Definition interp_cap_O (interp : D) : D :=
    λne w, (match w with
            | (WCap (O,b,e,a),WCap (O,b',e',a')) => ⌜b = b' ∧ e = e' ∧ a = a'⌝
            | _ => False
            end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne w, (match w with
            | (WCap (RO,b,e,a),WCap (RO,b',e',a')) =>
              ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
              [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
            | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RW (interp : D) : D :=
    λne w, (match w with
            | (WCap (RW,b,e,a),WCap (RW,b',e',a')) =>
              ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
            | _ => False
            end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne w, (match w with (WCap (RX,b,e,a),WCap (RX,b',e',a')) =>
                         ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                         [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne w, (match w with
              | (WCap (E,b,e,a),WCap (E,b',e',a')) => ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗ enter_cond b e a b' e' a' interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne w, (match w with (WCap (RWX,b,e,a),WCap (RWX,b',e',a')) =>
                         ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                           [∗ list] a ∈ (region_addrs b e), ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp
             | _ => False end)%I.
  Solve All Obligations with solve_proper.


  Program Definition interp1 (interp : D) : D :=
    (λne w,
    match w return _ with
    | (WInt _, WInt _) => interp_z w
    | (WCap (O, b, e, a),WCap (O, b', e', a')) => interp_cap_O interp w
    | (WCap (RO, b, e, a),WCap (RO, b', e', a')) => interp_cap_RO interp w
    | (WCap (RW, b, e, a),WCap (RW, b', e', a')) => interp_cap_RW interp w
    | (WCap (RX, b, e, a),WCap (RX, b', e', a')) => interp_cap_RX interp w
    | (WCap (E, b, e, a),WCap (E, b', e', a')) => interp_cap_E interp w
    | (WCap (RWX, b, e, a),WCap (RWX, b', e', a')) => interp_cap_RWX interp w
    | _ => False
    end)%I.
  Solve All Obligations with solve_proper.

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
    destruct x0; auto. destruct o,o0;auto. destruct c, p, p, p,c0,p,p,p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct o,o0;auto. destruct c, p, p, p,c0,p,p,p; auto.
    solve_contractive.
  Qed.
  Global Instance enter_cond_contractive b e a b' e' a'  :
    Contractive (λ interp, enter_cond b e a b' e' a' interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct o,o0;auto. destruct c, p, p, p,c0,p,p,p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct o,o0;auto. destruct c, p, p, p,c0,p,p,p; auto.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct x0; auto. destruct o,o0;auto. destruct c, p, p, p,c0,p,p,p; auto.
    solve_contractive.
  Qed.


  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn [w w0].
    rewrite /interp1.
    destruct w,w0; [auto..|].
    destruct c,p,p,p,c0,p,p,p; try auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RX_contractive.
    - by apply interp_cap_E_contractive.
    - by apply interp_cap_RWX_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (x : prodO (leibnizO Word) (leibnizO Word)) :
    fixpoint (interp1) x ≡ interp1 (fixpoint (interp1)) x.
  Proof. exact: (fixpoint_unfold (interp1) x). Qed.

  Definition interp : D := (fixpoint (interp1)).
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent w : Persistent (interp w).
  Proof. intros. destruct w as [w w0]. destruct w,w0; simpl; rewrite fixpoint_interp1_eq; simpl;
         try destruct c,p,p,p;try apply _;destruct c0,p,p,p; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Lemma read_allowed_inv (a'' a b e a' b' e' : Addr) p p' :
    (b ≤ a'' ∧ a'' < e)%Z →
    readAllowed p →
    ⊢ (interp (WCap (p,b,e,a),WCap (p',b',e',a')) →
     (∃ P, inv (logN .@ a'') (interp_ref_inv a'' P) ∗ read_cond P interp ∗ if writeAllowed p then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,p'; try contradiction; try done;
    try (iDestruct "Hinterp" as "[(%&%&%) Hinterp]"); simplify_eq;
    try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
  Qed.

  Lemma write_allowed_inv (a'' a b e a' b' e' : Addr) p p' :
    (b ≤ a'' ∧ a'' < e)%Z →
    writeAllowed p →
    ⊢ (interp (WCap (p,b,e,a), WCap (p',b',e',a')) →
     inv (logN .@ a'') (interp_ref_inv a'' interp))%I.
  Proof.
    iIntros (Hin Wa) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,p'; try contradiction; try done.
    - iDestruct "Hinterp" as "[(%&%&%) Hinterp]". simplify_eq.
      iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "Hinv []").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w w') "(Ha' & Ha'' & HP)".
        iExists w,w'. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w w') "(Ha' & Ha'' & HP)".
        iExists w,w'. iFrame. iApply "Hwrite". iFrame.
    - iDestruct "Hinterp" as "[(%&%&%) Hinterp]". simplify_eq.
      iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|].
      iApply (inv_iff with "Hinv []").
      iNext. iModIntro. iSplit.
      + iIntros "HP". iDestruct "HP" as (w w') "(Ha' & Ha'' & HP)".
        iExists w,w'. iFrame. iApply "Hread". iFrame.
      + iIntros "HP". iDestruct "HP" as (w w') "(Ha' & Ha'' & HP)".
        iExists w,w'. iFrame. iApply "Hwrite". iFrame.
  Qed.

  Global Instance writeAllowed_in_r_a_Persistent P r a: Persistent (if decide (writeAllowed_in_r_a r a) then write_cond P interp else emp)%I.
  Proof. intros. case_decide; apply _. Qed.

  Lemma read_allowed_inv_regs (a'' a b e a' b' e' : Addr) p p' r :
    (b ≤ a'' ∧ a'' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers r -∗
    interp (WCap (p,b,e,a),WCap (p',b',e',a')) -∗
     (∃ P, inv (logN .@ a'') (interp_ref_inv a'' P) ∗ read_cond P interp ∗ if decide (writeAllowed_in_r_a (<[PC:=WCap (p,b,e,a)]> r.1) a'') then write_cond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "#Hregs #Hinterp".
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[% Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as [reg [Hwa Ha] ].
      destruct (decide (reg = PC)).
      + rewrite /RegLocate in Hwa Ha. simplify_map_eq.
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p,p'; try contradiction; try done;
        iDestruct "Hinterp" as "[(%&%&%) Hinterp]";simplify_eq;
          try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
        rewrite lookup_insert in Hwa;inversion Hwa.
        rewrite lookup_insert in Hwa;inversion Hwa.
      + rewrite /RegLocate in Hwa Ha. rewrite lookup_insert_ne// in Hwa,Ha.
        destruct (r.1 !! reg) eqn:Hsome;rewrite Hsome in Ha Hwa; [|inversion Ha].
        assert (is_Some(r.2 !! reg)) as [? ?];[by destruct H0 with reg|].
        destruct w;[inversion Ha|]. destruct c,p0,p0. destruct Ha as [Hwba ->].
        iSpecialize ("Hregvalid" $! _ n). rewrite /RegLocate Hsome H1. iClear "Hinterp".
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct x; [destruct p0;done|].
        destruct p0,p',c,p0,p0,p0; try contradiction; try done; inversion Hwa;
        try (iDestruct "Hregvalid" as "[(%&%&%) Hregvalid]";simplify_eq);
        try (iDestruct (extract_from_region_inv with "Hregvalid") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
    - rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
      destruct p,p'; try contradiction; try done;
        iDestruct "Hinterp" as "[(%&%&%) Hinterp]";simplify_eq;
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv [Hiff _] ]"; [eauto|iExists P;iSplit;eauto]);
        try (iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv Hiff]"; [eauto|iExists P;iSplit;eauto]).
  Qed.

  (* Lemma for allocating invariants in a region *)
  Lemma region_inv_alloc E l1 l2 :
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v.1 ∗ k ↣ₐ v.2 ∗ interp v) ={E}=∗
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
      iFrame. iApply inv_alloc. iNext. iExists p.1,p.2. destruct p; iFrame.
  Qed.

  (* Two words in the binary value relation will be syntactically equivalent *)
  Lemma interp_eq (w w' : Word) :
    interp (w,w') -∗ ⌜w = w'⌝.
  Proof.
    iIntros "Hv".
    rewrite fixpoint_interp1_eq /=.
    destruct w,w';try done. by iDestruct "Hv" as %->. destruct c,p,p,p;done.
    destruct c,p,p,p,c0,p,p,p;try done;[by iDestruct "Hv" as %(->&->&->)|by iDestruct "Hv" as "[Hv _]"; iDestruct "Hv" as %(->&->&->)..].
  Qed.

  Lemma interp_reg_eq (r r' : Reg) (w : Word) :
    interp_registers (r,r') -∗ ⌜<[PC:=w]> r = <[PC:=w]> r'⌝.
  Proof.
    iIntros "Hv".
    rewrite map_eq'. iIntros (reg v).
    rewrite iff_to_and. iSplit.
    - iIntros (Hin).
      iDestruct "Hv" as "[% Hv]".
      simpl in *. destruct H0 with reg as [_ [? ?] ].
      destruct (decide (reg = PC));[by subst;rewrite lookup_insert;rewrite lookup_insert in Hin|].
      rewrite lookup_insert_ne// in Hin. rewrite lookup_insert_ne//.
      iSpecialize ("Hv" $! reg n). rewrite /RegLocate H1 Hin.
      iDestruct (interp_eq with "Hv") as %->. auto.
    - iIntros (Hin).
      iDestruct "Hv" as "[% Hv]".
      simpl in *. destruct H0 with reg as [ [? ?] _].
      destruct (decide (reg = PC));[by subst;rewrite lookup_insert; rewrite lookup_insert in Hin|].
      rewrite lookup_insert_ne// in Hin; rewrite lookup_insert_ne//.
      iSpecialize ("Hv" $! reg n). rewrite /RegLocate H1 Hin.
      iDestruct (interp_eq with "Hv") as %->. auto.
  Qed.

  Lemma interp_reg_dupl (r r' : Reg) :
    interp_registers (r,r') -∗ interp_registers (r,r).
  Proof.
    iIntros "[% #Hv]". rewrite /interp_registers /=.
    iSplit;[iPureIntro;intros x; destruct H0 with x;eauto|].
    iIntros (reg Hne). iDestruct ("Hv" $! reg Hne) as "Hval".
    destruct H0 with reg as [ [? Hreg1] [? Hreg2] ].
    rewrite /RegLocate Hreg1 Hreg2.
    iDestruct (interp_eq with "Hval") as %->. iFrame "Hval".
  Qed.

End logrel.
