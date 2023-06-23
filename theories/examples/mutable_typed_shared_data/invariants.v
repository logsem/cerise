From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.

Section invariants.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Definition sealN : namespace := nroot .@ "seal".

  Definition seal_state ι addr τ (φ: Addr → iPropI Σ) Φ {Hpers : ∀ w, Persistent (Φ w)} : iProp Σ :=
    na_inv logrel_nais ι (φ addr) ∗ seal_pred τ Φ.

  Definition valid_sealed w τ Φ :=
    (∃ sb, ⌜w = WSealed τ sb⌝ ∗ ⌜∀ w : leibnizO Word, Persistent (Φ w)⌝ ∗ seal_pred τ Φ ∗ Φ (WSealable sb))%I.

  Global Instance valid_sealed_persistent w o Φ: Persistent (valid_sealed w o Φ).
  Proof.
    Import uPred. (* exist_persistent *)

    apply exist_persistent; intros sb.
    unfold Persistent.
    iIntros "(%Hw & %Hpers & #Hs & HP)".

    (* use knowledge about persistence *)
    iAssert (<pers> Φ (WSealable sb))%I with "[HP]" as "HP".
    { by iApply Hpers. }

    repeat (iApply persistently_sep_2; iSplitR); auto.
  Qed.

  Lemma interp_valid_sealed sb o:
    interp (WSealed o sb) -∗ ▷ ∃ Φ, valid_sealed (WSealed o sb) o Φ.
  Proof.
    iIntros "Hsl".
    rewrite fixpoint_interp1_eq /=.
    iDestruct "Hsl" as (Φ) "(%Hpers & Hpred & Hφ)".
    iExists Φ, sb.
    by repeat iSplit.
  Qed.

  Lemma seal_state_valid_sealed_pred_eq ι addr τ w φ Φ Φ' {Hpers : ∀ w, Persistent (Φ w)}:
    seal_state ι addr τ φ Φ -∗ valid_sealed w τ Φ' -∗  (∀ w, ▷ (Φ w ≡ Φ' w)).
  Proof.
    iIntros "HsealLL Hvs".
    iDestruct "HsealLL" as "[_ Hsp]".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants.

Section invariants_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Notation "a ↪ₐ w" := (mapsto (L := Addr) (V := Word) a DfracDiscarded w) (at level 20) : bi_scope.

  Definition int_sealed: Word → iProp Σ :=
    (λ w, (∃ a_cap w', ⌜w = WCap RW a_cap (a_cap ^+ 1)%a a_cap⌝ ∗ a_cap ↪ₐ w' ∗ ⌜is_z w'⌝)%I).

  Definition seal_state_int ι addr τ: iProp Σ :=
    seal_state ι addr τ (λ addr, ∃ v, addr ↦ₐ v ∗ ⌜is_z v⌝)%I int_sealed.
  Definition valid_sealed_int w τ := valid_sealed w τ int_sealed.

  Instance int_sealed_timeless w : Timeless (int_sealed w).
  Proof. apply _. Qed.

  Instance int_sealed_persistent w : Persistent (int_sealed w).
  Proof. apply _. Qed.

  Lemma seal_state_int_valid_sealed_pred_eq ι addr τ w Φ:
    seal_state_int ι addr τ -∗ valid_sealed w τ Φ -∗  (∀ w, ▷ (int_sealed w ≡ Φ w)).
  Proof.
    iApply seal_state_valid_sealed_pred_eq.
  Qed.

End invariants_int.
