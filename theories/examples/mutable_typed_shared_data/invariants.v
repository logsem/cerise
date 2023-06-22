From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.

Section invariants.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Notation "a ↪ₐ w" := (mapsto (L := Addr) (V := Word) a DfracDiscarded w) (at level 20) : bi_scope.

  Definition isIntSealed_int w': Word → iProp Σ :=
    (λ w, (∃ a_cap, ⌜w = WCap RW a_cap (a_cap ^+ 1)%a a_cap⌝ ∗ a_cap ↪ₐ w' ∗ ⌜is_z w'⌝)%I).

  Definition isIntSealed: Word → iProp Σ := (λ w, (∃ w', isIntSealed_int w' w))%I.

  Definition seal_state ι addr τ {Hpers : ∀ w, Persistent (isIntSealed w)} : iProp Σ
    := na_inv logrel_nais ι
         (∃ τ_e, addr ↦ₐ WSealRange (true, true) τ τ_e τ ∗ ⌜(τ < τ_e)%ot⌝)%I
       ∗ seal_pred τ isIntSealed.

  Definition sealN : namespace := nroot .@ "seal".

  Lemma isIntSealed_alloc a_cap w:
    a_cap ↦ₐ w ∗ ⌜is_z w⌝ ==∗ isIntSealed_int w (WCap RW a_cap (a_cap ^+ 1)%a a_cap).
  Proof.
    iIntros "(Ha & Hw)".
    iMod (mapsto_persist with "Ha") as "#Ha".
    iModIntro. iExists _; eauto.
  Qed.

  Instance isIntSealed_timeless w : Timeless (isIntSealed w).
  Proof. apply _. Qed.

  Instance isIntSealed_persistent w : Persistent (isIntSealed w).
  Proof. apply _. Qed.

End invariants.
