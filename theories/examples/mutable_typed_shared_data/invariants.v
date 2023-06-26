From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples Require Import arch_sealing.

(* This section defines more general definitions and clearer explanations than `arch_sealing`. *)
Section invariants.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* Fact that the value `w` has been validly sealed satisfying a `Φ` predicate. *)
  (* This definition is close to `interp_sb` and can be obtained using `interp_valid_sealed`. *)
  Definition valid_sealed w τ Φ := valid_sealed w τ Φ.

  (* Something sealed is enough to know that the sealed satisfies a predicate `Φ`. *)
  (* The predicate `Φ` can be refined to a concrete predicate with `seal_state_valid_sealed_pred_eq`. *)
  Definition interp_valid_sealed sb τ := interp_valid_sealed sb τ.

  (* TODO: The τ OType is *NOT* in φ - Is this a problem? *)
  Definition seal_state ι addr (φ : Addr → iPropI Σ) τ Φ {Hpers : ∀ w, Persistent (Φ w)} :=
    (na_inv logrel_nais ι (φ addr) ∗ seal_pred τ Φ)%I.

  (* Concludes that `Φ` ≡ `Φ'` if `seal_state` and `valid_sealed` have the same `τ` OType. *)
  Definition seal_state_valid_sealed_pred_eq ι addr τ w Φ Φ' {Hpers : ∀ w, Persistent (Φ w)} :=
    sealLL_valid_sealed_pred_eq ι addr τ w Φ Φ'.

End invariants.

(* This section refines the definitions specifically for [load_int] and [store_int]. *)
Section invariants_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Notation "a ↪ₐ w" := (mapsto (L := Addr) (V := Word) a DfracDiscarded w) (at level 20) : bi_scope.

  Definition sealN : namespace := nroot .@ "seal".

  Definition int_sealed: Word → iProp Σ :=
    (λ w, (∃ a_cap w', ⌜w = WCap RW a_cap (a_cap ^+ 1)%a a_cap⌝ ∗ a_cap ↪ₐ w' ∗ ⌜is_z w'⌝)%I).

  Instance int_sealed_timeless w : Timeless (int_sealed w).
  Proof. apply _. Qed.

  Instance int_sealed_persistent w : Persistent (int_sealed w).
  Proof. apply _. Qed.

  (* TODO: ⌜is_z w⌝ should not be there *)
  Definition seal_state_int ι addr τ: iProp Σ :=
    seal_state ι addr (λ addr, ∃ w, addr ↦ₐ w ∗ ⌜is_z w⌝)%I τ int_sealed.

  Definition valid_sealed_int w τ := valid_sealed w τ int_sealed.

  Lemma seal_state_int_valid_sealed_pred_eq ι addr τ w Φ :
    seal_state_int ι addr τ -∗ valid_sealed w τ Φ -∗  (∀ w, ▷ (int_sealed w ≡ Φ w)).
  Proof.
    iIntros "HsealLL Hvs".
    iDestruct "HsealLL" as "[_ Hsp]".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants_int.
