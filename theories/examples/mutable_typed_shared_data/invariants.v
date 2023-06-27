From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples Require Import arch_sealing.

(* This section redefines useful definitions from `arch_sealing` along with further explanations. *)
Section invariants.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (*  *)
  (* Note: *)
  Definition seal_pred τ Φ {Hpers : ∀ w, Persistent (Φ w)} := seal_pred τ Φ.

  (* `seal_state` is the combination of `seal_pred` and a specific invariant. *)
  (* This invariant pin `WSealRange` in memory to retrieve an access to it. *)
  (* > In our case, `WSealRange` is already pinned and easily accessible. *)
  (* For simplicity, this example will only use `seal_pred`. *)

  (* Fact that the value `w` has been validly sealed satisfying a `Φ` predicate. *)
  (* This definition is close to `interp_sb` and can be obtained using `interp_valid_sealed`. *)
  Definition valid_sealed w τ Φ := valid_sealed w τ Φ.

  (* Something sealed is enough to know that the sealed satisfies a predicate `Φ`. *)
  (* The predicate `Φ` can be refined to a concrete predicate with `seal_pred_valid_sealed_eq`. *)
  Definition interp_valid_sealed sb τ := interp_valid_sealed sb τ.

  (* Concludes that `Φ` ≡ `Φ'` if `seal_state` and `valid_sealed` have the same `τ` OType. *)
  (* Note: This is a more-generic version of `sealLL_valid_sealed_pred_eq` *)
  Lemma seal_pred_valid_sealed_eq τ w Φ Φ' {Hpers : ∀ w, Persistent (Φ w)} :
    seal_store.seal_pred τ Φ -∗ valid_sealed w τ Φ' -∗ (∀ w, ▷ (Φ w ≡ Φ' w)).
  Proof.
    iIntros "Hsp Hvs".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants.

Section invariants_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Definition seal_intN : namespace := nroot .@ "seal".

  Definition int_sealed : Word → iProp Σ :=
    (λ w, (∃ a_cap, ⌜w = WCap RW a_cap (a_cap ^+ 1)%a a_cap⌝
                         ∗ na_inv logrel_nais seal_intN (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝))%I).

  Instance int_sealed_persistent w : Persistent (int_sealed w).
  Proof. apply _. Qed.

  (* Integer-specific redefinitions *)
  Definition seal_pred_int τ := seal_pred τ int_sealed.
  Definition valid_sealed_int w τ := valid_sealed w τ int_sealed.

  Lemma seal_state_int_valid_sealed_pred_eq τ w Φ :
    seal_pred τ int_sealed -∗ valid_sealed w τ Φ -∗  (∀ w, ▷ (int_sealed w ≡ Φ w)).
  Proof.
    iIntros "Hsp Hvs".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants_int.
