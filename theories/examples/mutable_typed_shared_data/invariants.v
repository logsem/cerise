From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.
From cap_machine.examples Require Import arch_sealing.

(* This section redefines useful definitions from `arch_sealing` along with further explanations. *)
Section invariants.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* `seal_pred` denotes that the sealed satisfies a predicate `Φ`, for a specific `τ` OType. *)
  (* Note: `seal_pred` does not need to be put inside an invariant, because it is `Persistent`. *)
  Definition seal_pred τ Φ {Hpers : ∀ w, Persistent (Φ w)} := seal_store.seal_pred τ Φ.

  (* Note: `arch_sealing.seal_state` is the combination of `seal_pred` and a invariant. *)
  (* > This invariant pins `WSealRange` in memory to retrieve an access to it. *)
  (* For simplicity, we will explicitly split `seal_pred` and the invariant on `WSealRange`. *)

  (* Fact that the value `w`, if `interp w`, has been validly sealed satisfying a `Φ` predicate. *)
  Definition valid_sealed w τ Φ := arch_sealing.valid_sealed w τ Φ.

  (* Lemma: If something is sealed, it is sufficient to know that the sealed satisfies a predicate `Φ`. *)
  Definition interp_valid_sealed sb τ := arch_sealing.interp_valid_sealed sb τ.

  (* Lemma: Concludes that `Φ ≡ Φ'` if `seal_pred τ Φ` and `valid_sealed w τ Φ` have the same `τ` OType. *)
  (* Note: This is a more generic version of `arch_sealing.sealLL_valid_sealed_pred_eq` *)
  Lemma seal_pred_valid_sealed_eq τ w Φ Φ' {Hpers : ∀ w, Persistent (Φ w)} :
    seal_pred τ Φ -∗ valid_sealed w τ Φ' -∗ (∀ w, ▷ (Φ w ≡ Φ' w)).
  Proof.
    iIntros "Hsp Hvs".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants.

(* The proof guideline for accessing the sealed predicate is as follows: *)

(* We assume: *)
(*  - `seal_pred τ φ`, for some known `φ` (e.g: `sealed_int`) *)
(*  - `interp w`, where `w = WSealed τ scap` for any given `scap` *)

(* 1. Using `interp_valid_sealed`, we can get `▷ valid_sealed (WSealed τ scap) τ Φ`. *)
(* 2. `Φ` is currently unknown, we have to use `seal_pred_valid_sealed_eq` to retrieve `φ`. *)

Section invariants_int.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  Definition seal_intN : namespace := nroot .@ "seal".

  (* `sealed_int` is the sealed predicate of a sealed buffer containing an integer. *)
  Definition sealed_int : Word → iProp Σ :=
    λ w, na_inv logrel_nais seal_intN
           (∃ a_cap, ⌜w = WCap RW a_cap (a_cap ^+ 1)%a a_cap⌝ ∗ (∃ w, a_cap ↦ₐ w ∗ ⌜is_z w⌝))%I.

  (* Note: `sealed_int` is not `Timeless` because of the use of the non-atomic invariant. *)
  (* > In our case, any later can be stripped at time. *)
  (* One could use `a_cap ↦ₐ{DFracDiscarded} w` to avoid using the non-atomic invariant. *)
  (* > However, this denies the right to write to `a_cap` making it read-only. *)

  (* Required by `seal_pred`: `sealed_int` is `Persistent`. *)
  Instance sealed_int_persistent w : Persistent (sealed_int w).
  Proof. apply _. Qed.

  (* Integer-specific redefinitions *)
  Definition seal_pred_int τ := seal_pred τ sealed_int.
  Definition valid_sealed_int w τ := valid_sealed w τ sealed_int.

End invariants_int.
