From iris.algebra Require Import auth excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Export tactics.

Parameter event : Type.
Definition trace : Type := list event.
Definition traceO : ofeT := leibnizO trace.

Class traceG Σ := { foo_inG :> inG Σ (authR (optionUR (exclR traceO))) }.
Definition traceΣ : gFunctors := #[GFunctor (authR (optionUR (exclR traceO)))].

Section S.
Context `{!traceG Σ}.

Context (γ : gname).

Definition tracefull (t: trace) : iProp Σ := own γ (● (Some (Excl (t: traceO)))).
Definition tracefrag (t: trace) : iProp Σ := own γ (◯ (Some (Excl (t: traceO)))).

Lemma trace_full_frag_eq t t':
  tracefull t -∗ tracefrag t' -∗
  ⌜ t = t' ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid.
  pose proof (Excl_included _ _ Hi). apply leibniz_equiv in H. subst; auto.
Qed.

Lemma tracefrag_excl t t' :
  tracefrag t -∗ tracefrag t' -∗ ⌜ False ⌝.
Proof.
  iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
  rewrite -auth_frag_op // in Hv.
Qed.

Lemma trace_update t t' :
  tracefull t ∗ tracefrag t ==∗
  tracefull t' ∗ tracefrag t'.
Proof.
  rewrite /tracefull /tracefrag. rewrite -!own_op.
  apply own_update, auth_update.
  apply option_local_update.
  apply exclusive_local_update. constructor.
Qed.

End S.
