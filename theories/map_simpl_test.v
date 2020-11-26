From iris.proofmode Require Import tactics.
From cap_machine Require Import rules_base addr_reg_sample map_simpl.

Section test.
  Context `{memG Σ, regG Σ}.

  Lemma foo (w1 w2 w3: Word) :
    ([∗ map] k↦y ∈ (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    iIntros "H".
    map_simpl "H".
  Abort.

End test.
