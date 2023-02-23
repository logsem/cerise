From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules_base addr_reg_sample map_simpl.

Section test.
  Context `{memG Σ, regG Σ}.

  Lemma foo rmap:
    ([∗ map] k↦y ∈ <[r_t3:=WInt 0%Z]>
     (<[r_t2:=WInt 0%Z]>
      (<[r_t4:=WInt 0%Z]>
       (<[r_t5:=WInt 0%Z]> (delete r_t5 (<[r_t2:=WInt 0%Z]> (delete r_t3 (delete r_t1 rmap))))))),
     k ↦ᵣ y) -∗ ⌜True⌝.
  Proof.
    iIntros "H".
    map_simpl "H".
  Abort.

  Lemma foo (w1 w2 w3: Word) :
    ([∗ map] k↦y ∈ delete r_t2 (<[r_t1:=w1]> (<[r_t2:=w2]> (<[r_t1:=w3]> ∅))), k ↦ᵣ y) -∗
    r_t1 ↦ᵣ w1 ∗ r_t2 ↦ᵣ w2.
  Proof.
    iIntros "H".
    map_simpl "H".
  Abort.

  Lemma expressions_allowed pc_p pc_b pc_e a_first:
    ([∗ map] k↦y ∈  (<[r_t8:= WCap pc_p pc_b pc_e (a_first ^+ 0)%a]>
                       (<[r_t8 := WInt 0]> ∅)),
            k ↦ᵣ y) -∗ ⌜ True ⌝.
  Proof. iIntros "Ht".
         map_simpl "Ht".
  Abort.
End test.
