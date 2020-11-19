From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
 Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  

  Definition ftlr_instr (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (i: instr) (P : D) := 
      p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, b, e, a))
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrW w = i
    -> □ ▷ (∀ a0 a1 a2 a3 a4,
             full_map a0
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a1, a2, a3, a4)]> a0)
          -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (inr (a1, a2, a3, a4)) -∗ interp_conf)
    -∗ (fixpoint interp1) (inr (p, b, e, a)) 
    -∗ inv (logN.@a) (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) (r !r! r1))
    -∗ ▷ □ (∀ w : Word, P w -∗ (fixpoint interp1) w)
            ∗ (if decide (writeAllowed_in_r_a (<[PC:=inr (p, b, e, a)]> r) a) then ▷ □ (∀ w : Word, (fixpoint interp1) w -∗ P w) else emp)
    -∗ na_own logrel_nais ⊤
    -∗ a ↦ₐ w
    -∗ ▷ P w
    -∗ (▷ (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
    -∗ PC ↦ᵣ inr (p, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=> WP Seq (of_val v)
                                                    {{ v0, ⌜v0 = HaltedV⌝
                                                           → ∃ r1 : Reg, full_map r1 ∧ registers_mapsto r1
                                                                                                        ∗ na_own logrel_nais ⊤ }} }}.


End fundamental.
