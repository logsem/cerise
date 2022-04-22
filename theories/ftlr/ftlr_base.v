From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
 Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  

  Definition ftlr_instr (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (w : Word) (it: instr) (i : CoreN) (P : D) :=
      p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (r !! (i, x)))
    → isCorrectPC (WCap p b e a)
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrW w = it
    -> □ ▷ (∀ i a0 a1 a2 a3 a4,
             full_map a0 i
          -∗ (∀ (j : CoreN) (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜a0 !! (j, r1) = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[(i, PC):=WCap a1 a2 a3 a4]> a0)
             -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ (interp_conf i))
    -∗ (fixpoint interp1) (WCap p b e a)
    -∗ inv (logN.@a) (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0)
    -∗ (∀ (j : CoreN) (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r !! (j, r1) = Some v⌝ → (fixpoint interp1) v)
    -∗ ▷ □ (∀ w : Word, P w -∗ (fixpoint interp1) w)
            ∗ (if decide (writeAllowed_in_r_a (<[(i, PC):=WCap p b e a]> r) i a) then ▷ □ (∀ w : Word, (fixpoint interp1) w -∗ P w) else emp)
    -∗ a ↦ₐ w
    -∗ ▷ P w
    -∗ (▷ (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
    -∗ (i, PC) ↦ᵣ WCap p b e a
    -∗ ([∗ map] k↦y ∈ delete (i, PC) (<[(i, PC):=WCap p b e a]> r), k ↦ᵣ y)
    -∗
        WP (i, Instr Executable)
        @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=> WP fill_item SeqCtx (of_val v)
                                                    {{ v0, ⌜v0 = (i, HaltedV)⌝
                                                           → ∃ r1 : Reg
                                                          , full_map r1 i ∧ registers_mapsto r1}} }}.
End fundamental.
