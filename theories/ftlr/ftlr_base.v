From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
 Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO Word) -n> iPropO Σ).
  Notation R := ((leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* NOTE: I think having PC:= wsrc in the IH in below definition, rather than restricting induction to capabilities only, would allow us to more generally apply the induction hypothesis in multiple cases. Now we do the `wp_notCorrectPC`-related reasoning in multiple places, not just in the top-level ftlr. *)

  Definition ftlr_instr (r : leibnizO Reg) (p : Perm)
        (b e a : Addr) (widc w : Word) (i: instr) (P : D) :=
      p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (WCap p b e a)
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrW w = i
    -> □ ▷ (∀ a0 a1 a2 a3 a4 w,
             full_map a0
          -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r1 ≠ idc⌝ → ⌜a0 !! r1 = Some v⌝ → (fixpoint interp1) v)
          -∗ registers_mapsto (<[idc:=w]>(<[PC:=WCap a1 a2 a3 a4]> a0))
          -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (WCap a1 a2 a3 a4) -∗ interp_conf)
    -∗ (fixpoint interp1) (WCap p b e a)
    -∗ (fixpoint interp1) widc
    -∗ inv (logN.@a) (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0)
    -∗ (∀ (r1 : RegName) v, ⌜r1 ≠ PC⌝ → ⌜r !! r1 = Some v⌝ → (fixpoint interp1) v)
    -∗ ▷ □ (∀ w : Word, P w -∗ (fixpoint interp1) w)
            ∗ (if decide (writeAllowed_in_r_a (<[PC:=WCap p b e a]> r) a) then ▷ □ (∀ w : Word, (fixpoint interp1) w -∗ P w) else emp)
    -∗ na_own logrel_nais ⊤
    -∗ a ↦ₐ w
    -∗ ▷ P w
    -∗ (▷ (∃ w0 : leibnizO Word, a ↦ₐ w0 ∗ P w0) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
    -∗ PC ↦ᵣ WCap p b e a
    -∗ idc ↦ᵣ widc
    -∗ ([∗ map] k↦y ∈ (delete idc (delete PC (<[idc:=widc]> (<[PC:=WCap p b e a]> r)))), k ↦ᵣ y)
    -∗
        WP Instr Executable
        @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=> WP Seq (of_val v)
                                                    {{ v0, ⌜v0 = HaltedV⌝
                                                           → ∃ r1 : Reg, full_map r1 ∧ registers_mapsto r1
                                                                                                        ∗ na_own logrel_nais ⊤ }} }}.


End fundamental.
