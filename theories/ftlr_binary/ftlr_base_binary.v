From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel_binary.

Section fundamental.
 Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition ftlr_instr (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
             (b e a : Addr) (w w' : Word) (i : instr) (P : D) :=
    p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (r.1 !! x) ∧ is_Some (r.2 !! x))
    → isCorrectPC (WCap (p, b, e, a))
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrW w = i
    → □ ▷ (∀ a0 a1 a2 a3 a4,
              full_map a0
           -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → interp (a0.1 !r! r0, a0.2 !r! r0))
           -∗ registers_mapsto (<[PC:=WCap (a1, a2, a3, a4)]> a0.1)
           -∗ spec_registers_mapsto (<[PC:=WCap (a1, a2, a3, a4)]> a0.2)
           -∗ na_own logrel_nais ⊤
           -∗ ⤇ Seq (Instr Executable)
           -∗ □ spec_ctx
           -∗ □ interp (WCap (a1, a2, a3, a4), WCap (a1, a2, a3, a4)) -∗ interp_conf)
    -∗ spec_ctx
    -∗ interp (WCap (p, b, e, a), WCap (p, b, e, a))
    -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → interp (r.1 !r! r0, r.2 !r! r0))
    -∗ inv (logN.@a) (∃ w0 w'0 : Word, a ↦ₐ w0 ∗ a ↣ₐ w'0 ∗ P (w0, w'0))
    -∗ ▷ □ (∀ w0 w'0 : Word, P (w0, w'0) -∗ interp (w0, w'0))
            ∗ (if decide (writeAllowed_in_r_a (<[PC:=WCap (p, b, e, a)]> r.1) a) then ▷ □ (∀ w0 w'0 : Word, interp (w0, w'0) -∗ P (w0, w'0)) else emp)
    -∗ spec_registers_mapsto (<[PC:=WCap (p, b, e, a)]> r.2)
    -∗ na_own logrel_nais ⊤
    -∗ ⤇ Seq (Instr Executable)
    -∗ a ↦ₐ w
    -∗ a ↣ₐ w'
    -∗ ▷ P (w, w')
    -∗ (▷ (∃ w0 w'0 : Word, a ↦ₐ w0 ∗ a ↣ₐ w'0 ∗ P (w0, w'0)) ={⊤ ∖ ↑logN.@a,⊤}=∗ emp)
    -∗ PC ↦ᵣ WCap (p, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=WCap (p, b, e, a)]> r.1), k ↦ᵣ y)
    -∗ WP Instr Executable @ ⊤ ∖ ↑logN.@a {{ v, |={⊤ ∖ ↑logN.@a,⊤}=> WP Seq (of_val v)
                                                {{ v0, ⌜v0 = HaltedV⌝
                                                       → ∃ r0 : Reg * Reg, ⤇ Instr Halted
                                                                           ∗ full_map r0 ∧ registers_mapsto r0.1
                                                                           ∗ spec_registers_mapsto r0.2
                                                                           ∗ na_own logrel_nais ⊤ }} }}. 
  
    
End fundamental.
