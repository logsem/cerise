From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).


  (* NOTE: I think having PC:= wsrc in the IH in below definition, rather than restricting induction to capabilities only, would allow us to more generally apply the induction hypothesis in multiple cases. Now we do the `wp_notCorrectPC`-related reasoning in multiple places, not just in the top-level ftlr. *)

  Definition ftlr_instr (lregs : leibnizO LReg) (p : Perm)
        (b e a : Addr) (v : Version) (lw : LWord) (i: instr) (P : D) :=
      p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (lregs !! x))
    → isCorrectLPC (LCap p b e a v)
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrWL lw = i
    -> □ ▷ (∀ lregs' p' b' e' a' v',
             full_map lregs'
          -∗ (∀ (r1 : RegName) (lv : LWord),
              ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
          -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
          -∗ na_own logrel_nais ⊤
             -∗ □ (fixpoint interp1) (LCap p' b' e' a' v') -∗ interp_conf)
    -∗ (fixpoint interp1) (LCap p b e a v)
    -∗ inv (logN.@(a,v)) (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0)
    -∗ (∀ (r1 : RegName) (lv : LWord),
        ⌜r1 ≠ PC⌝ → ⌜lregs !! r1 = Some lv⌝ → (fixpoint interp1) lv)
    -∗ ▷ □ (∀ lw : LWord, P lw -∗ (fixpoint interp1) lw)
            ∗ (if decide (writeAllowed_in_r_av (<[PC:=LCap p b e a v]> lregs) a v)
               then ▷ □ (∀ lw : LWord, (fixpoint interp1) lw -∗ P lw)
               else emp)
            ∗ (persistent_cond P)
    -∗ na_own logrel_nais ⊤
    -∗ (a,v) ↦ₐ lw
    -∗ ▷ P lw
    -∗ (▷ (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0) ={⊤ ∖ ↑logN.@(a,v),⊤}=∗ emp)
    -∗ PC ↦ᵣ LCap p b e a v
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=LCap p b e a v]> lregs), k ↦ᵣ y)
    -∗ WP Instr Executable
        @ ⊤ ∖ ↑logN.@(a,v)
        {{ v0, |={⊤ ∖ ↑logN.@(a,v),⊤}=>
             WP Seq (of_val v0)
               {{ v1, ⌜v1 = HaltedV⌝ →
                      ∃ lregs0 : LReg,
                        full_map lregs0 ∧ registers_mapsto lregs0 ∗ na_own logrel_nais ⊤
               }}
        }}.


End fundamental.
