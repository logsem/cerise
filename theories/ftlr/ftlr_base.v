From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).


  (* NOTE: I think having PC:= wsrc in the IH in below definition, rather than restricting induction to capabilities only, would allow us to more generally apply the induction hypothesis in multiple cases. Now we do the `wp_notCorrectPC`-related reasoning in multiple places, not just in the top-level ftlr. *)

  Definition ftlr_instr
    (lregs : leibnizO LReg) (p : Perm)
        (b e a : Addr) (v : Version) (lw : LWord) (i: instr) (P : D) :=
      p = RX ∨ p = RWX
    → (∀ x : RegName, is_Some (lregs !! x))
    → isCorrectLPC (LCap p b e a v)
    → (b <= a)%a ∧ (a < e)%a
    → decodeInstrWL lw = i
    → (□ custom_enclave_contract_gen ∗ system_inv)
    (* Loeb induction hypothesis, but only for those assumptions that change in the recursive step *)
    -∗ □ ▷ (∀ lregs' p' b' e' a' v',
             full_map lregs'
          -∗ (∀ (r1 : RegName) (lv : LWord),
              ⌜r1 ≠ PC⌝ → ⌜lregs' !! r1 = Some lv⌝ → (fixpoint interp1) lv)
          -∗ registers_mapsto (<[PC:=LCap p' b' e' a' v']> lregs')
          -∗ na_own logrel_nais ⊤
             -∗ (□ (fixpoint interp1) (LCap p' b' e' a' v')) -∗ interp_conf)

    -∗ (fixpoint interp1) (LCap p b e a v)
       (* (1) *)
    -∗ inv (logN.@(a,v)) (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0) (* invariant for the address where PC points to, namely P should hold for it *)
    -∗ (∀ (r1 : RegName) (lv : LWord),
        ⌜r1 ≠ PC⌝ → ⌜lregs !! r1 = Some lv⌝ → (fixpoint interp1) lv) (* the vals of all regs in lregs have to be safe *)

    -∗ ▷ □ (∀ lw : LWord, P lw -∗ (fixpoint interp1) lw) (* read condition on P: has to be safe *)
            ∗ (if decide (writeAllowed_in_r_av (<[PC:=LCap p b e a v]> lregs) a v) (* other side condition: if you have write access, then the write condition has to hold as well *)
               then ▷ □ (∀ lw : LWord, (fixpoint interp1) lw -∗ P lw)
               else emp)
            ∗ (persistent_cond P) (* P v ⊢ P v ∗ P v *)

    -∗ na_own logrel_nais ⊤ (* same as the Loeb induction cond: knowledge about the existence of nonatomic invariants *)
    -∗ (a,v) ↦ₐ lw (* points-to for the address of the PC cap *) (* as a consequence of (1) *)
    -∗ ▷ P lw (* as a consequence of (1) *)
    -∗ (▷ (∃ lw0 : leibnizO LWord, (a,v) ↦ₐ lw0 ∗ P lw0) ={⊤ ∖ ↑logN.@(a,v),⊤}=∗ emp) (* the PC invariant can be closed *)
    -∗ PC ↦ᵣ LCap p b e a v
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=LCap p b e a v]> lregs), k ↦ᵣ y) (* points-tos for values of all other regs *)
    -∗ WP Instr Executable (* WP holds in current machine state *)
        @ ⊤ ∖ ↑logN.@(a,v) (* assuming the opened atomic (i.e. for the execution of one instruction) invariant from above *)
        {{ v0, |={⊤ ∖ ↑logN.@(a,v),⊤}=> (* one has to show that the invariant can be closed again *)
             WP Seq (of_val v0) (* moreover, after executing one instruction, the system needs to continue executing safely *)
               {{ v1, ⌜v1 = HaltedV⌝ →
                      ∃ lregs0 : LReg,
                        full_map lregs0 ∧ registers_mapsto lregs0 ∗ na_own logrel_nais ⊤
               }}
        }}.


End fundamental.
