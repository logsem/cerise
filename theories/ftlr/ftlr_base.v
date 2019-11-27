From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition ftlr_instr (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (i: instr) :=
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = i
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (fs, fr)) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ ▷ future_mono (λ Wv : prodO WORLD (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2)
    -∗ ▷ ((fixpoint interp1) (fs, fr)) w
    -∗ sts_full fs fr
    -∗ na_own logrel_nais ⊤
    -∗ open_region a (fs, fr)
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (fs' : STS_states) (fr' : STS_rels),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full fs' fr' ∗ region (fs', fr') }} }}.

End fundamental.