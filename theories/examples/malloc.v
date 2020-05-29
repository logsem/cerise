From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import rules logrel addr_reg_sample.

Section malloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).
  
  (* We will assume there exists a malloc spec. A trusted Kernel would have to show that it satisfies the spec *)

  (* First we need parameters for the malloc subroutine *)
  Global Parameter p_m : Perm. 
  Global Parameter b_m : Addr.
  Global Parameter e_m : Addr.
  Global Parameter a_m : Addr.

  Global Parameter malloc_subroutine : list Word.
  Global Parameter malloc_γ : namespace. 

  Global Axiom malloc_subroutine_spec : forall (W : WORLD) (size : Z) (continuation : Word) rmap φ,
  (  (* the malloc subroutine and parameters *)
       inv malloc_γ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine]])
     ∗ r_t0 ↦ᵣ continuation
     (* the PC points to the malloc subroutine *)
     ∗ PC ↦ᵣ inr (RX,Global,b_m,e_m,a_m)
     ∗ r_t1 ↦ᵣ inl size
     (* we pass control of all general purpose registers *)
     ∗ ⌜dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]}⌝
     ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
     (* continuation *)
     ∗ ▷ ((([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
        ∗ r_t0 ↦ᵣ continuation
        ∗ PC ↦ᵣ continuation
        (* the newly allocated region *)
        ∗ ∃ (b e : Addr), ⌜(e - b = size)%Z⌝ ∧ r_t1 ↦ᵣ inr (RWX,Global,b,e,b)
        ∗ [[b,e]] ↦ₐ[RWX] [[region_addrs_zeroes b e]]
        (* the allocated region is guaranteed to be fresh in the provided world *)
        (* TODO: remove this is we can prove it *)
        ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝)
        -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.

End malloc.
