From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import rules logrel addr_reg_sample region_macros. 

Section malloc.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
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

  Global Parameter malloc_subroutine : RegName -> nat -> list Word.
  
  Global Axiom malloc_spec : forall (W : WORLD) (size : nat) (continuation : Word) (r : RegName) φ, 
  ( (* the malloc subroutine and parameters *)
       [[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine r size]]
     ∗ r_t0 ↦ᵣ continuation
    (* we pass control of all general purpose registers *)
     ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r_t0]; wsr, r_i ↦ᵣ w_i)
    (* the PC points to the malloc subroutine *)
     ∗ PC ↦ᵣ inr (p_m,Global,b_m,e_m,a_m)
    (* continuation *)
     ∗ ▷ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine r size]]
        ∗ (∃ wsr, [∗ list] r_i;w_i ∈ list_difference all_registers [PC;r]; wsr, r_i ↦ᵣ w_i)
        ∗ PC ↦ᵣ continuation
        (* the newly allocated region *)
        ∗ ∃ (b e : Addr), ⌜(e - b = size)%Z⌝ ∧ r ↦ᵣ inr (RWX,Global,b,e,b)
        ∗ [[b,e]] ↦ₐ[RWX] [[region_addrs_zeroes b e]]
        (* the allocated region is guaranteed to be fresh in the provided world *)
        (* TODO: remove this is we can prove it *)
        ∗ ⌜Forall (λ a, (countable.encode a) ∉ dom (gset positive) (std_sta W)
                      ∧ (countable.encode a) ∉ dom (gset positive) (std_rel W)) (region_addrs b e)⌝
        -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.

End malloc.   
  
