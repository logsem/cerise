From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
(* From cap_machine Require Import logrel fundamental. *)
From cap_machine Require Import proofmode.
Open Scope Z_scope.

Section reclaim_buffer_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {seals:sealStoreG Σ}
          `{MP: MachineParameters}.

  Definition reclaim_buffer_code : list LWord :=
    (* code: *)
    encodeInstrsLW [
      Mov r_t2 PC;
      Lea r_t2 5; (* label if-false *)
      IsUnique r_t0 r_t1; (* r_t0 = 1 <-> r_t1 is unique, *)
      Jnz r_t2 r_t0; (* jump if r_t0 is unique *)
      (* if-false: *)
      Fail; (* abort, in the case r_t0 is not unique *)
      (* if-true: *)
      Store r_t1 42; (* store value, in the case r_t0 is unique *)
      Mov r_t1 0;
      Mov r_t2 0;
      Jmp r_t31
    ].


  Lemma reclaim_buffer_code_spec
    (a_first: Addr)
    (w0 w2 wadv lw : LWord)
    (b e a : Addr) (v pc_v : Version)
    φ :
    let len_code := length reclaim_buffer_code in
    ContiguousRegion a_first len_code →
    (b + 1)%a = Some (b ^+1)%a ->
    (* TODO assumes that
       [a_first;a_first+len_code)
       and [b;b+1)
       do not overlap ! *)

    ⊢ (( PC ↦ᵣ LCap RWX a_first (a_first ^+ len_code)%a a_first pc_v
           ∗ r_t0 ↦ᵣ w0
           ∗ r_t1 ↦ᵣ LCap RW b (b^+1)%a b v
           ∗ r_t2 ↦ᵣ w2
           ∗ r_t31 ↦ᵣ wadv
           ∗ codefrag a_first pc_v reclaim_buffer_code
           ∗ (b,v) ↦ₐ lw
           ∗ ▷ ( PC ↦ᵣ updatePcPermL wadv
                   ∗ r_t0 ↦ᵣ LInt 1
                   ∗ r_t1 ↦ᵣ LInt 0
                   ∗ r_t2 ↦ᵣ LInt 0
                   ∗ r_t31 ↦ᵣ wadv
                   ∗ codefrag a_first pc_v reclaim_buffer_code
                   ∗ (b,v) ↦ₐ lw
                   ∗ (b,(v+1)%nat) ↦ₐ LInt 42
                  -∗ WP Seq (Instr Executable) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros len_region.
    iIntros (Hcont Hb) "(HPC & Hr0 & Hr1 & Hr2 & Hr31 & Hprog & Hbuf & Hφ)".
    iGo "Hprog".

    iInstr_lookup "Hprog" as "Hi" "Hprog".
    wp_instr.
    iAssert ([[b,(b ^+ 1)%a]]↦ₐ{v}[[ [lw] ]])%I with "[Hbuf]" as "Hbuf".
    { iApply region_mapsto_cons; eauto; first solve_addr.
      iFrame.
      rewrite /region_mapsto finz_seq_between_empty //=; last solve_addr.
    }
    iApply (wp_isunique_success with "[HPC Hr1 Hr0 Hbuf Hi]"); try iFrame; try solve_pure.
    { admit. } (* cf hypothesis*)
    { cbn.
      rewrite finz_dist_S; last solve_addr.
      rewrite finz_dist_0; solve_addr.
    }
    iNext.
    iIntros "H".
    iDestruct "H" as "[ (HPC& Hr0& Hr1& Hi& Hbuf_old& Hbuf) | (HPC& Hr0& Hr1& Hi& Hbuf)]".
    all: wp_pure; iInstr_close "Hprog".
    2:{ iGo "Hprog"; wp_end; by iRight. }

    iDestruct (region_mapsto_single with "Hbuf") as "Hbuf"; eauto.
    iDestruct "Hbuf" as (lw') "[ Hbuf % ]" ; simplify_eq.
    iDestruct (region_mapsto_single with "Hbuf_old") as "Hbuf_old"; eauto.
    iDestruct "Hbuf_old" as (lw) "[ Hbuf_old % ]" ; simplify_eq.

    iGo "Hprog". solve_addr.
    iGo "Hprog".

    iApply (wp_wand with "[-]").
    iApply "Hφ". 2: eauto.
    iFrame.
  Admitted.
