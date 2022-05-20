From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

(* TODO documentation :
   static spinlock -> we need to already have the capability and the
   memory addresse of the lock state
 *)

From iris.algebra Require Import excl.
Class lockG Σ := lock_G :> inG Σ (exclR unitR).
Section lock_model.
  Context `{memG Σ, lockG Σ, invG Σ}.

  (* We use a ghost name with a token to model whether the lock is locked or not.
     The the token is just exclusive ownerwhip of unit value. *)
  Definition locked γ := own γ (Excl ()).

  (* The lock invariant *)
  Definition is_lock γ (a : Addr) P :=
    (a ↦ₐ WInt 0 ∗ P ∗ locked γ ∨ a ↦ₐ WInt 1)%I.

End lock_model.

Section StaticSpinlock.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{lockG Σ, MP: MachineParameters}.

  (* r0 contains the capability pointing to the lock address *)
  Definition acquire_spinlock_instrs r0 r1 r2 r3 :=
    encodeInstrsW [
     Mov r1 1  ; (* value when lock acquired *)
     Mov r2 PC ; (* Adresse loop to wait --> label loop*)
     Lea r2 2  ;
     (* loop: *)
     Mov r3 0  ; (* value to check lock state *)
     CAS r0 r3 r1;
     Jnz r2 r3
     (* if (r1 -> 0), then the lock was free, we can continue *)
     (* if (r1 -> 1), then the lock was locked, we can wait and loop *)
      ].

  (* r0 contains the capability pointing to the lock address *)
  Definition release_spinlock_instrs r0 :=
    encodeInstrsW [
        Store r0 0
      ].


  Lemma spinlock_spec (i : CoreN)
    p_pc b_pc e_pc a_spinlock
    r0 r1 r2 r3
    w1 w2 w3
    p_lock (b_lock e_lock a_lock : Addr) P
    N E (γ : gname) φ :

    let e_spinlock := (a_spinlock ^+ length (acquire_spinlock_instrs r0 r1 r2 r3))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_spinlock e_spinlock ->

    writeAllowed p_lock = true ->
    withinBounds b_lock e_lock a_lock = true ->

    ↑N ⊆ E ->
    ⊢ ( inv N (codefrag a_spinlock (acquire_spinlock_instrs r0 r1 r2 r3) ∗ is_lock γ a_lock P)
        ∗ (i, PC) ↦ᵣ WCap p_pc b_pc e_pc a_spinlock
        ∗ (i, r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
        ∗ (i,r1) ↦ᵣ w1
        ∗ (i,r2) ↦ᵣ w2
        ∗ (i,r3) ↦ᵣ w3
        ∗ ▷ ( (i,PC) ↦ᵣ WCap p_pc b_pc e_pc e_spinlock
              ∗ (i,r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
              ∗ (i,r1) ↦ᵣ WInt 1
              ∗ (∃ w2, (i,r2) ↦ᵣ w2)
              ∗ (i, r3) ↦ᵣ WInt 0
              ∗ P ∗ locked γ
              -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }}
            )
        -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }})%I.
  Proof.
    intro e_spinlock.
    iIntros (HPC_exec HPC_bounds Hwrite_lock Hwrite_bounds HN)
      "(#Hinv & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hφ)".
    iDestruct (inv_split_l with "Hinv") as "Hinv_prog".
    do 3 (iInstr_inv "Hinv_prog").
    iLöb as "IH" forall (w3).
    iInstr_inv "Hinv_prog".

    wp_instr
    ; iInv "Hinv" as "[>Hprog Hlock]" "Hcls"
    ; codefrag_facts "Hprog".
    rewrite {2}/is_lock.
    iDestruct "Hlock" as "[(>Hlock & Hp & >Hlocked) | >Hlock]".
    - (* The lock is free, we acquire it *)
      iInstr "Hprog"
      ; iMod ("Hcls" with "[Hprog Hlock]") as "_"
      ; [ iNext ; iFrame ; iRight ; iFrame|]
      ; iModIntro ; wp_pure.
      do 1 (iInstr_inv "Hinv_prog").
      iApply "Hφ". iFrame.
      iExists _ ; iFrame.
    - (* The lock is already locked by another core *)
      iInstr "Hprog"
      ; iMod ("Hcls" with "[Hprog Hlock]") as "_"
      ; [ iNext ; iFrame ; iRight ; iFrame|]
      ; iModIntro ; wp_pure.
      do 1 (iInstr_inv "Hinv_prog").
      iAssert ( (i, PC) ↦ᵣ WCap p_pc b_pc e_pc (a_spinlock ^+ 3)%a )%I with "[HPC]"
        as "HPC".
      { inversion HPC_exec ; auto ; subst ; iFrame. }
      iApply ("IH" with "[$Hr0] [$Hr3]
                         [$Hφ] [$Hr1] [$HPC] [$Hr2]").
  Qed.

  Lemma release_spec (i : CoreN)
    p_pc b_pc e_pc pc_a
    r0
    p_lock (b_lock e_lock a_lock : Addr) P
    N E (γ : gname) φ :

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc pc_a (pc_a ^+1)%a  ->

    writeAllowed p_lock = true ->
    withinBounds b_lock e_lock a_lock = true ->

    ↑N ⊆ E ->
    ⊢ ( inv N (codefrag pc_a (release_spinlock_instrs r0)
               ∗ is_lock γ a_lock P)
        ∗ (i, PC) ↦ᵣ WCap p_pc b_pc e_pc pc_a
        ∗ (i, r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
        ∗ P ∗ locked γ
        ∗ ▷ ( (i,PC) ↦ᵣ WCap p_pc b_pc e_pc (pc_a ^+1)%a
              ∗ (i,r0) ↦ᵣ (WCap p_lock b_lock e_lock a_lock)
              -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }}
            )
        -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }})%I.
  Proof.
    iIntros (HPC_exec HPC_bounds Hwrite_lock Hwrite_bounds HN)
      "(#Hinv & HPC & Hr0 & Hp & Hlocked & Hφ)".
    iDestruct (inv_split_l with "Hinv") as "Hinv_prog".

    wp_instr
    ; iInv "Hinv" as "[>Hprog Hlock]" "Hcls"
    ; codefrag_facts "Hprog".
    rewrite {2}/is_lock.
    iDestruct "Hlock" as "[(>Hlock & Hp' & >Hlocked') | >Hlock]".
    - (* The lock is free -- impossible *)
      iDestruct (own_valid_2 with "Hlocked Hlocked'") as %Hv.  (* Hv = ⊥ *)
      done.
    - (* We release the lock, and give back the locked + resources to the invariant *)
      iInstr "Hprog"
      ; iMod ("Hcls" with "[Hprog Hlock Hp Hlocked]") as "_"
      ; [ iNext ; iFrame ; iLeft ; iFrame|]
      ; iModIntro ; wp_pure.
      iApply "Hφ" ; iFrame.
  Qed.

  Definition acquire_spinlock_length : Z :=
    Eval cbv in (length (acquire_spinlock_instrs PC PC PC PC)).

End StaticSpinlock.
