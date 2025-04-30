From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

(* Assert routine *)

(* Maintains a flag storing whether an assert has failed. *)

Section Assert.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.

  (* assert (r4 == r5) *)
  Definition assert_subroutine_instrs :=
    encodeInstrsLW [
      Sub r_t4 r_t4 r_t5;
      Mov r_t5 PC;
      Lea r_t5 6;
      Jnz r_t5 r_t4;
      (* success case *)
      Mov r_t4 0;
      Mov r_t5 0;
      Jmp r_t0; (* return *)
      (* failure case *)
      Lea r_t5 6; (* pointer to cap: *)
      Load r_t5 r_t5;
      Store r_t5 1;
      Mov r_t4 0;
      Mov r_t5 0;
      Jmp r_t0 (* return *)
    ].
  (* followed in memory by:
    cap: (RW, flag, end, flag)
    flag: <0 or 1>
    end:
  *)

  Definition assert_inv (b a_flag e : Addr) (v : Version) : iProp Σ :=
    (∃ cap_addr,
       codefrag b v assert_subroutine_instrs ∗
       ⌜(b + length assert_subroutine_instrs)%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some a_flag⌝ ∗
       ⌜(a_flag + 1)%a = Some e⌝ ∗
       (cap_addr, v) ↦ₐ LCap RW a_flag e a_flag v).

  Lemma assert_subroutine_spec b a_flag e v cont n1 n2 flag N E φ :
    ↑N ⊆ E →
    (  na_inv logrel_nais N (assert_inv b a_flag e v)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ LCap RX b e b v
     ∗ r_t0 ↦ᵣ cont
     ∗ r_t4 ↦ᵣ LInt n1
     ∗ r_t5 ↦ᵣ LInt n2
     ∗ (a_flag, v) ↦ₐ LInt flag
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPermL cont
          ∗ r_t0 ↦ᵣ cont
          ∗ r_t4 ↦ᵣ LInt 0
          ∗ r_t5 ↦ᵣ LInt 0
          ∗ (a_flag, v) ↦ₐ LInt (if (n1 =? n2)%Z then flag else 1%Z)
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE) "(#Hinv & Hna & HPC & Hr0 & Hr1 & Hr2 & Hflag & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds b e b (b ^+ length assert_subroutine_instrs)%a) by solve_addr.
    do 3 iInstr "Hprog".
    destruct (decide (n1 = n2)).
    { (* n1 = n2 *)
      subst n2. rewrite (_: n1 - n1 = 0)%Z; last lia.
      iGo "Hprog".
      iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
      { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
      iApply "Hφ". iFrame. rewrite Z.eqb_refl //. }
    { (* n1 ≠ n2 *)
      iInstr "Hprog". { assert (n1 - n2 ≠ 0)%Z by lia. congruence. }
      iInstr "Hprog". rewrite (_: (b ^+ 13)%a = cap_addr). 2: solve_addr.
      iInstr "Hprog". solve_addr.
      iInstr "Hprog". solve_addr.
      iGo "Hprog".
      iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
      { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
      iApply "Hφ". iFrame. rewrite (_: (n1 =? n2)%Z = false) //.
      by apply Z.eqb_neq. }
  Qed.

  Lemma assert_success_spec b a_flag e v cont n1 n2 N E φ :
    ↑N ⊆ E →
    n1 = n2 →
    (  na_inv logrel_nais N (assert_inv b a_flag e v)
     ∗ na_own logrel_nais E
     ∗ PC ↦ᵣ LCap RX b e b v
     ∗ r_t0 ↦ᵣ cont
     ∗ r_t4 ↦ᵣ LInt n1
     ∗ r_t5 ↦ᵣ LInt n2
     ∗ ▷ (na_own logrel_nais E
          ∗ PC ↦ᵣ updatePcPermL cont
          ∗ r_t0 ↦ᵣ cont
          ∗ r_t4 ↦ᵣ LInt 0
          ∗ r_t5 ↦ᵣ LInt 0
          -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (HNE Heq) "(#Hinv & Hna & HPC & Hr0 & Hr1 & Hr2 & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hassert & Hna & Hinv_close)"; auto.
    iDestruct "Hassert" as (cap_addr) "(Hprog & %Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs. codefrag_facts "Hprog".
    assert (SubBounds b e b (b ^+ length assert_subroutine_instrs)%a) by solve_addr.
    do 3 iInstr "Hprog". rewrite (_: n1 - n2 = 0)%Z; last lia.
    iGo "Hprog".
    iMod ("Hinv_close" with "[Hprog Hcap $Hna]") as "Hna".
    { iExists _. iNext. iFrame. iPureIntro. repeat split; solve_addr. }
    iApply "Hφ". iFrame.
  Qed.

End Assert.
