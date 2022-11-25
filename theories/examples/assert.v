From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

(* Assert routine *)

(* Maintains a flag storing whether an assert has failed. *)

Section Assert.
  Context {Σ:gFunctors} {CP:CoreParameters} {memg:memG Σ} {regg:@regG Σ CP}
          `{MP: MachineParameters}.

  (* assert (r4 == r5) *)
  Definition assert_subroutine_instrs :=
    encodeInstrsW [
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

  Definition assert_inv (b a_flag e : Addr) : iProp Σ :=
    ( codefrag b assert_subroutine_instrs ∗
      (∃ cap_addr,
       ⌜(b + length assert_subroutine_instrs)%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some a_flag⌝ ∗
       ⌜(a_flag + 1)%a = Some e⌝ ∗
       cap_addr ↦ₐ WCap RW a_flag e a_flag)).


  Ltac fact :=
    match goal with
    | h : @ContiguousRegion _ ?a (Z.of_nat (@Datatypes.length _ ?code))
      |- context [(@environments.Esnoc _ _ (INamed "Hprog") (@codefrag _ _ ?a ?code))]
      => match goal with
        | h: SubBounds ?b ?e ?a
               (?a ^+ (Z.of_nat (@Datatypes.length _ ?code)))%a
          |- context [(@environments.Esnoc _ _ _ ((_, PC) ↦ᵣ WCap _ ?b ?e _))]
          => idtac
        | _ => codefrag_facts "Hprog"
        end
    | _ => codefrag_facts "Hprog"
    end.

  Lemma assert_subroutine_spec i b a_flag e cont n1 n2 flag N E φ :
    ↑N ⊆ E →
    (  inv N (assert_inv b a_flag e)
     ∗ (i,PC) ↦ᵣ WCap RX b e b
     ∗ (i,r_t0) ↦ᵣ cont
     ∗ (i,r_t4) ↦ᵣ WInt n1
     ∗ (i,r_t5) ↦ᵣ WInt n2
     ∗ a_flag ↦ₐ WInt flag
     ∗ ▷ ((i,PC) ↦ᵣ updatePcPerm cont
          ∗ (i,r_t0) ↦ᵣ cont
          ∗ (i,r_t4) ↦ᵣ WInt 0
          ∗ (i, r_t5) ↦ᵣ WInt 0
          ∗ a_flag ↦ₐ WInt (if (n1 =? n2)%Z then flag else 1%Z)
          -∗ WP (i, Seq (Instr Executable)) @ E {{ φ }})
     ⊢ WP (i, Seq (Instr Executable)) @ E{{ φ }})%I.
  Proof.
    iIntros (HNE) "(#Hinv & HPC & Hr0 & Hr1 & Hr2 & Hflag & Hφ)".
    iDestruct (inv_split_l with "Hinv") as "Hinv_code".

    wp_instr.
    iInv "Hinv" as ">[Hprog Hassert]" "Hcls".
    iDestruct "Hassert" as (cap_addr) "(%Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs.
    fact.
    assert (SubBounds b e b (b ^+ length assert_subroutine_instrs)%a) by
      solve_addr.
    iInstr "Hprog".
    (iMod ("Hcls" with "[$Hprog Hcap]") as "_" ;[| iModIntro ; wp_pure]).
    { iNext ; iExists _ ; eauto. }
    do 2 iInstr_inv "Hinv_code".

    destruct (decide (n1 = n2)).
    { (* n1 = n2 *)
      subst n2. rewrite (_: n1 - n1 = 0)%Z; last lia.
      repeat (iInstr_inv "Hinv_code").
      iApply "Hφ". iFrame. rewrite Z.eqb_refl //. }
    { (* n1 ≠ n2 *)
      iInstr_inv "Hinv_code". { assert (n1 - n2 ≠ 0)%Z by lia. congruence. }
      iInstr_inv "Hinv_code". rewrite (_: (b ^+ 13)%a = cap_addr).
      2: solve_addr.

      (* Load *)
      wp_instr.
      iInv "Hinv" as ">[Hprog Hassert]" "Hcls".
      iDestruct "Hassert" as (cap_addr') "(%Hcap' & %Hflag' & _ & Hcap)".
      rewrite <- Hflag' in Hflag ; rewrite Hcap' in Hcap. simplify_eq.
      rewrite /assert_subroutine_instrs.
      iInstr "Hprog".
      solve_addr.
      (iMod ("Hcls" with "[$Hprog Hcap]") as "_" ;[| iModIntro ; wp_pure]).
      { iNext ; iExists _ ; eauto. }

      (* Store *)
      wp_instr.
      iInv "Hinv" as ">[Hprog Hassert]" "Hcls".
      iDestruct "Hassert" as (cap_addr') "(%Hcap'' & %Hflag'' & _ & Hcap)".
      rewrite <- Hflag'' in Hflag' ; rewrite Hcap'' in Hcap'. simplify_eq.
      rewrite /assert_subroutine_instrs.
      iInstr "Hprog".
      solve_addr.
      (iMod ("Hcls" with "[$Hprog Hcap]") as "_" ;[| iModIntro ; wp_pure]).
      { iNext ; iExists _ ; eauto. }

      repeat (iInstr_inv "Hinv_code").
      iApply "Hφ". iFrame. rewrite (_: (n1 =? n2)%Z = false) //.
      by apply Z.eqb_neq. }
  Qed.

  Lemma assert_success_spec i b a_flag e cont n1 n2 N E φ :
    ↑N ⊆ E →
    n1 = n2 →
    (  inv N (assert_inv b a_flag e)
     ∗ (i, PC) ↦ᵣ WCap RX b e b
     ∗ (i, r_t0) ↦ᵣ cont
     ∗ (i, r_t4) ↦ᵣ WInt n1
     ∗ (i, r_t5) ↦ᵣ WInt n2
     ∗ ▷ ((i, PC) ↦ᵣ updatePcPerm cont
          ∗ (i, r_t0) ↦ᵣ cont
          ∗ (i, r_t4) ↦ᵣ WInt 0
          ∗ (i, r_t5) ↦ᵣ WInt 0
          -∗ WP (i, Seq (Instr Executable)) @ E{{ φ }})
     ⊢ WP (i, Seq (Instr Executable)) @ E{{ φ }})%I.
  Proof.
    iIntros (HNE Heq) "(#Hinv & HPC & Hr0 & Hr1 & Hr2 & Hφ)".
    iDestruct (inv_split_l with "Hinv") as "Hinv_code".

    wp_instr.
    iInv "Hinv" as ">[Hprog Hassert]" "Hcls".
    iDestruct "Hassert" as (cap_addr) "(%Hcap & %Hflag & %He & Hcap)".
    rewrite /assert_subroutine_instrs.
    fact.
    assert (SubBounds b e b (b ^+ length assert_subroutine_instrs)%a) by
      solve_addr.
    iInstr "Hprog".
    (iMod ("Hcls" with "[$Hprog Hcap]") as "_" ;[| iModIntro ; wp_pure]).
    { iNext ; iExists _ ; eauto. }
    do 2 iInstr_inv "Hinv_code".
    rewrite (_: n1 - n2 = 0)%Z; last lia.
    repeat iInstr_inv "Hinv_code".
    iApply "Hφ". iFrame.
  Qed.

End Assert.
