From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import register_tactics.
From cap_machine Require Import fundamental logrel rules.
From cap_machine.proofmode Require Import tactics_helpers proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine.exercises Require Import subseg_buffer.
Open Scope Z_scope.

(** Firtly, we create a closure around our code and buffer. The capability
    pointing to the allocated buffer is stored in memory. We thus have to load
    it in the register. This part of code sets up the context, allowing to use
    the previous specification.
 *)
Section closure_program.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.

  Program Definition inv_ie_pc b_pc e_pc a_pc
    : leibnizO Word -n> iPropO Σ :=
    λne w, ⌜w = (WCap RX b_pc e_pc a_pc)⌝%I.

  Program Definition inv_ie_idc b_mem e_mem
    : leibnizO Word -n> iPropO Σ :=
    λne w, ⌜w = (WCap RW b_mem e_mem b_mem)⌝%I.

  Lemma prog_CPS_safe_to_share_IE
    b_pc e_pc a_prog (b_mem e_mem: Addr) secret_off secret
    b_ie e_ie a_ie :

    (* The instructions of the code are in the memory closure of the PCC *)
    SubBounds b_pc e_pc a_prog (a_prog ^+ length (prog_code secret_off secret))% a →
    (* The secret offset fits in the memory buffer *)
    (b_mem ≤ b_mem ^+ secret_off < e_mem)%a →

    SubBounds b_ie e_ie a_ie (a_ie ^+ 1)%a →

    ⊢ ( code_inv a_prog secret_off secret
       ∗ start_mem_inv b_mem e_mem secret_off
       ∗ end_mem_inv b_mem e_mem secret_off
       ∗ secret_inv b_mem secret_off secret
       ∗ inv (logN.@a_ie) (∃ w1 : leibnizO Word , a_ie ↦ₐ w1 ∗ inv_ie_pc b_pc e_pc a_prog w1)
       ∗ inv (logN.@(a_ie ^+ 1)%a) (∃ w2 : leibnizO Word, (a_ie ^+ 1)%a ↦ₐ w2 ∗ inv_ie_idc b_mem e_mem w2)
      )

   -∗ interp (WCap IE b_ie e_ie a_ie).
  Proof.
    iIntros (Hbounds_pc Hbounds_mem Hbounds_ie)
      "#(Hcode & Hmem & Hend_mem & Hsecret & Hinv_ie_pc & Hinv_ie_idc)".
    rewrite fixpoint_interp1_eq /=.
    iIntros "[%Hwb %Hwb']".
    iExists (inv_ie_pc b_pc e_pc a_prog), (inv_ie_idc b_mem e_mem).
    iSplit.
    rewrite /persistent_cond /inv_ie_pc //=.
    iPureIntro; intros; apply bi.pure_persistent.
    iSplit.
    rewrite /persistent_cond /inv_ie_pc //=.
    iPureIntro; intros; apply bi.pure_persistent.
    iFrame "#".
    iIntros (w1 w2 regs). iNext ; iModIntro.
    iIntros "[Hw1 Hw2] ([Hfull Hregs] & Hrmap & Hown)".
    rewrite /=.

    (* TODO And the problem arise at this point, if I have the disjunction:
       (P1 w1 \/ interp w1) * (P2 w2 \/ interp w2) -* E(w1, w2)
       I need the cases [w1 = ...] and [w2 = ... ],
       otherwise, the spec says nothing.
     *)

    iApply (prog_spec_CPS_full with "[-]") ; eauto.
End closure_program.
