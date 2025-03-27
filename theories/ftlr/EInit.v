From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma einit_case (lregs : leibnizO LReg)
    (p : Perm) (b e a : Addr) (v : Version)
    (lw : LWord) (r : RegName) (P : D):
    ftlr_instr lregs p b e a v lw (EInit r) P.
  Proof.
  (*   intros Hp Hsome i Hbae Hi. *)
  (*   iIntros "#IH #Hinv #Hinva #Hreg #Hread Hown Ha HP Hcls HPC Hmap". *)
  (*   rewrite delete_insert_delete. *)
  (*   destruct (reg_eq_dec PC r); simplify_map_eq. *)
  (*   * iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame. *)
  (*     iNext. iIntros "[HPC Ha] /=". *)
  (*     (* reconstruct invariant *) *)
  (*     iMod ("Hcls" with "[Ha HP]") as "_";[iExists lw;iFrame|]. *)
  (*     iModIntro. *)
  (*     iApply wp_pure_step_later; auto. *)
  (*     (* reconstruct registers *) *)
  (*     iNext. *)
  (*     iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /="; *)
  (*       [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. *)
  (*     (* apply IH *) *)
  (*     iIntros "_". *)
  (*     iApply ("IH" $! _ _ b e a with "[] [] [Hmap] [$Hown]"); eauto. *)
  (*     { iPureIntro. apply Hsome. } *)
  (*     destruct Hp as [-> | ->]; iFrame. *)
  (*   * specialize Hsome with r as Hr. *)
  (*     destruct Hr as [wsrc Hsomesrc]. *)
  (*     iDestruct ((big_sepM_delete _ _ r) with "Hmap") as "[Hsrc Hmap]"; eauto. *)
  (*     rewrite (lookup_delete_ne lregs PC r); eauto. *)
  (*     iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto. *)
  (*     iNext. iIntros "[HPC [Ha Hsrc]] /=". *)
  (*     iApply wp_pure_step_later; auto. *)
  (*     (* reconstruct regions *) *)
  (*     iDestruct ((big_sepM_delete _ _ r) with "[Hsrc Hmap]") as "Hmap /="; *)
  (*       [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. *)
  (*     rewrite -delete_insert_ne // insert_id; auto. *)

  (*     iMod ("Hcls" with "[HP Ha]");[iExists lw;iFrame|iModIntro]. *)

  (*    (* Needed because IH disallows non-capability values *) *)
  (*     destruct wsrc as [ | [p' b' e' a' v' | ] | ]; cycle 1. *)
  (*     { *)
  (*       rewrite /updatePcPerm. *)
  (*       (* Special case for E-values*) *)
  (*       destruct (decide (p' = E)) as [-> | HneE]. *)
  (*       - *)
  (*         unshelve iDestruct ("Hreg" $! r _ _ Hsomesrc) as "HPCv"; auto. *)
  (*         iClear "Hinv". *)
  (*         rewrite fixpoint_interp1_eq; simpl. *)

  (*         iDestruct (big_sepM_insert _ _ PC with "[$Hmap $HPC]") as "Hmap"; [apply lookup_delete|]. *)
  (*         rewrite insert_delete_insert; auto. *)
  (*         iDestruct ("HPCv" with "[$Hmap $Hown]") as "Hcont"; auto. *)
  (*       - iAssert (PC ↦ᵣ LCap p' b' e' a' v')%I  with "[HPC]" as "HPC". *)
  (*         { destruct p'; auto. congruence. } *)

  (*         iDestruct (big_sepM_insert _ _ PC with "[$Hmap $HPC]") as "Hmap"; [apply lookup_delete|]. *)
  (*         rewrite insert_delete_insert; auto. *)
  (*         iNext; iIntros "_". *)
  (*         iApply ("IH" $! (<[PC:=LCap p' b' e' a' v']> lregs) with "[%] [] [Hmap] [$Hown]"). *)
  (*         { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). } *)
  (*         { iIntros (ri ? Hri Hvs). *)
  (*           rewrite lookup_insert_ne in Hvs; auto. *)
  (*           destruct (decide (ri = r)); simplify_map_eq. *)
  (*           { rewrite Hsomesrc in Hvs; inversion Hvs; subst; clear Hvs. *)
  (*             unshelve iSpecialize ("Hreg" $! r _ _ Hsomesrc); eauto. } *)
  (*           { iApply "Hreg"; auto. } *)
  (*         } *)
  (*         { rewrite insert_insert. iApply "Hmap". } *)
  (*         iModIntro. *)
  (*         unshelve iSpecialize ("Hreg" $! r _ _ Hsomesrc); eauto. *)
  (*     } *)

  (*    (* Non-capability cases *) *)
  (*     all: iNext; iIntros "_". *)
  (*     all: rewrite /updatePcPerm; iApply (wp_bind (fill [SeqCtx])); *)
  (*       iApply (wp_notCorrectPC with "HPC"); [intros HFalse; inversion HFalse; cbn in *; simplify_eq| ]. *)
  (*     all: repeat iNext; iIntros "HPC /=". *)
  (*     all: iApply wp_pure_step_later; auto. *)
  (*     all: iNext; iIntros "_". *)
  (*     all: iApply wp_value. *)
  (*     all: iIntros; discriminate. *)
  (* Qed. *)
    Admitted.

End fundamental.
