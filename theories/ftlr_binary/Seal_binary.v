From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine Require Export rules_Seal.
From cap_machine.ftlr_binary Require Import interp_weakening.
From cap_machine.rules_binary Require Import rules_binary_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma seal_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (src1 src2 : RegName) (P : D):
    ftlr_instr r p b e a w w' (Seal dst src1 src2) P.
  Proof.
    intros Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { eapply lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr; eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    (* we assert that w = w' *)
    iAssert (⌜w = w'⌝)%I as %Heqw.
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    destruct HSpec; cycle 1.
    - (* In case of failure, we do not necessarily get a contradiction, but the proof is trivial *)
      iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w'; iFrame|iModIntro].
      iNext;iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - destruct (decide (src1 = PC)) as [->|Hnesp]; simplify_map_eq.
      specialize (Hsome src1) as (_ & (vr2 & Hsr1')).
      iAssert (interp(_,vr2)) as "HFalse".
      { iApply ("Hreg" $! src1); eauto. }
      rewrite !fixpoint_interp1_eq /=. done.
Qed.

End fundamental.
