From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_AddSubLt.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma AddSubLt_spec_determ r i dst arg1 arg2 regs regs' retv retv' :
    is_AddSubLt i dst arg1 arg2 ->
    AddSubLt_spec i r dst arg1 arg2 regs retv ->
    AddSubLt_spec i r dst arg1 arg2 regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros isASL Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto.
    - inv H4; congruence.
    - inv H4; congruence.
    - inv H0; congruence.
  Qed.

  Lemma add_sub_lt_case i (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (arg1 arg2 : Z + RegName) (P : D):
    is_AddSubLt i dst arg1 arg2 ->
    ftlr_instr r p b e a w w' i P.
  Proof.
    intros HisASL Hp Hsome HisCorrect Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq. reflexivity. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr; eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    (* we assert that w = w' *)
    iAssert (⌜w = w'⌝)%I as %Heqw.
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    iMod (step_AddSubLt _ [SeqCtx] i with "[$Ha' $Hsmap $Hs $Hspec]") as (retv' regs'') "(Hs' & Hs & Ha' & Hsmap) /=";[rewrite Heqw in Hi|..];eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { solve_ndisj. }
    iDestruct "Hs'" as %HSpec'.

    subst w'. rewrite Hi in HSpec, HSpec'.
    specialize (AddSubLt_spec_determ _ i _ _ _ _ _ _ _ HisASL HSpec HSpec') as [Hregs <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w; iFrame|iModIntro]. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Hregs as [<-|Hcontr];[|inversion Hcontr].
      incrementPC_inv; simplify_map_eq.
      iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w,w; iFrame|iModIntro].
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.

      destruct (decide (PC = dst));simplify_eq;simplify_map_eq.
      rewrite (insert_commute _ _ PC)// insert_insert.
      iApply ("IH" $! ((<[dst:=_]> r1),(<[dst:=_]> r1)) with "[] [] Hmap Hsmap Hown Hs Hspec").
      { iPureIntro. simpl. intros reg. destruct Hsome with reg;auto.
        destruct (decide (dst = reg));[subst;rewrite lookup_insert|rewrite !lookup_insert_ne//];eauto. }
      { simpl. iIntros (rr v1 v2 Hne Hv1s Hv2s).
        destruct (decide (rr = dst));[subst;rewrite lookup_insert in Hv1s, Hv2s|].
        - rewrite /interp !fixpoint_interp1_eq /=; simplify_eq; auto.
        - rewrite !lookup_insert_ne// in Hv1s,Hv2s. simplify_eq.
          revert Heq; rewrite map_eq' =>Heq.
          destruct (r1 !! rr) eqn:Hsome';rewrite Hsome' in Hv1s;[|rewrite !fixpoint_interp1_eq;congruence]. inversion Hv1s. subst v1.
          specialize (Heq rr w0). rewrite !lookup_insert_ne// in Heq. apply Heq in Hsome' as Heq'.
          by iSpecialize ("Hreg" $! rr _ _ Hne Hsome' Heq').
      }
      {  simplify_eq.
        rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
    }
  Qed.

End fundamental.


