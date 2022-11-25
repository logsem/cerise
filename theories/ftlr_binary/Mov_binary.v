From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base_binary.
From cap_machine.rules_binary Require Import rules_binary_base rules_binary_Mov.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfgsg: cfgSG Σ}
          `{MachineParameters}.

  Notation D := ((prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := ((prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types ww : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma Mov_spec_determ r dst src regs regs' retv retv' :
    Mov_spec r dst src regs retv ->
    Mov_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2;subst; simplify_eq.
    - split;auto.
    - split;auto.
  Qed.

  Lemma mov_case (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (b e a : Addr) (w w' : Word) (dst : RegName) (src : Z + RegName) (P : D):
    ftlr_instr r p b e a w w' (Mov dst src) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "#IH #Hspec #Hinv #Hreg #Hinva #Hread Hsmap Hown Hs Ha Ha' HP Hcls HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr;eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    (* we assert that w = w' *)
    iAssert (⌜w = w'⌝)%I as %Heqw.
    { iDestruct "Hread" as "[Hread _]". iSpecialize ("Hread" with "HP"). by iApply interp_eq. }
    destruct r as [r1 r2]. simpl in *.
    iDestruct (interp_reg_eq r1 r2 (WCap p b e a) with "[]") as %Heq;[iSplit;auto|]. rewrite -!Heq.

    iMod (step_Mov _ [SeqCtx] with "[$Ha' $Hsmap $Hs $Hspec]") as (retv' regs'') "(Hs & #Hmovspec & Ha' & Hsmap) /=";[rewrite Heqw in Hi|..];eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_gmap_dom. destruct (decide (PC = rr));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne //].
      destruct Hsome with rr;eauto. }
    { solve_ndisj. }
    iDestruct "Hmovspec" as %HSpec'.

    specialize (Mov_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto.
      iMod ("Hcls" with "[Ha Ha' HP]"); [iExists w,w'; iFrame|iModIntro]. iNext
      ;iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Hregs as [<-|Hcontr];[|inversion Hcontr].
      incrementPC_inv; simplify_map_eq.
      iMod ("Hcls" with "[Ha Ha' HP]") as "_"; [iExists w',w'; iFrame|iModIntro].
      iApply wp_pure_step_later; auto. iNext;iIntros "_".
      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.

      destruct (decide (PC = dst));simplify_eq;simplify_map_eq.
      - rewrite lookup_insert in H1. simplify_eq. rewrite !insert_insert.
        destruct (PermFlowsTo RX x) eqn:Hpft.
        + revert Heq; rewrite map_eq' =>Heq.
          iApply ("IH" $! (r1,r1) with "[] [] Hmap Hsmap Hown Hs Hspec").
          { iPureIntro. simpl. intros reg. destruct Hsome with reg;auto. }
          {  iIntros (ri v1 v2 Hri Hv1s Hv2s) "/=".
            destruct Hsome with ri as [ [v Hsome'] _]. specialize (Heq ri v).
            rewrite !lookup_insert_ne// in Heq. apply Heq in Hsome' as Heq'.
            iSpecialize ("Hreg" $! ri _ _ Hri Hsome' Heq'). by simplify_map_eq.  }
          { destruct src; inversion H0.
            destruct (decide (r = PC));
              [subst r;rewrite lookup_insert in H3;inversion H3;subst|iClear "Hinv";rewrite lookup_insert_ne// in H3];rewrite !fixpoint_interp1_eq /=.
            destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto.
            destruct Hsome with r as [ [v Hsome'] _]. specialize (Heq r).
            rewrite !lookup_insert_ne// in Heq. apply Heq in H3 as Heq'.
            iSpecialize ("Hreg" $! r _ _ n H3 Heq').
           destruct x; inversion Hpft;rewrite fixpoint_interp1_eq /=;iDestruct "Hreg" as "[_ $]";auto.
          }
        + iApply (wp_bind (fill [SeqCtx])).
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct x; simpl in Hpft; try discriminate; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iNext;iIntros "_".
          iApply wp_value.
          iIntros. discriminate.
      - rewrite (insert_commute _ _ PC)// insert_insert.
        iApply ("IH" $! ((<[dst:=w0]> r1),(<[dst:=w0]> r1)) with "[] [] Hmap Hsmap Hown Hs Hspec").
        { iPureIntro. simpl. intros reg. destruct Hsome with reg;auto.
          destruct (decide (dst = reg));[subst;rewrite lookup_insert|rewrite !lookup_insert_ne//];eauto. }
        { simpl. iIntros (rr v1 v2 Hne Hv1s Hv2s).
          destruct (decide (rr = dst));[subst;rewrite lookup_insert in Hv1s,Hv2s |].
          - rewrite lookup_insert_ne // lookup_insert in H1.
            destruct src.
            { simplify_eq. inversion H0. rewrite !fixpoint_interp1_eq;eauto. }
            cbn in H0. pose proof (H0' := H0). rewrite Heq in H0'.
            simplify_map_eq.
            destruct (decide (r = PC));[subst;rewrite /= lookup_insert in H0;inversion H0;done|].
            rewrite !lookup_insert_ne// in H0, H0'.
            by iSpecialize ("Hreg" $! r  _ _ n0 H0 H0').
          - rewrite !lookup_insert_ne// in Hv1s, Hv2s. simplify_eq.
            revert Heq; rewrite map_eq' =>Heq.
            destruct (r1 !! rr) eqn:Hsome';rewrite Hsome' in Hv1s;[|rewrite !fixpoint_interp1_eq;congruence]. inversion Hv1s. subst v1.
            specialize (Heq rr w). rewrite !lookup_insert_ne// in Heq. apply Heq in Hsome' as Heq'.
            by iSpecialize ("Hreg" $! rr _ _ Hne Hsome' Heq').
        }
        { rewrite lookup_insert_ne// lookup_insert in H1. simplify_eq.
          rewrite !fixpoint_interp1_eq /=. destruct Hp as [-> | ->];iDestruct "Hinv" as "[_ $]";auto. }
    }
  Qed.

End fundamental.
