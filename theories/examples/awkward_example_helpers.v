From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel region_invariants fundamental region_invariants_revocation region_invariants_static.


Section awkward_helpers.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Ltac iPrologue prog :=
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  (* TODO: put into revocation file *)
  Lemma related_sts_pub_world_fresh_loc W (i x : positive) r1 r2 :
    i ∉ dom (gset positive) (loc W).1 →
    i ∉ dom (gset positive) (loc W).2 →
    related_sts_pub_world W (W.1,(<[i:=x]> W.2.1, <[i:= (r1,r2)]> W.2.2)).
  Proof.
    rewrite /loc. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) W.2.1 i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) W.2.2 i) in Hdom_rel.
      intros j r1' r2' r1'' r2'' Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left. 
  Qed.

  Lemma updatePcPerm_RX w g b e a :
    inr (RX, g, b, e, a) = updatePcPerm w ->
    w = inr (RX, g, b, e, a) ∨ w = inr (E, g, b, e, a).
  Proof.
    intros Hperm. 
    destruct w;inversion Hperm.
    destruct c,p,p,p,p;simplify_eq;auto.
  Qed.

  Lemma exec_wp W p g b e a :
    isCorrectPC (inr (p, g, b, e, a)) ->
    exec_cond W b e g p interp -∗
    ∀ r W', future_world g W W' → ▷ ((interp_expr interp r) W') (inr (p, g, b, e, a)).
  Proof. 
    iIntros (Hvpc) "Hexec". 
    rewrite /exec_cond /enter_cond. 
    iIntros (r W'). rewrite /future_world.
    assert (a ∈ₐ[[b,e]])%I as Hin. 
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    destruct g. 
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame. 
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame. 
  Qed.
      
  (* The following lemma is to assist with a pattern when jumping to unknown valid capablities *)
  Lemma jmp_or_fail_spec W w φ :
     (interp W w
    -∗ (if decide (isCorrectPC (updatePcPerm w)) then
          (∃ p g b e a, ⌜w = inr (p,g,b,e,a)⌝
          ∗ □ ∀ r W', future_world g W W' → ▷ ((interp_expr interp r) W') (updatePcPerm w))
        else
          φ FailedV ∗ PC ↦ᵣ updatePcPerm w -∗ WP Seq (Instr Executable) {{ φ }} ))%I.
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))). 
    - inversion i.
      destruct w;inversion H. destruct c,p0,p0,p0; inversion H.
      destruct H1 as [-> | [-> | ->] ]. 
      + destruct p0; simpl in H; simplify_eq.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iAlways.
          iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|]. 
          iApply exec_wp;auto.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iAlways.
          rewrite /= fixpoint_interp1_eq /=.
          iExact "Hw". 
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iAlways.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|]. 
        iApply exec_wp;auto.
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iAlways.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].           
        iApply exec_wp;auto.
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto. 
      iEpilogue "_". iApply wp_value. iFrame.
  Qed. 


End awkward_helpers. 
