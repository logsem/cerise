From stdpp Require Import base.
From iris.program_logic Require Import language.
From cap_machine Require Import machine_parameters machine_base cap_lang.

Section machine_run.
  Context {MP:MachineParameters}.

  (* The operational semantics as an interpreter: this effectively "runs" the
    machine until it fails or halts (or we run out of fuel). *)

  Fixpoint machine_run (fuel: nat) (c: Conf): option ConfFlag :=
    match fuel with
    | 0 => None
    | S fuel =>
      match c with
      | (Failed, _) => Some Failed
      | (Halted, _) => Some Halted
      | (NextI, φ) => machine_run fuel (Executable, φ)
      | (Executable, (r, m)) =>
        match r !! PC with
        | None => Some Failed
        | Some pc =>
          if isCorrectPCb pc then (
            let a := match pc with
                    | WInt _ => top (* dummy *)
                    | WCap _ _ _ a => a
                    end in
            match m !! a with
            | None => Some Failed
            | Some wa =>
                let i := decodeInstrW wa in
                let c' := exec i (r, m) in
                machine_run fuel (c'.1, c'.2)
            end
          ) else (
            Some Failed
          )
        end
      end
    end.

  Lemma machine_run_correct fuel cf (φ: ExecConf) cf':
    machine_run fuel (cf, φ) = Some cf' →
    ∃ φ', rtc erased_step
              ([Seq (Instr cf)], φ)
              ([Instr cf'], φ').
  Proof.
    revert cf cf' φ. induction fuel.
    { cbn. done. }
    { cbn. intros ? ? [r m] Hc.
      destruct cf; simplify_eq.
      destruct (r !! PC) as [wpc | ] eqn:HePC.
      2: {
        eexists. eapply rtc_l. unfold erased_step. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
        constructor. constructor; auto.
        eapply rtc_once. exists []. simplify_eq.
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        constructor. }
      destruct (isCorrectPCb wpc) eqn:HPC.
      { apply isCorrectPCb_isCorrectPC in HPC.
        destruct wpc eqn:Hr; [by inversion HPC|].
        destruct (m !! a) as [wa | ] eqn:HeMem.
        2: {
          eexists. eapply rtc_l. unfold erased_step. exists [].
          eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
          eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
          constructor. eapply step_exec_memfail; eauto.
          eapply rtc_once. exists []. simplify_eq.
          eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
          eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
          constructor. }
        eapply IHfuel in Hc as [φ' Hc]. eexists.
        eapply rtc_l. unfold erased_step. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity.
        constructor. eapply step_exec_instr; eauto. rewrite Hr //.
      }
      { simplify_eq. apply isCorrectPCb_nisCorrectPC in HPC.
        eexists. eapply rtc_l. unfold erased_step. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
        constructor. eapply step_exec_corrfail; eauto.
        eapply rtc_once. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        constructor. }
      { eexists. eapply rtc_once. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        econstructor. }
      { eexists. eapply rtc_once. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        econstructor. }
      { apply IHfuel in Hc as [φ' Hc]. eexists.
        eapply rtc_l. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        econstructor. cbn. apply Hc. } }
  Qed.

  Fixpoint depth expr :=
    match expr with
    | Instr _ => 0
    | Seq expr => S (depth expr)
    end.

  Lemma fill_depth K cf :
    depth (ectx_language.fill K cf) = length K + depth cf.
  Proof.
    generalize cf. clear cf.
    induction K.
    reflexivity. intros cf.
    destruct a. simpl.
    rewrite (IHK (Seq cf)).
    simpl. lia.
  Qed.

  Lemma fill_seq_seq {cf K cf'} :
    Seq (Instr cf) = ectx_language.fill K (Seq (Instr cf')) ->
    K = [] /\ cf = cf'.
  Proof.
    intros H.
    apply (f_equal depth) in H as Hd.
    rewrite fill_depth in Hd. simpl in Hd.
    assert (Hk : K = []).
    apply nil_length_inv.
    apply (Nat.add_cancel_r _ _ 1).
    symmetry. simpl. exact Hd.
    split. exact Hk.
    rewrite Hk in H. inversion H. reflexivity.
  Qed.

  Lemma fill_seq_instr {cf k cf'} :
    Seq (Instr cf) = ectx_language.fill k (Instr cf') ->
    k = [ SeqCtx ] /\ cf = cf'.
  Proof.
    intros H.
    apply (f_equal depth) in H as Hd.
    rewrite fill_depth in Hd. simpl in Hd.
    destruct k; simpl in Hd. lia.
    apply (inj S) in Hd. rewrite Nat.add_0_r in Hd.
    assert (Hk : k = []).
    apply nil_length_inv. symmetry. exact Hd.
    rewrite Hk. destruct e.
    split. reflexivity. rewrite Hk in H. inversion H. reflexivity.
  Qed.

  Lemma fill_simpl {cf K e} :
    Seq (Instr cf) = ectx_language.fill K e ->
    e = Instr cf \/ e = Seq (Instr cf).
  Proof.
    intros H.
    apply (f_equal depth) in H as Hd.
    rewrite fill_depth in Hd.
    destruct e; simpl in Hd.
    left.
    destruct K; simpl in Hd. discriminate.
    assert (Hk : K = []).
    apply nil_length_inv.
    apply (inj S) in Hd. rewrite Nat.add_0_r in Hd.
    symmetry. apply Hd. rewrite Hk in H.
    destruct e. simpl in H. inversion H. reflexivity.
    right. assert (Hk : K = []).
    apply nil_length_inv. rewrite Nat.add_succ_r in Hd.
    apply (inj S) in Hd. symmetry in Hd.
    apply Nat.eq_add_0 in Hd. destruct Hd. assumption.
    rewrite Hk in H. simpl in H. inversion H. reflexivity.
  Qed.

  Lemma fill_instr {c k e}:
    Instr c = ectx_language.fill k e -> Instr c = e.
  Proof.
    intros H. apply (f_equal depth) in H as Hd.
    rewrite fill_depth in Hd. simpl in Hd.
    assert (Hk : k = []).
    apply nil_length_inv. symmetry in Hd. apply Nat.eq_add_0 in Hd.
    destruct Hd as [Hd _]. apply Hd.
    rewrite Hk in H. simpl in H. inversion H. reflexivity.
  Qed.

  Lemma singleton_app_cons {A:Type} {e e':A} {t t':list A} :
    [e] = t ++ e' :: t' -> e = e' /\ t = [] /\ t' = [].
  Proof.
    intros H. symmetry in H. apply app_singleton in H.
    destruct H as [[Ht Het]|[_ Habsurd]].
    2: discriminate.
    apply (inj2 cons) in Het as [l r]. auto.
  Qed.

  Lemma erased_step_halted {cf φ φ'}:
    rtc erased_step ([Instr Halted], φ) ([Instr cf], φ') ->
    cf = Halted.
  Proof.
    intros Hstep.
    rewrite erased_steps_nsteps in Hstep.
    destruct Hstep as [n [ks Hstep]].
    revert Hstep. generalize ks. clear ks.
    induction n.
    intros. inversion Hstep. reflexivity.
    intros. inversion Hstep.
    inversion H0.
    apply pair_equal_spec in H5 as [H5 Hφ].
    apply singleton_app_cons in H5 as [He [Ht1 Ht2]].
    rewrite -He in H7.
    inversion H7. simpl in K, e1', e2'.
    apply fill_instr in H5.
    rewrite -H5 in H9; inversion H9.
  Qed.

  Lemma erased_step_failed {cf φ φ'}:
    rtc erased_step ([Instr Failed], φ) ([Instr cf], φ') ->
    cf = Failed.
  Proof.
    intros Hstep.
    rewrite erased_steps_nsteps in Hstep.
    destruct Hstep as [n [ks Hstep]].
    revert Hstep. generalize ks. clear ks.
    induction n.
    intros. inversion Hstep. reflexivity.
    intros. inversion Hstep.
    inversion H0.
    apply pair_equal_spec in H5 as [H5 Hφ].
    apply singleton_app_cons in H5 as [He [Ht1 Ht2]].
    rewrite -He in H7.
    inversion H7. simpl in K, e1', e2'.
    apply fill_instr in H5.
    rewrite -H5 in H9; inversion H9.
  Qed.

  Lemma erased_step_seq_halted {cf φ φ'}:
    rtc erased_step ([Seq (Instr Halted)], φ) ([Instr cf], φ') ->
    cf = Halted.
  Proof.
    intros Hstep.
    rewrite erased_steps_nsteps in Hstep.
    destruct Hstep as [n [ks Hstep]].
    inversion Hstep.
    inversion H.
    apply pair_equal_spec in H5 as [H5 Hφ].
    apply singleton_app_cons in H5 as [He [Ht1 Ht2]].
    rewrite -He in H7.
    inversion H7. simpl in K, e1', e2'.
    destruct (fill_simpl H5) as [He1 | He1];
    rewrite He1 in H9; inversion H9.
    rewrite He1 in H5. apply fill_seq_seq in H5 as [HK _].
    rewrite HK -H13 in H8. simpl in H8.
    rewrite H8 Ht1 Ht2 -H15 -H14 -Hφ in H6. simpl in H6.
    rewrite H6 in H0.
    apply (ex_intro (fun κs => nsteps n0 ([Instr Halted], φ) κs ([Instr cf], φ')) κs) in H0.
    apply (ex_intro (fun n0 => ∃ κs, nsteps n0 ([Instr Halted], φ) κs ([Instr cf], φ')) n0) in H0.
    rewrite -erased_steps_nsteps in H0.
    apply (erased_step_halted H0).
  Qed.

  Lemma erased_step_seq_failed {cf φ φ'}:
    rtc erased_step ([Seq (Instr Failed)], φ) ([Instr cf], φ') ->
    cf = Failed.
  Proof.
    intros Hstep.
    rewrite erased_steps_nsteps in Hstep.
    destruct Hstep as [n [ks Hstep]].
    inversion Hstep.
    inversion H.
    apply pair_equal_spec in H5 as [H5 Hφ].
    apply singleton_app_cons in H5 as [He [Ht1 Ht2]].
    rewrite -He in H7.
    inversion H7. simpl in K, e1', e2'.
    destruct (fill_simpl H5) as [He1 | He1];
    rewrite He1 in H9; inversion H9.
    rewrite He1 in H5. apply fill_seq_seq in H5 as [HK _].
    rewrite HK -H13 in H8. simpl in H8.
    rewrite H8 Ht1 Ht2 -H15 -H14 -Hφ in H6. simpl in H6.
    rewrite H6 in H0.
    apply (ex_intro (fun κs => nsteps n0 ([Instr Failed], φ) κs ([Instr cf], φ')) κs) in H0.
    apply (ex_intro (fun n0 => ∃ κs, nsteps n0 ([Instr Failed], φ) κs ([Instr cf], φ')) n0) in H0.
    rewrite -erased_steps_nsteps in H0.
    apply (erased_step_failed H0).
  Qed.

  Lemma machine_run_complete cf (φ φ': ExecConf) cf':
    rtc erased_step ([Seq (Instr cf)], φ) ([Instr cf'], φ') ->
    ∃ fuel, machine_run fuel (cf, φ) = Some cf'.
  Proof.
    intros Hstep. rewrite rtc_list in Hstep.
    destruct Hstep as [l [Hhd [Htl Hstep]]].
    revert Hhd Htl Hstep. revert φ φ' cf cf'.
    induction l; intros. discriminate Hhd.
    apply Some_inj in Hhd.
    destruct l as [|b l].
    apply Some_inj in Htl. rewrite Hhd in Htl. discriminate.

    specialize (Hstep 0 a b eq_refl eq_refl) as Hstep'.
    destruct Hstep' as [k Hstep'].
    inversion Hstep' as [e1 σ1 e2 σ2 extra t1 t2 Ha Hb Hstep''].
    inversion Hstep'' as [K e1' e2' He1 He2 Hstep''']. simpl in K, e1', e2'.
    rewrite Hhd in Ha.
    apply pair_equal_spec in Ha as [Ha Hφ].
    apply singleton_app_cons in Ha as [He1' [Ht1 Ht2]].
    rewrite Ht1 Ht2 in Hb. simpl in Hb.

    inversion Hstep'''.
    - inversion H.
      all: rewrite -H7 in H3;
             rewrite -He1' -H0 in He1;
             apply fill_seq_instr in He1 as [Hk He1];
             rewrite Hk -H3 in He2; simpl in He2;
             rewrite He2 -H5 in Hb. 1,2,3: simplify_eq.
      1,2,3: assert (IH: ∃ fuel : nat, machine_run fuel (Failed, σ2) = Some cf').
      1,3,5: apply (IHl σ2 φ' Failed cf'); try auto;
             intros i a' b' Hi Hsi; apply (Hstep (S i) a' b');
             simpl; assumption.
      1,2,3: destruct IH as [fuel Hmr]; exists (S fuel); simpl;
             destruct σ2 as [r m].
      + simpl in H8. rewrite H8.
        destruct fuel; simpl in Hmr. discriminate.
        apply Hmr.
      + simpl in H9. rewrite H9.
        rewrite -isCorrectPCb_nisCorrectPC in H10.
        rewrite H10.
        destruct fuel; simpl in Hmr. discriminate. apply Hmr.
      + simpl in H9. rewrite H9. simpl in H10.
        destruct (isCorrectPCb (WCap p b0 e a0)).
        rewrite H10.
        all: destruct fuel; simpl in Hmr; discriminate || apply Hmr.
      + rewrite He1. rewrite He1 in He1' Hhd.
        assert (IH: ∃ fuel : nat, machine_run fuel (c.1, σ2) = Some cf').
        apply (IHl σ2 φ'). rewrite Hb. reflexivity.
        auto. intros j a' b' Hi Hsi; apply (Hstep (S j) a' b');
        simpl; assumption.
        destruct IH as [fuel Hmr]; exists (S fuel); simpl.
        rewrite Hφ. destruct σ1 as [r m].
        rewrite -isCorrectPCb_isCorrectPC in H11.
        rewrite -H12 in H13.
        rewrite H9 H11 H10 H13 H8. apply Hmr.
    - rewrite -He1' -H in He1. apply fill_seq_seq in He1.
      destruct He1 as [HK Hcf].
      rewrite HK in He2. simpl in He2.
      rewrite Hcf.
      rewrite He2 -H2 -H3 -H4 -Hφ in Hb.
      specialize (IHl φ φ' Executable cf').
      assert (IH: ∃ fuel : nat, machine_run fuel (Executable, φ) = Some cf').
      { apply IHl. simpl. rewrite Hb. reflexivity.
        apply Htl.
        intros i a' b' Hi Hsi.
        apply (Hstep (S i) a' b'); simpl; assumption. }
      destruct IH as [fuel Hmr]. exists (S fuel). simpl. apply Hmr.
    - rewrite -He1' -H in He1. apply fill_seq_seq in He1.
      destruct He1 as [HK Hcf].
      rewrite HK in He2. simpl in He2.
      rewrite Hcf.
      rewrite He2 -H2 -H3 -H4 -Hφ in Hb.
      rewrite Hcf in He1', Hhd. rewrite Hhd in Hstep.
      assert (cf' = Halted).
      eapply erased_step_seq_halted.
      apply rtc_list.
      exists (([Seq (Instr Halted)], φ) :: b :: l).
      split. reflexivity.
      split. apply Htl. apply Hstep.
      rewrite H5. exists 1. simpl. reflexivity.
    - rewrite -He1' -H in He1. apply fill_seq_seq in He1.
      destruct He1 as [HK Hcf].
      rewrite HK in He2. simpl in He2.
      rewrite Hcf.
      rewrite He2 -H2 -H3 -H4 -Hφ in Hb.
      rewrite Hcf in He1', Hhd. rewrite Hhd in Hstep.
      assert (cf' = Failed).
      eapply erased_step_seq_failed.
      apply rtc_list.
      exists (([Seq (Instr Failed)], φ) :: b :: l).
      split. reflexivity.
      split. apply Htl. apply Hstep.
      rewrite H5. exists 1. simpl. reflexivity.
  Qed.

  Lemma machine_run_ends_in_halted_or_error:
    ∀ {n init c},
      machine_run n init = Some c ->
      c = Halted \/ c = Failed.
  Proof.
    intros n.
    induction n; intros init c mr.
    - discriminate mr.
    - simpl in mr.
      destruct init as [[ | | | ] [r m]].
      destruct (r !! PC).
      destruct (isCorrectPCb w).
      destruct (m !! match w with
      | WInt _ => finz.largest 0%a
      | WCap _ _ _ a => a
      end). apply IHn in mr. apply mr.
      1,2,3,5: right; symmetry; apply Some_inj in mr; apply mr.
      left; symmetry. apply Some_inj in mr; apply mr.
      apply IHn in mr. apply mr.
  Qed.

  Lemma machine_run_ends_incr:
    ∀ {n n' init c},
      n <= n' ->
      machine_run n init = Some c ->
      machine_run n' init = Some c.
  Proof.
    intros n n'. generalize n. clear n.
    induction n'.
    - intros n init c n_inf_0. apply Nat.le_0_r in n_inf_0.
      rewrite n_inf_0. auto.
    - intros n [ conf [r m] ] c n_inf_n'.
      apply PeanoNat.Nat.le_succ_r in n_inf_n'.
      destruct n_inf_n' as [n_inf_n' | n_eq_n'].
      2: { rewrite n_eq_n'. auto. }
      destruct n as [ | n ]. intros mr_n. discriminate mr_n.
      simpl.
      destruct conf.
      destruct (r !! PC).
      destruct (isCorrectPCb w).
      destruct (m !! match w with
      | WInt _ => finz.largest 0%a
      | WCap _ _ _ a => a
      end).
      all: try auto.
      all: apply IHn'; lia.
  Qed.

  Lemma machine_run_unique_result:
    ∀ {n n' c c' init},
      machine_run n init = Some c ->
      machine_run n' init = Some c' ->
      c = c'.
  Proof.
    intros n n' c c' init mr mr'.
    destruct (le_lt_dec n n') as [nn' | nn'].
    2: apply Nat.lt_le_incl in nn'.
    rewrite (machine_run_ends_incr nn' mr) in mr'.
    2: rewrite (machine_run_ends_incr nn' mr') in mr.
    apply Some_inj in mr'. apply mr'.
    apply Some_inj in mr. symmetry. apply mr.
  Qed.

End machine_run.
