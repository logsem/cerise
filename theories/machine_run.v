From stdpp Require Import base fin_maps fin_sets gmap.
From iris.program_logic Require Import language.
From cap_machine Require Import machine_parameters machine_base cap_lang.
From cap_machine Require Import stdpp_img linking.

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
                    | WCap _ _ _ a => a
                    | _ => top (* dummy *)
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
        destruct wpc eqn:Hr; [by inversion HPC| | by inversion HPC]. destruct sb as [p b e a | ]; last by inversion HPC.
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

  Fixpoint context_depth expr :=
    match expr with
    | Instr _ => 0
    | Seq expr => S (context_depth expr)
    end.

  Lemma fill_depth K cf :
    context_depth (ectx_language.fill K cf) = length K + context_depth cf.
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
    apply (f_equal context_depth) in H as Hd.
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
    apply (f_equal context_depth) in H as Hd.
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
    apply (f_equal context_depth) in H as Hd.
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
    intros H. apply (f_equal context_depth) in H as Hd.
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
      | WCap _ _ _ a => a
      | _ => finz.largest 0%a
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
      | WCap _ _ _ a => a
      | _ => finz.largest 0%a
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

  (** Shows machine_run is unchanged when adding
      values in the segment at addresses which can't
      be reached by any capability *)
  Section machine_run_subseteq.

    (* A lot of intermediate lemmas showing preservation of can_address_only *)

    Lemma updatePcPerm_preserve_can_addr_only {w s}:
      can_address_only w s -> can_address_only (updatePcPerm w) s.
    Proof.
      unfold can_address_only, updatePcPerm. destruct w;
      [ auto | destruct sb | auto ]; [ destruct p | auto ]; auto.
    Qed.

    Lemma updatePcPerm_regs_preserve_can_addr_only {regs:Reg} {w' seg r}:
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      w' ∈ img regs ->
      ∀ w, w ∈ img (<[r:=updatePcPerm w']> regs) -> can_address_only w seg.
    Proof.
      intros Hr Hw' w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. apply updatePcPerm_preserve_can_addr_only. apply (Hr w' Hw').
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma updatePC_preserve_can_addr_only {regs:Reg} {r p p' b e a a' seg} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      WCap p b e a ∈ img regs ->
      ∀ w, w ∈ img (<[r:=WCap p' b e a']> regs) -> can_address_only w seg.
    Proof.
      intros Hr Hw' w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. unfold can_address_only. apply (Hr _ Hw').
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma restrict_preserve_can_addr_only {regs:Reg} {r p p' b b' e' e a a' seg} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      isWithin b' e' b e = true ->
      WCap p b e a ∈ img regs ->
      ∀ w, w ∈ img (<[r:=WCap p' b' e' a']> regs) -> can_address_only w seg.
    Proof.
      intros Hr Hb Hw' w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. unfold can_address_only.
      intros addr Haddr. apply (Hr _ Hw'). apply isWithin_implies in Hb. solve_addr.
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma word_of_argument_preserve_can_addr_only {regs:Reg} {r w' src seg} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      word_of_argument regs src = Some w' ->
      ∀ w, w ∈ img (<[r:=w']> regs) -> can_address_only w seg.
    Proof.
      intros Hr Hw' w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. destruct src. apply Some_inj in Hw'. rewrite -Hw'. exact I.
      apply Hr. unfold word_of_argument in Hw'. apply (elem_of_img_2 _ _ _ Hw').
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma insert_wint_preserve_can_addr_only {regs:Reg} {r x seg} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      ∀ w, w ∈ img (<[r:=WInt x]> regs) -> can_address_only w seg.
    Proof.
      intros Hr w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. exact I.
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma insert_wsealrange_preserve_can_addr_only {regs:Reg} {r seg p b e a} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      ∀ w, w ∈ img (<[r:=WSealRange p b e a]> regs) -> can_address_only w seg.
    Proof.
      intros Hr w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. exact I.
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    Lemma insert_wsealed_preserve_can_addr_only {regs:Reg} {r o s seg} :
      (∀ w, w ∈ img regs -> can_address_only w seg) ->
      WSealable s ∈ img regs ->
      ∀ w, w ∈ img (<[r:=WSealed o s]> regs) -> can_address_only w seg.
    Proof.
      intros Hr Hw' w Hw. apply elem_of_img in Hw as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. unfold can_address_only. apply (Hr _ Hw').
      apply Hr. apply (elem_of_img_2 _ _ _ Hrw).
    Qed.

    (* Smart matching to apply the above lemmas *)
    Local Ltac solve_can_addr_only :=
      match goal with
      | H: _ !! _ = Some ?w'
      |- ∀ w, w ∈ img (<[_:=updatePcPerm ?w']> _) -> can_address_only w _
        => apply updatePcPerm_regs_preserve_can_addr_only;
           [ solve_can_addr_only | apply (elem_of_img_2 _ _ _ H) ]
      | H: _ !! _ = Some (WCap _ ?b ?e _)
      |- ∀ w, w ∈ img (<[_:=WCap _ ?b ?e _]> _) -> can_address_only w _
        => eapply updatePC_preserve_can_addr_only;
           [ solve_can_addr_only | apply (elem_of_img_2 _ _ _ H) ]
      | H: _ !! _ = Some (WCap _ ?b ?e _), H1 : isWithin ?b' ?e' ?b ?e = true
      |- ∀ w, w ∈ img (<[_:=WCap _ ?b' ?e' _]> _) -> can_address_only w _
        => eapply restrict_preserve_can_addr_only;
           [ solve_can_addr_only | apply H1 | apply (elem_of_img_2 _ _ _ H) ]
      | H: word_of_argument _ ?src = Some ?w'
      |- ∀ w, w ∈ img (<[_:=?w']> _) -> can_address_only w _
        => eapply word_of_argument_preserve_can_addr_only;
           [ solve_can_addr_only | apply H ]
      | |- ∀ w, w ∈ img (<[_:=WInt _]> _) -> can_address_only w _
        => eapply insert_wint_preserve_can_addr_only; solve_can_addr_only
      | |- ∀ w, w ∈ img (<[_:=WSealRange _ _ _ _]> _) -> can_address_only w _
        => eapply insert_wsealrange_preserve_can_addr_only; solve_can_addr_only
      | H: _ !! _ = Some (WSealable ?s) |- ∀ w, w ∈ img (<[_:=WSealed _ ?s]> _) -> can_address_only w _
        => eapply insert_wsealed_preserve_can_addr_only;
           [ solve_can_addr_only | apply (elem_of_img_2 _ _ _ H) ]
      | _ => auto
      end.

    (** This destruct the successive matches/tests in exec to
        quickly get to a base simple case; then it tries to solve it with
        solve_can_addr_only

        Called with H of the form (_, (_, _)) = exec i (_, _) *)
    Local Ltac destruct_exec H :=
      match type of H with
      | _ = match ?b ≫= _ with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d; simpl in H; destruct_exec H
      | _ = match (if ?b then _ else _) with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d; simpl in H; destruct_exec H
      | _ = match (match ?b with _ => _ end) with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d; simpl in H; destruct_exec H
      | _ = match updatePC _ with _ => _ end =>
          unfold updatePC in H; simpl in H; destruct_exec H
      | _ = (_, update_reg _ _ _) =>
          unfold update_reg in H; simpl in H; destruct_exec H
      | (_, (_, _)) = (_, (_, _)) =>
          apply pair_equal_spec in H as [_ H];
          apply pair_equal_spec in H as [Heq_reg Heq_ms];
          simpl in Heq_ms, Heq_reg; rewrite Heq_ms Heq_reg;
          split; try split; solve_can_addr_only
      end.

    (* exec preserve our can_address_only predicate,
       and stays in the designated memory region *)
    Lemma exec_segment_preserve_can_addr_only {i c regs seg regs' seg'} :
      (∀ w, w ∈ img seg -> can_address_only w (dom seg)) ->
      (∀ w, w ∈ img regs -> can_address_only w (dom seg)) ->
      (c, (regs', seg')) = exec i (regs, seg) ->
      dom seg = dom seg' /\
      (∀ w, w ∈ img seg' -> can_address_only w (dom seg')) /\
      (∀ w, w ∈ img regs' -> can_address_only w (dom seg')).
    Proof.
      intros Hwr_seg Hwr_regs Heq.
      unfold exec, exec_opt in Heq; destruct i; simpl in Heq.

      all: destruct_exec Heq.
      intros w' Hw'. apply elem_of_img in Hw' as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w. apply Hwr_seg. simplify_eq.
      apply (elem_of_img_2 _ _ _ Heq_d3).
      apply Hwr_regs. apply (elem_of_img_2 _ _ _ Hrw).

      symmetry. apply dom_insert_lookup_L.
      apply (elem_of_img_2 (D:=gset _)), Hwr_regs in Heq_d0.
      specialize (Heq_d0 f1).
      rewrite -elem_of_dom. apply Heq_d0.
      apply andb_true_iff in Heq_d3 as [_ Hwithinbounds].
      apply withinBounds_true_iff in Hwithinbounds. apply Hwithinbounds.

      intros w' Hw'. apply elem_of_img in Hw' as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      rewrite -Hw'w.
      destruct src; simpl in Heq_d.
      apply Some_inj in Heq_d. rewrite -Heq_d. exact I.
      apply (can_address_only_subseteq_stable _ (dom seg)). set_solver.
      apply Hwr_regs. apply (elem_of_img_2 _ _ _ Heq_d).
      apply (can_address_only_subseteq_stable _ (dom seg)). set_solver.
      apply Hwr_seg. apply (elem_of_img_2 _ _ _ Hrw).

      intros w' Hw'.
      apply (can_address_only_subseteq_stable _ (dom seg)). set_solver.
      apply (Hwr_regs w' Hw').

      destruct (decide (dst=PC)) as [Heq|Hneq]. rewrite Heq lookup_insert in Heq_d5.
      apply Some_inj in Heq_d5. inversion Heq_d5.
      rewrite H0 in Heq_d0.
      intros w' Hw'. apply elem_of_img in Hw' as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      apply (elem_of_img_2 (D:=gset _)) in Heq_d0.
      rewrite -Hw'w. unfold can_address_only. apply (Hwr_regs _ Heq_d0).
      apply Hwr_regs. apply (elem_of_img_2 _ _ _ Hrw).

      destruct s0.
      intros w' Hw'. apply elem_of_img in Hw' as [r' Hrw].
      apply lookup_insert_Some in Hrw as [[HPCr Hw'w] | [HPCr Hrw]].
      apply (elem_of_img_2 (D:=gset _)) in Heq_d0.
      rewrite -Hw'w. unfold can_address_only. apply (Hwr_regs _ Heq_d0).
      apply Hwr_regs. apply (elem_of_img_2 _ _ _ Hrw).
      apply insert_wsealrange_preserve_can_addr_only; assumption.
    Qed.

    (* Same concept as destruct_exec, but with two hypotheses of the form
       (_, (_, _)) = exec i (_, _) *)
    Local Ltac destruct_exec2 H H2 :=
      match type of H with
      | _ = match ?b ≫= _ with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d;
          try rewrite (lookup_union_Some_l _ _ _ _ Heq_d) in H2; simpl in H, H2;
          destruct_exec2 H H2
      | _ = match (if ?b then _ else _) with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d; simpl in H, H2; destruct_exec2 H H2
      | _ = match (match ?b with _ => _ end) with _ => _ end =>
          let Heq_d := fresh "Heq_d" in
          destruct b eqn:Heq_d; simpl in H, H2; destruct_exec2 H H2
      | _ = match updatePC _ with _ => _ end =>
          unfold updatePC in H, H2; simpl in H, H2; destruct_exec2 H H2
      | _ = (_, update_reg _ _ _) =>
          unfold update_reg in H, H2; simpl in H, H2; destruct_exec2 H H2
      | (_, (_, _)) = (_, (_, _)) =>
          apply pair_equal_spec in H as [Hc H];
          apply pair_equal_spec in H as [Heq_reg Heq_ms];
          apply pair_equal_spec in H2 as [H2c H2];
          apply pair_equal_spec in H2 as [H2eq_reg H2eq_ms];
          simpl in Heq_ms, Heq_reg, H2eq_ms, H2eq_reg;
          split; try split; (try simplify_eq; auto)
      | _ => idtac
      end.

    (** Calling exec on (r,s ∪ s') when r and s can_address_only s
        is the same as calling exec on (r,s) and then adding s'.

        writing s2 as s ∪ s' is a just a way of saying s ⊆ s2
        and calling s' the difference between s and s' *)
    Lemma exec_segment_subseteq {i c c1 regs seg seg1 regs' regs1' seg' seg1'} :
      (∀ w, w ∈ img seg -> can_address_only w (dom seg)) ->
      (∀ w, w ∈ img regs -> can_address_only w (dom seg)) ->
      (c, (regs', seg')) = exec i (regs, seg) ->
      (c1, (regs1', seg1')) = exec i (regs, seg ∪ seg1) ->
      c = c1 /\ regs' = regs1' /\ seg1' = seg' ∪ seg1.
    Proof.
      intros Hwr_seg Hwr_regs Heq Heq'.
      unfold exec, exec_opt in Heq, Heq'.
      destruct i; simpl in Heq, Heq'.
      all: destruct_exec2 Heq Heq'.
      apply andb_true_iff in Heq_d2 as [_ Hbounds]. apply withinBounds_true_iff in Hbounds.
      specialize (Hwr_regs (WCap p f f0 f1) (elem_of_img_2 _ _ _ Heq_d) f1 Hbounds).
      rewrite elem_of_dom Heq_d3 in Hwr_regs. contradiction (is_Some_None Hwr_regs).
      apply insert_union_l.
    Qed.

    Lemma machine_run_segment_subseteq {n cf regs seg1 seg2}:
      seg1 ⊆ seg2 ->
      (∀ w, w ∈ img seg1 -> can_address_only w (dom seg1)) ->
      (∀ w, w ∈ img regs -> can_address_only w (dom seg1)) ->
      machine_run n (cf, (regs, seg1)) = machine_run n (cf, (regs, seg2)).
    Proof.
      revert n cf regs seg1 seg2.
      induction n.
      intros cf regs seg1 seg2 Hincl Hwr_ms Hwr_regs. reflexivity.
      intros cf regs seg1 seg2 Hincl Hwr_ms Hwr_regs. simpl.
      destruct cf.
      4: apply (IHn _ regs seg1 seg2 Hincl Hwr_ms Hwr_regs).
      destruct (regs !! PC) as [pc|] eqn:regs_pc.
      destruct (isCorrectPCb pc) eqn:pcv.
      rewrite isCorrectPCb_isCorrectPC in pcv.
      inversion pcv. rewrite <- H1 in regs_pc.
      specialize (Hwr_regs _ (elem_of_img_2 _ _ _ regs_pc) a H) as Ha.
      apply elem_of_dom in Ha as [w seg1a_w].
      unfold Mem in *. rewrite seg1a_w.
      destruct (map_subseteq_spec seg1 seg2) as [ seg2a_w _ ].
      specialize (seg2a_w Hincl a w seg1a_w).
      rewrite seg2a_w.
      destruct (exec (decodeInstrW w) (regs, seg1)) as [c' [regs' seg']] eqn:Heq'.
      destruct (exec (decodeInstrW w) (regs, seg2)) as [c1' [regs1' seg1']] eqn:Heq1'.
      symmetry in Heq', Heq1'. simpl.
      destruct (exec_segment_preserve_can_addr_only Hwr_ms Hwr_regs Heq') as [Hdom [Hwr_seg' Hwr_regs']].
      assert (Hseg: seg2 = seg1 ∪ seg2).
      symmetry. apply map_subseteq_union. exact Hincl.
      rewrite Hseg in Heq1'.

      destruct (exec_segment_subseteq Hwr_ms Hwr_regs Heq' Heq1') as [Hc [Hr Hs]].
      rewrite -Hc -Hr Hs.
      eapply (IHn c' regs' seg' _ _ Hwr_seg' Hwr_regs').
      all: reflexivity.
      Unshelve. apply map_union_subseteq_l.
    Qed.
  End machine_run_subseteq.

End machine_run.
