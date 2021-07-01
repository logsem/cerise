From stdpp Require Import base.
From iris.program_logic Require Import language.
From cap_machine Require Import machine_parameters machine_base cap_lang.

(* The operational semantics as an interpreter: this effectively "runs" the
   machine until it fails or halts (or we run out of fuel). *)

Fixpoint machine_run `{MachineParameters} (fuel: nat) (c: Conf): option ConfFlag :=
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

Lemma machine_run_correct `{MachineParameters} fuel cf (φ: ExecConf) cf':
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

