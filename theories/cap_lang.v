From iris.prelude Require Import prelude.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg machine_base machine_parameters.

(* Context { M : CoreParameters }. *)
Ltac inv H := inversion H; clear H; subst.

Section cap_lang.

  Context `{CP : CoreParameters}.

Definition ExecConf := (Reg * Mem)%type.

Inductive CoreState : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition ExecState := gmap CoreN CoreState.

Definition CoreConf  : Type := CoreState * ExecConf.
Definition Conf  : Type := ExecState * ExecConf.

Definition reg  (ϕ: ExecConf) := fst ϕ.

Definition mem  (ϕ: ExecConf) := snd ϕ.

Definition update_reg  (φ: ExecConf) (i: CoreN) (r: RegName) (w: Word): ExecConf
  := (<[(i,r):=w]>(reg φ),mem φ).
Definition update_mem  (φ: ExecConf) (a: Addr) (w: Word): ExecConf
  := (reg φ, <[a:=w]>(mem φ)).
Definition update_state  (s: ExecState) (i : CoreN) (cs : CoreState) : ExecState
  := <[i:=cs]> s.

Lemma update_state_lookup :
  forall es i c,
  update_state es i c !! i = Some c.
Proof.
  intros.
  by apply lookup_insert.
Qed.

(* Note that the `None` values here also undo any previous changes that were tentatively made in the same step. This is more consistent across the board. *)
Definition updatePC (i : CoreN) (φ: ExecConf)
  : option CoreConf :=
  match (reg φ) !! (i,PC) with
  | Some (WCap p b e a) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ i PC (WCap p b e a')) in
               Some (NextI, φ')
    | None => None
    end
  | _ => None
  end.


Definition updatePC' (i : CoreN) (s: ExecState) (φ: ExecConf) : option Conf :=
  match (reg φ) !! (i,PC) with
  | Some (WCap p b e a) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ i PC (WCap p b e a')) in
               Some (update_state s i NextI, φ')
    | None => None
    end
  | _ => None
  end.


(*--- z_of_argument ---*)

Definition z_of_argument (regs: Reg) (i : CoreN) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! (i,r) with
    | Some (WInt z) => Some z
    | _ => None
    end
  end.

Lemma z_of_argument_Some_inv (regs: Reg) (i : CoreN) (arg: Z + RegName) (z:Z) :
  z_of_argument regs i arg = Some z →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! (i, r) = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma z_of_argument_Some_inv' (regs regs': Reg) (i : CoreN) (arg: Z + RegName) (z:Z) :
  z_of_argument regs i arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r, arg = inr r
                      ∧ regs !! (i, r) = Some (WInt z)
                      ∧ regs' !! (i, r) = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma z_of_arg_mono (regs r: Reg) (i : CoreN) arg argz:
regs ⊆ r
-> z_of_argument regs i arg = Some argz
-> z_of_argument r i arg = Some argz.
Proof.
  intros.
  unfold z_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply (@lookup_weaken (prod (@CoreN CP) RegName)) in Heq as ->; auto.
Qed.

(*--- word_of_argument ---*)

Definition word_of_argument (regs: Reg) (i : CoreN) (a: Z + RegName): option Word :=
  match a with
  | inl n => Some (WInt n)
  | inr r => regs !! (i,r)
  end.

Lemma word_of_argument_Some_inv (regs: Reg) (i : CoreN) (arg: Z + RegName) (w:Word) :
  word_of_argument regs i arg = Some w →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !! (i,r) = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma word_of_argument_Some_inv' (regs regs': Reg) (i : CoreN) (arg: Z + RegName) (w:Word) :
  word_of_argument regs i arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !! (i,r) = Some w ∧ regs' !! (i,r) = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma word_of_argument_inr (regs: Reg) (i : CoreN) (arg: Z + RegName) p b e a:
  word_of_argument regs i arg = Some (WCap p b e a) →
  (∃ r : RegName, arg = inr r ∧ regs !! (i,r) = Some (WCap p b e a)).
Proof.
  intros HStoreV.
  unfold word_of_argument in HStoreV.
  destruct arg.
      - by inversion HStoreV.
      - exists r. split;auto.
Qed.

Lemma word_of_arg_mono (regs r: Reg) (i : CoreN) arg w:
regs ⊆ r
-> word_of_argument regs i arg = Some w
-> word_of_argument r i arg = Some w.
Proof.
  intros.
  unfold word_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply (@lookup_weaken (prod (@CoreN CP) RegName)) in Heq as ->; auto.
Qed.

(*--- addr_of_argument ---*)

Definition addr_of_argument regs (i : CoreN) src :=
  match z_of_argument regs i src with
  | Some n => z_to_addr n
  | None => None
  end.

Lemma addr_of_argument_Some_inv (regs: Reg) (i : CoreN) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs i arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! (i,r) = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma addr_of_argument_Some_inv' (regs regs': Reg) (i : CoreN) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs i arg = Some a →
  regs ⊆ regs' →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! (i,r) = Some (WInt z) ∧ regs' !! (i,r) = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma addr_of_arg_mono (regs r: Reg) (i : CoreN) arg w:
regs ⊆ r
-> addr_of_argument regs i arg = Some w
-> addr_of_argument r i arg = Some w.
Proof.
  intros.
  unfold addr_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply (@lookup_weaken (prod (@CoreN CP) RegName)) in Heq as ->; auto.
Qed.
End cap_lang.

Section opsem.
  Context `{CP : CoreParameters}.
  Context `{MachineParameters}.

  Definition exec_opt (it: instr) (i : CoreN) (φ : ExecConf)
    : option CoreConf :=
    match it with
    | Fail => Some (Failed, φ)
    | Halt => Some (Halted, φ)
    | Jmp r =>
        wr ← (reg φ) !! (i,r) ;
        let φ' := (update_reg φ i PC (updatePcPerm wr)) in
        Some (NextI, φ') (* Note: allow jumping to integers, sealing ranges etc; machine will crash later *)
    | Jnz r1 r2 =>
        wr2 ← (reg φ) !! (i,r2);
        wr1 ← (reg φ) !! (i,r1);
        if nonZero wr2 then
          let φ' := (update_reg φ i PC (updatePcPerm wr1)) in
          Some (NextI, φ')
        else updatePC i φ
    | Load dst src =>
        wsrc ← (reg φ) !! (i,src);
        match wsrc with
        | WCap p b e a =>
            if readAllowed p && withinBounds b e a then
              asrc ← (mem φ) !! a;
              updatePC i (update_reg φ i dst asrc)
            else None
        | _ => None
        end
    | Store dst ρ =>
      tostore ← word_of_argument (reg φ) i ρ;
      wdst ← (reg φ) !! (i,dst);
      match wdst with
      | WCap p b e a =>
          if writeAllowed p && withinBounds b e a then
            updatePC i (update_mem φ a tostore)
          else None
      | _ => None
      end
    | Mov dst ρ =>
      tomov ← word_of_argument (reg φ) i ρ;
      updatePC i (update_reg φ i dst tomov)
    | Lea dst ρ =>
      n ← z_of_argument (reg φ) i ρ;
      wdst ← (reg φ) !! (i,dst);
      match wdst with
      | WInt _ => None
      | WCap p b e a =>
          match p with
          | E => None
          | _ => match (a + n)%a with
                | Some a' => updatePC i (update_reg φ i dst (WCap p b e a'))
                | None => None
                end
          end
      end
  | Restrict dst ρ =>
      n ← z_of_argument (reg φ) i ρ ;
      wdst ← (reg φ) !! (i,dst);
      match wdst with
      | WInt _ => None
      | WCap permPair b e a =>
          match permPair with
          | E => None
          | _ => if PermFlowsTo (decodePerm n) permPair then
                  updatePC i (update_reg φ i dst (WCap (decodePerm n) b e a))
                else None
          end
      end
  | Add dst ρ1 ρ2 =>
      n1 ← z_of_argument (reg φ) i ρ1;
      n2 ← z_of_argument (reg φ) i ρ2;
      updatePC i (update_reg φ i dst (WInt (n1 + n2)%Z))
  | Sub dst ρ1 ρ2 =>
      n1 ← z_of_argument (reg φ) i ρ1;
      n2 ← z_of_argument (reg φ) i ρ2;
      updatePC i (update_reg φ i dst (WInt (n1 - n2)%Z))
  | Lt dst ρ1 ρ2 =>
      n1 ← z_of_argument (reg φ) i ρ1;
      n2 ← z_of_argument (reg φ) i ρ2;
      updatePC i (update_reg φ i dst (WInt (Z.b2z (Z.ltb n1 n2))))
  | Subseg dst ρ1 ρ2 =>
      a1 ← addr_of_argument (reg φ) i ρ1;
      a2 ← addr_of_argument (reg φ) i ρ2;
      wdst ← (reg φ) !! (i,dst);
      match wdst with
      | WInt _ => None
      | WCap p b e a =>
          match p with
          | E => None
          | _ =>
              if isWithin a1 a2 b e then
                updatePC i (update_reg φ i dst (WCap p a1 a2 a))
              else None
          end
      end
  | GetA dst r =>
      wr ← (reg φ) !! (i,r);
      match wr with
      | WInt _ => None
      | WCap _ _ _ a => updatePC i (update_reg φ i dst (WInt a))
      end
  | GetB dst r =>
      wr ← (reg φ) !! (i,r);
      match wr with
      | WInt _ => None
      | WCap _ b _ _ => updatePC i (update_reg φ i dst (WInt b))
      end
  | GetE dst r =>
      wr ← (reg φ) !! (i,r);
      match wr with
      | WInt _ => None
      | WCap _ _ e _ => updatePC i (update_reg φ i   dst (WInt e))
      end
  | GetP dst r =>
      wr ← (reg φ) !! (i,r);
      match wr with
      | WInt _ => None
      | WCap p _ _ _ => updatePC i (update_reg φ i   dst (WInt (encodePerm p)))
      end
  | IsPtr dst r =>
      wr ← (reg φ) !! (i,r);
      match wr with
      | WInt _ => updatePC i (update_reg φ i dst (WInt 0%Z))
      | WCap _ _ _ _ => updatePC i (update_reg φ i dst (WInt 1%Z))
      end
  | CAS loc r1 r2 =>
      wloc ← (reg φ) !! (i,loc);
      cond ← (reg φ) !! (i,r1);
      newvalue ← (reg φ) !! (i,r2);
      match wloc with
        | WCap p b e a =>
          oldvalue ← (mem φ) !! a;
          if writeAllowed p && withinBounds b e a
          then
            if (decide (oldvalue = cond))
            then updatePC i (update_reg (update_mem φ a newvalue) i r1 oldvalue)
            else updatePC i (update_reg φ i r1 oldvalue)
          else None
        | WInt _ => None
      end
    end.

  Definition exec (it: instr) (i : CoreN) (φ: ExecConf)
    : CoreConf :=
     match exec_opt it i φ with
     | None => (Failed, φ)
     | Some conf => conf end .

  Lemma exec_opt_exec_some :
    forall φ it i c,
      exec_opt it i φ = Some c →
      exec it i φ = c.
  Proof. unfold exec. by intros * ->. Qed.
  Lemma exec_opt_exec_none :
    forall φ it i,
      exec_opt it i φ = None→
      exec it i φ = (Failed, φ).
  Proof. unfold exec. by intros * ->. Qed.

  (* Per-core step *)
  Inductive core_step : CoreN -> CoreConf -> CoreConf → Prop :=
  | core_step_exec_regfail:
      forall i M,
        (reg M) !! (i ,PC) = None →
        core_step i (Executable, M) (Failed, M)
  | core_step_exec_corrfail:
      forall M wreg i,
        (reg M) !! (i,PC) = Some wreg →
        not (isCorrectPC wreg) →
        core_step i (Executable, M) (Failed, M)
  | core_step_exec_memfail:
      forall M p b e a i,
        (reg M) !! (i,PC) = Some (WCap p b e a) →
        (mem M) !! a = None →
        core_step i (Executable, M) (Failed, M)
  | core_step_exec_instr:
      forall M p b e a it c wa i,
        (reg M) !! (i,PC) = Some (WCap p b e a) →
        (mem M) !! a = Some wa →
        isCorrectPC (WCap p b e a) →
        decodeInstrW wa = it →
        exec it i M = c →
        core_step i (Executable, M) (c.1, c.2).

  Inductive machine_step : Conf -> Conf -> Prop :=
    | conf_step:
      forall i es φ φ' c c',
      es !! i = Some c ->
      core_step i (c, φ) (c', φ') ->
      machine_step (es, φ) (update_state es i c', φ').

  Lemma normal_always_core_step:
    forall M i ,
        exists c M', core_step i (Executable, M) (c, M').
  Proof.
    intros. destruct (reg M !! (i,PC)) as [wpc | ] eqn:Hreg.
    destruct (isCorrectPC_dec wpc) as [Hcorr | ].
    set (Hcorr' := Hcorr).
    inversion Hcorr' as [???? _ _ Hre]. subst wpc.
    destruct (mem M !! a) as [wa | ] eqn:Hmem.
    all: eexists _,_; by econstructor.
  Qed.

  Lemma normal_always_step:
    forall i es φ,
    es !! i = Some Executable ->
    exists es' φ', machine_step (es,φ) (es', φ').
  Proof.
    intros * Hes.
    pose proof (normal_always_core_step φ i) as [c [M' Hstep]].
    eexists _,_.
    econstructor; eassumption.
  Qed.

  Lemma core_step_deterministic:
    forall i c1 c2 c2' σ1 σ2 σ2',
      core_step i (c1, σ1) (c2, σ2) →
      core_step i (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.

  Lemma core_step_exec_inv (r: Reg) p b e a m w instr
    (c: CoreState) (σ: ExecConf) (i: CoreN) :
    r !! (i,PC) = Some (WCap p b e a) →
    isCorrectPC (WCap p b e a) →
    m !! a = Some w →
    decodeInstrW w = instr →
    core_step i (Executable, (r, m)) (c, σ) ->
    exec instr i (r, m) = (c, σ).
  Proof.
    intros HPC Hpc Hm Hinstr. inversion 1; cbn in *.
    1,2,3: congruence.
    simplify_eq. by destruct (exec _ _).
  Qed.

  Lemma core_step_fail_inv wpc c (σ σ': ExecConf) (i : CoreN) :
    reg σ !! (i,PC) = Some wpc →
    ¬ isCorrectPC wpc →
    core_step i (Executable, σ) (c, σ') ->
    c = Failed ∧ σ' = σ.
  Proof.
    intros Hw HPC Hs.
    inv Hs ; subst ; auto.
    congruence.
  Qed.


  Inductive vFlag: Type :=
  | HaltedV: vFlag
  | FailedV: vFlag
  | NextIV: vFlag.

  Definition val := (CoreN * vFlag)%type.

  (* TODO: change to co-inductive list in the Seq case *)
  Inductive pre_expr: Type :=
  | Instr (c : CoreState)
  | Seq (e : pre_expr).
  Definition expr: Type := (CoreN * pre_expr).

  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | (i, HaltedV) => (i, Instr Halted)
    | (i, FailedV) => (i, Instr Failed)
    | (i, NextIV) => (i, Instr NextI)
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | (n, Instr c) =>
      match c with
      | Executable => None
      | Halted => Some (n, HaltedV)
      | Failed => Some (n, FailedV)
      | NextI => Some (n, NextIV)
      end
    | (n, Seq _) => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH. destruct e ; try destruct p; simpl in HH; inv HH; auto.
    destruct c0 ; simpl ; inv H1 ; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v ; destruct v ; reflexivity. Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match e with
    | (n,pe) =>
      match Ki with
      | SeqCtx => (n, Seq pe)
      end
    end.


  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_instr i σ c' σ' :
    core_step i (Executable, σ) (c', σ') ->
    prim_step (i, (Instr Executable)) σ [] (i, (Instr c')) σ' []
  | PS_no_fork_seq i σ :
    prim_step (i, (Seq (Instr NextI))) σ [] (i, (Seq (Instr Executable))) σ []
  | PS_no_fork_halt i σ :
    prim_step (i, (Seq (Instr Halted))) σ [] (i, (Instr Halted)) σ []
  | PS_no_fork_fail i σ :
    prim_step (i, (Seq (Instr Failed))) σ [] (i, (Instr Failed)) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv i σ1 l1 e2 σ2 efs :
    prim_step (i, (Instr Executable)) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = []
    /\ exists (c: CoreState), e2 = (i, Instr c) ∧ core_step i (Executable, σ1) (c, σ2).
  Proof.
    intros Hprim_step.
    inversion Hprim_step ; subst ; split ; eauto.
  Qed.

  Lemma prim_step_and_step_exec i σ1 e2 σ2 l1 e2' σ2' efs :
    core_step i (Executable, σ1) (e2, σ2) →
    prim_step (i, (Instr Executable)) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (i, (Instr e2)) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? ? Hstep' | | |] ; subst.
    generalize (core_step_deterministic i _ _ _ _ _ _ Hstep Hstep').
    intros [-> ->].
    auto.
  Qed.

  Lemma cap_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2.
    all: repeat match goal with HH : core_step _ _ _ |- _ => inv HH end; try congruence.
    all: auto.
    all: try match goal with HH : _ !! _ = _ |- _ => rewrite ->HH in * end.
    all: try simplify_map_eq; auto.
  Qed.


  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct e ; destruct Ki; simplify_option_eq; eauto.
  Qed.

  #[global] Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros x y ?; destruct x,y; simplify_eq; auto with f_equal. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof.
    destruct Ki
    ; inversion 1
    ; destruct e as [? p], p
    ; simplify_option_eq ; eauto.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
  Qed.

  Lemma cap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
  Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Definition is_atomic (e : expr) : Prop :=
    match e with
    | (_, Instr _) => True
    | (_, _) => False
    end.

  Lemma updatePC_some φ i c:
    updatePC i φ = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /updatePC; repeat case_match; try congruence. inversion 1.
    simplify_eq.
    by eexists _.
  Qed.

  Lemma instr_atomic it i φ :
    ∃ φ', (exec it i φ = (Failed, φ') )
          ∨ (exec it i φ = (NextI, φ'))
          ∨ (exec it i φ = (Halted, φ')).
  Proof.
    unfold exec, exec_opt.
    repeat case_match; simplify_eq; eauto;rename H0 into Heqo.
    all: repeat destruct (addr_of_argument (reg φ) i _)
    ; repeat destruct (word_of_argument (reg φ) i _)
    ; repeat destruct (z_of_argument (reg φ) i _)
    ; cbn in *; try by exfalso.
    all: repeat destruct (reg _ !! _); cbn in *; repeat case_match.
    all: repeat destruct (mem _ !! _); cbn in *; repeat case_match.
    all: simplify_eq; try by exfalso.
    all: try apply updatePC_some in Heqo as [φ' Heqo]
    ; simplify_eq
    ; eauto.
Qed.

End opsem.

Canonical Structure cap_ectxi_lang `{CoreParameters} `{MachineParameters} := EctxiLanguage cap_lang_mixin.
Canonical Structure cap_ectx_lang `{CoreParameters} `{MachineParameters} := EctxLanguageOfEctxi cap_ectxi_lang.
Canonical Structure cap_lang `{CoreParameters} `{MachineParameters} := LanguageOfEctx cap_ectx_lang.

#[export] Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

#[export] Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

#[export] Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

Global Instance dec_pc c : Decision (isCorrectPC c).
Proof. apply isCorrectPC_dec. Qed.

(* There is probably a more general instance to be stated there...*)
#[global] Instance Reflexive_ofe_equiv_Word : (Reflexive (ofe_equiv (leibnizO Word))).
Proof. intro; reflexivity. Qed.

(****)

Global Instance is_atomic_correct `{CoreParameters} `{MachineParameters} s (e : expr) : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic, ectx_language_atomic.
  - destruct e.
    + destruct p; rewrite /Atomic; intros ????? Hstep;
        inversion Hstep.
      match goal with HH : core_step _ _ _ |- _ => inversion HH end; eauto.
      destruct (instr_atomic it i σ) as [σstepped [Hst | [Hst | Hst]]];
          simplify_eq; rewrite Hst; simpl; eauto.
      all: try inversion Ha.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x.
    destruct (fill K e') eqn:Heq.
    rewrite Heq in Ha.
    destruct p ; contradiction.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : core.
#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

Lemma head_reducible_from_step `{CoreParameters} `{MachineParameters} i σ1 c2 σ2 :
  core_step i (Executable, σ1) (c2, σ2) →
  @head_reducible cap_ectx_lang  (i, (Instr Executable)) σ1.
Proof. intros * HH. rewrite /head_reducible /head_step //=.
       eexists [], (i, (Instr _)), σ2, [].
       by econstructor.
Qed.

Lemma normal_always_head_reducible `{CoreParameters} `{MachineParameters} σ i :
  @head_reducible cap_ectx_lang  (i, (Instr Executable)) σ.
Proof.
  intros.
  pose proof (normal_always_core_step σ i) as [ es' [σ' Hnorm]].
  eapply head_reducible_from_step; eauto.
Qed.
