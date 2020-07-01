From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg machine_base machine_parameters.
Set Warnings "-redundant-canonical-projection".

Ltac inv H := inversion H; clear H; subst.

Definition RegLocate (reg : Reg) (r : RegName) :=
  match (reg !! r) with
  | Some w => w
  | None => inl 0%Z
  end.

Definition MemLocate (mem : Mem) (a : Addr) :=
  match (mem !! a) with
  | Some w => w
  | None => inl 0%Z
  end.

Notation "mem !m! a" := (MemLocate mem a) (at level 20).
Notation "reg !r! r" := (RegLocate reg r) (at level 20).

Definition ExecConf := (Reg * Mem)%type.

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition reg (ϕ: ExecConf) := fst ϕ.

Definition mem (ϕ: ExecConf) := snd ϕ.

Lemma regs_lookup_eq (regs: Reg) (r: RegName) (v: Word) :
  regs !! r = Some v →
  regs !r! r = v.
Proof. rewrite /RegLocate. intros HH. rewrite HH//. Qed.

Lemma mem_lookup_eq (m: Mem) (a: Addr) (v: Word) :
  m !! a = Some v →
  m !m! a = v.
Proof. rewrite /MemLocate. intros HH. rewrite HH//. Qed.

Lemma regs_lookup_inr_eq (regs: Reg) (r: RegName) p g b e a :
  regs !r! r = inr ((p, g), b, e, a) →
  regs !! r = Some (inr ((p, g), b, e, a)).
Proof. rewrite /RegLocate. intros HH. destruct (regs !! r); first by apply f_equal.  discriminate.
Qed.

Lemma mem_lookup_inr_eq (m: Mem) (a: Addr) p g b e i :
  m !m! a = inr ((p, g), b, e, i) →
  m !! a = Some (inr ((p, g), b, e, i)).
Proof. rewrite /MemLocate. intros HH. destruct (m !! a); first by apply f_equal.  discriminate.
Qed.

Lemma regs_lookup_inl_eq (regs: Reg) (r: RegName) z :
  is_Some (regs !! r) →
  regs !r! r = inl z →
  regs !! r = Some (inl z).
Proof. rewrite /RegLocate. intros Hall HH.
       destruct (regs !! r) eqn:HRead; first by apply f_equal.
       destruct Hall as (s & Hsr). rewrite Hsr in HRead; discriminate.
Qed.

Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf := (<[r:=w]>(reg φ),mem φ).
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf := (reg φ, <[a:=w]>(mem φ)).

Definition updatePC (φ: ExecConf): Conf :=
  match RegLocate (reg φ) PC with
  | inr ((p, g), b, e, a) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ PC (inr ((p, g), b, e, a'))) in
                 (NextI, φ')
    | None => (Failed, φ)
    end
  | _ => (Failed, φ)
  end.

Definition isWithin (n1 n2 b e: Addr) : bool :=
  ((b <=? n1) && (n2 <=? e))%a.

Inductive access_kind: Type :=
| LoadU_access (b e a: Addr) (offs: Z): access_kind
| StoreU_access (b e a: Addr) (offs: Z): access_kind.

Definition verify_access (a: access_kind): option Addr :=
  match a with
  | LoadU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_lt_dec a' a then
                    if Addr_le_dec a e then
                      Some a' else None else None else None
    end
  | StoreU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_le_dec a' a then
                    if Addr_lt_dec a e then
                      Some a' else None else None else None
    end
  end.

Lemma verify_access_spec:
  forall a a',
    (verify_access a = Some a') <->
    (match a with
     | LoadU_access b e a offs =>
       (a + offs)%a = Some a' /\ (b <= a')%a /\ (a' < a)%a /\ (a <= e)%a
     | StoreU_access b e a offs =>
       (a + offs)%a = Some a' /\ (b <= a')%a /\ (a' <= a)%a /\ (a < e)%a
     end).
Proof.
  intros; split; intros.
  - destruct a; simpl in H; destruct (a + offs)%a as [a1|] eqn:Ha; intros; try congruence;
    repeat match goal with
           | H: context [if ?t then _ else _] |- _ => destruct t
           end; inv H; auto.
  - destruct a; destruct H as [Ha [A [B C]]]; simpl; rewrite Ha;
    repeat match goal with
           | |- context [if ?t then _ else _] => destruct t
           end; tauto.
Qed.

(*--- z_of_argument ---*)

Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! r with
    | Some (inl z) => Some z
    | _ => None
    end
  end.

Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z) ∧ regs' !! r = Some (inl z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Section opsem.
  Context `{MachineParameters}.

  Definition exec (i: instr) (φ: ExecConf): Conf :=
    match i with
    | Fail => (Failed, φ)
    | Halt => (Halted, φ)
    | Jmp r => let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r))) in (NextI, φ')
    | Jnz r1 r2 =>
      if nonZero (RegLocate (reg φ) r2) then
        let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r1))) in (NextI, φ')
      else updatePC φ
    | Load dst src =>
      match RegLocate (reg φ) src with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        (* Fails for U cap *)
        if readAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_reg φ dst (MemLocate (mem φ) a))
        else (Failed, φ)
      end
    | Store dst (inr src) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) && canStore p (RegLocate (reg φ) src) then
          updatePC (update_mem φ a (RegLocate (reg φ) src))
        else (Failed, φ)
      end
    | Store dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_mem φ a (inl n)) else (Failed, φ)
      end
    | Mov dst (inl n) => updatePC (update_reg φ dst (inl n))
    | Mov dst (inr src) => updatePC (update_reg φ dst (RegLocate (reg φ) src))
    | Lea dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match (a + n)%a with
                                      | Some a' => if Addr_le_dec a' a then
                                                    let c := ((p, g), b, e, a') in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                      | None => (Failed, φ)
                                      end
        | _ => match (a + n)%a with
               | Some a' => let c := ((p, g), b, e, a') in
                            updatePC (update_reg φ dst (inr c))
               | None => (Failed, φ)
               end
        end
      end
    | Lea dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match RegLocate (reg φ) r with
                                      | inr _ => (Failed, φ)
                                      | inl n => match (a + n)%a with
                                                | Some a' =>
                                                  if Addr_le_dec a' a then
                                                    let c := ((p, g), b, e, a') in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                                | None => (Failed, φ)
                                                end
                   end
        | _ => match RegLocate (reg φ) r with
              | inr _ => (Failed, φ)
              | inl n => match (a + n)%a with
                         | Some a' =>
                           let c := ((p, g), b, e, a') in
                           updatePC (update_reg φ dst (inr c))
                         | None => (Failed, φ)
                         end
              end
        end
      end
    | Restrict dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (permPair, b, e, a) =>
        match permPair with
        | (E, _) => (Failed, φ)
        | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                updatePC (update_reg φ dst (inr (decodePermPair n, b, e, a)))
              else (Failed, φ)
        end
      end
    | Restrict dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (permPair, b, e, a) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          match permPair with
          | (E, _) => (Failed, φ)
          | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                  updatePC (update_reg φ dst (inr (decodePermPair n, b, e, a)))
                else (Failed, φ)
          end
        end
      end
    | Add dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
                 end
      end
    | Add dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 + n2)%Z))
    | Sub dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
                 end
      end
    | Sub dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 - n2)%Z))
    | Lt dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
                 end
      end
    | Lt dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
    | Subseg dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match RegLocate (reg φ) r2 with
            | inr _ => (Failed, φ)
            | inl n2 =>
              match z_to_addr n1, z_to_addr n2 with
              | Some a1, Some a2 =>
                if isWithin a1 a2 b e then
                  updatePC (update_reg φ dst (inr ((p, g), a1, a2, a)))
                else (Failed, φ)
              | _,_ => (Failed, φ)
              end
            end
          end
        end
      end
    | Subseg dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r2 with
          | inr _ => (Failed, φ)
          | inl n2 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr ((p, g), a1, a2, a)))
                     else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr ((p, g), a1, a2, a)))
              else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inl n1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match z_to_addr n1, z_to_addr n2 with
          | Some a1, Some a2 =>
            if isWithin a1 a2 b e then
              updatePC (update_reg φ dst (inr ((p, g), a1, a2, a)))
            else (Failed, φ)
          | _,_ => (Failed, φ)
          end
        end
      end
    | GetA dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (_, _, _, a) =>
        match a with
        | A a' _ _ => updatePC (update_reg φ dst (inl a'))
        end
      end
    | GetB dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (_, b, _, _) =>
        match b with
        | A b' _ _ => updatePC (update_reg φ dst (inl b'))
        end
      end
    | GetE dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (_, _, e, _) =>
        match e with
        | A e' _ _ => updatePC (update_reg φ dst (inl e'))
        end
      end
    | GetP dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr ((p, _), _, _, _) => updatePC (update_reg φ dst (inl (encodePerm p)))
      end
    | GetL dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr ((_, g), _, _, _) => updatePC (update_reg φ dst (inl (encodeLoc g)))
      end
    | IsPtr dst r =>
      match RegLocate (reg φ) r with
      | inl _ => updatePC (update_reg φ dst (inl 0%Z))
      | inr _ => updatePC (update_reg φ dst (inl 1%Z))
      end
    | LoadU rdst rsrc offs =>
      match RegLocate (reg φ) rsrc with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        if isU p then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (LoadU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => updatePC (update_reg φ rdst (MemLocate (mem φ) a'))
                         end
          end
        else (Failed, φ)
      end
    | StoreU dst offs src =>
      let w := match src with
               | inl n => inl n
               | inr rsrc => (RegLocate (reg φ) rsrc)
               end in
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        if isU p && canStoreU p w then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (StoreU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => if addr_eq_dec a a' then
                                       match (a + 1)%a with
                                       | Some a => updatePC (update_reg (update_mem φ a' w) dst (inr ((p, g), b, e, a)))
                                       | None => (Failed, φ)
                                       end
                                     else updatePC (update_mem φ a' w)
                         end
          end
        else (Failed, φ)
      end
    | PromoteU dst =>
      match RegLocate (reg φ) dst with
      | inr ((p, g), b, e, a) =>
        if perm_eq_dec p E then (Failed, φ)
        else updatePC (update_reg φ dst (inr ((promote_perm p, g), b, min a e, a)))
      | inl _ => (Failed, φ)
      end
    end.

  Inductive step: Conf → Conf → Prop :=
  | step_exec_fail:
      forall φ,
        not (isCorrectPC ((reg φ) !r! PC)) →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c,
        RegLocate (reg φ) PC = inr ((p, g), b, e, a) →
        isCorrectPC ((reg φ) !r! PC) →
        decodeInstrW ((mem φ) !m! a) = i →
        exec i φ = c →
        step (Executable, φ) (c.1, c.2).

  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros; destruct (isCorrectPC_dec (RegLocate (reg φ) PC)).
    - inversion i; subst; do 2 eexists; eapply step_exec_instr; eauto.
    - exists Failed, φ. constructor 1; eauto.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.

  Lemma step_exec_inv (r: Reg) p g b e a m w instr (c: ConfFlag) (σ: ExecConf) :
    r !! PC = Some (inr ((p, g), b, e, a)) →
    isCorrectPC (inr ((p, g), b, e, a)) →
    m !! a = Some w →
    decodeInstrW w = instr →
    step (Executable, (r, m)) (c, σ) →
    exec instr (r, m) = (c, σ).
  Proof.
    intros HPC Hpc Hm Hinstr. inversion 1.
    { exfalso. erewrite regs_lookup_eq in *; eauto. }
    erewrite regs_lookup_eq in *; eauto.
    match goal with H: inr _ = inr _ |- _ => inversion H; clear H end.
    cbn in *.
    match goal with H: exec ?i _ = ?k |- _ => destruct k; subst i end. cbn.
    subst.
    match goal with H: m !! _ = Some w |- _ =>
                    erewrite (mem_lookup_eq _ _ _ H) in * end. eauto.
  Qed.

  Lemma step_fail_inv (r: Reg) c (σ σ': ExecConf) :
    ¬ isCorrectPC (reg σ !r! PC) →
    step (Executable, σ) (c, σ') →
    c = Failed ∧ σ' = σ.
  Proof.
    intros HPC Hs. inversion Hs; subst; auto. done.
  Qed.

  Inductive val: Type :=
  | HaltedV: val
  | FailedV: val
  | NextIV: val.

  (* TODO: change to co-inductive list in the Seq case *)
  Inductive expr: Type :=
  | Instr (c : ConfFlag)
  | Seq (e : expr).
  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => Instr Halted
    | FailedV => Instr Failed
    | NextIV => Instr NextI
    end.

  Fixpoint to_val (e: expr): option val :=
    match e with
    | Instr c =>
      match c with
      | Executable => None
      | Halted => Some HaltedV
      | Failed => Some FailedV
      | NextI => Some NextIV
      end
    | Seq _ => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH. destruct e; try destruct c; simpl in HH; inv HH; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v; reflexivity. Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | SeqCtx => Seq e
    end.

  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_instr σ e' σ' :
      step (Executable, σ) (e', σ') → prim_step (Instr Executable) σ [] (Instr e') σ' []
  | PS_no_fork_seq σ : prim_step (Seq (Instr NextI)) σ [] (Seq (Instr Executable)) σ []
  | PS_no_fork_halt σ : prim_step (Seq (Instr Halted)) σ [] (Instr Halted) σ []
  | PS_no_fork_fail σ : prim_step (Seq (Instr Failed)) σ [] (Instr Failed) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv σ1 l1 e2 σ2 efs :
    prim_step (Instr Executable) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = [] ∧
    exists (c: ConfFlag),
      e2 = Instr c ∧
      step (Executable, σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec σ1 e2 σ2 l1 e2' σ2' efs :
    step (Executable, σ1) (e2, σ2) →
    prim_step (Instr Executable) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (Instr e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
  Qed.

  Lemma cap_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2.
    all: repeat match goal with HH : step _ _ |- _ => inv HH end; try congruence.
    all: auto.
    match goal with HH : _ !r! _ = _ |- _ => rewrite ->HH in * end.
    simplify_map_eq. auto.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

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
    | Instr _ => True
    | _ => False
    end.

  Lemma updatePC_atomic φ :
    ∃ φ', updatePC φ = (Failed,φ') ∨ (updatePC φ = (NextI,φ')) ∨
          (updatePC φ = (Halted,φ')).
  Proof.
    rewrite /updatePC; repeat case_match; eauto.
  Qed.

  Lemma instr_atomic i φ :
    ∃ φ', (exec i φ = (Failed, φ')) ∨ (exec i φ = (NextI, φ')) ∨
          (exec i φ = (Halted, φ')).
  Proof.
    unfold exec; repeat case_match; eauto; try (eapply updatePC_atomic; eauto).
  Qed.

End opsem.

Canonical Structure cap_ectxi_lang `{MachineParameters} := EctxiLanguage cap_lang_mixin.
Canonical Structure cap_ectx_lang `{MachineParameters} := EctxLanguageOfEctxi cap_ectxi_lang.
Canonical Structure cap_lang `{MachineParameters} := LanguageOfEctx cap_ectx_lang.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible.
Local Hint Resolve to_of_val.
Local Hint Unfold language.irreducible.

Global Instance dec_pc c : Decision (isCorrectPC c).
Proof. apply isCorrectPC_dec. Qed.

(* There is probably a more general instance to be stated there...*)
Instance Reflexive_ofe_equiv_Word : (Reflexive (ofe_equiv (leibnizO Word))).
Proof. intro; reflexivity. Qed.

(****)

Definition get_addr_pointsto (w : Word) (conf : ExecConf) : option Word :=
  match w with
  | inl z => None
  | inr ((p,g),b,e,a) => Some (MemLocate (mem conf) a)
  end.

Global Instance is_atomic_correct `{MachineParameters} s (e : expr) : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic, ectx_language_atomic.
  - destruct e.
    + destruct c; rewrite /Atomic; intros ????? Hstep;
        inversion Hstep.
      match goal with HH : step _ _ |- _ => inversion HH end; eauto.
      destruct (instr_atomic i σ) as [σstepped [Hst | [Hst | Hst]]];
          simplify_eq; rewrite Hst; simpl; eauto.
    + inversion Ha.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Hint Extern 0 (Atomic _ _) => solve_atomic.
Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

Lemma head_reducible_from_step `{MachineParameters} σ1 e2 σ2 :
  step (Executable, σ1) (e2, σ2) →
  head_reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /head_reducible /head_step //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_head_reducible `{MachineParameters} σ :
  head_reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply head_reducible_from_step. eauto.
Qed.

