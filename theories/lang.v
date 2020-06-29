From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg.

Ltac inv H := inversion H; clear H; subst.

Module cap_lang.

  Inductive Perm: Type :=
  | O
  | RO
  | RW
  | RWL
  | RX
  | E
  | RWX
  | RWLX
  | URW
  | URWL
  | URWX
  | URWLX.

  Definition isU (p: Perm) :=
    match p with
    | URW | URWL | URWX | URWLX => true
    | _ => false
    end.

  Inductive Locality: Type :=
  | Global
  | Local.

  (* None = MemNum bound *)
  Definition Cap: Type :=
    (Perm * Locality) * Addr * Addr * Addr.

  Definition Word := (Z + Cap)%type.

  Definition Reg := gmap RegName Word.

  Definition Mem := gmap Addr Word.

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

  Instance perm_eq_dec : EqDecision Perm.
  Proof. solve_decision. Defined.
  Instance local_eq_dec : EqDecision Locality.
  Proof. solve_decision. Defined.
  Instance cap_eq_dec : EqDecision Cap.
  Proof. solve_decision. Defined.
  Instance word_eq_dec : EqDecision Word.
  Proof. solve_decision. Defined.

  Notation "mem !m! a" := (MemLocate mem a) (at level 20).
  Notation "reg !r! r" := (RegLocate reg r) (at level 20).

  Definition ExecConf := (Reg * Mem)%type.

  Inductive ConfFlag : Type :=
  | Executable
  | Halted
  | Failed
  | NextI.

  Definition Conf: Type := ConfFlag * ExecConf.

  Inductive instr: Type :=
  | Jmp (r: RegName)
  | Jnz (r1 r2: RegName)
  | Mov (dst: RegName) (src: Z + RegName)
  | Load (dst src: RegName)
  | Store (dst: RegName) (src: Z + RegName)
  | Lt (dst: RegName) (r1 r2: Z + RegName)
  | Add (dst: RegName) (r1 r2: Z + RegName)
  | Sub (dst: RegName) (r1 r2: Z + RegName)
  | Lea (dst: RegName) (r: Z + RegName)
  | Restrict (dst: RegName) (r: Z + RegName)
  | Subseg (dst: RegName) (r1 r2: Z + RegName)
  | IsPtr (dst r: RegName)
  | GetL (dst r: RegName)
  | GetP (dst r: RegName)
  | GetB (dst r: RegName)
  | GetE (dst r: RegName)
  | GetA (dst r: RegName)
  | Fail
  | Halt
  (* Load value at src + offs into dst *)
  | LoadU (dst src: RegName) (offs: Z + RegName)
  (* Load value in src to dst + offs *)
  | StoreU (dst: RegName) (offs src: Z + RegName)
  (* Promote the uninitialized capability in dst *)
  | PromoteU (dst: RegName).

  (* Use fundamental theorem of arithmetic/unique prime factorization theorem to define them ? *)
  Axiom decode: Word -> instr.

  Axiom encode: instr -> Word.

  Global Axiom decode_encode_inv:
    forall i, decode (encode i) = i.

  Global Axiom decode_cap_fail:
    forall c, decode (inr c) = Fail.

  Global Axiom encode_decode_not_fail:
    forall w, decode w <> Fail ->
         encode (decode w) = w.

  Axiom encodePerm: Perm -> Z.

  Axiom encodeLoc: Locality -> Z.

  (*Axiom encodePermPair: (Perm * Locality) -> Z.*)

  Axiom decodePermPair: Z -> (Perm * Locality).

  Inductive isCorrectPC: Word -> Prop :=
  | isCorrectPC_intro:
      forall p g (b e a : Addr),
        (b <= a < e)%a ->
        p = RX \/ p = RWX \/ p = RWLX ->
        isCorrectPC (inr ((p, g), b, e, a)).

  Definition reg (ϕ: ExecConf) := fst ϕ.

  Definition mem (ϕ: ExecConf) := snd ϕ.

  Definition pwl p : bool :=
    match p with
    | RWLX | RWL => true
    | _ => false
    end.

  Definition pwlU p : bool :=
    match p with
    | RWLX | RWL | URWLX | URWL => true
    | _ => false
    end.

  Definition executeAllowed (p: Perm): bool :=
    match p with
    | RWX | RWLX | RX | E => true
    | _ => false
    end.

  (* Uninitialized capabilities are neither read nor write allowed *)
  Definition readAllowed (p: Perm): bool :=
    match p with
    | RWX | RWLX | RX | RW | RWL | RO => true
    | _ => false
    end.

  Definition writeAllowed (p: Perm): bool :=
    match p with
    | RWX | RWLX | RW | RWL => true
    | _ => false
    end.

  Lemma writeA_implies_readA p :
    writeAllowed p = true → readAllowed p = true.
  Proof. destruct p; auto. Qed.

  Lemma pwl_implies_RWL_RWLX p :
    pwl p = true → p = RWL ∨ p = RWLX.
  Proof.
    intros. destruct p; try by exfalso.
    by left. by right.
  Qed.

  Lemma isCorrectPC_ra_wb pc_p pc_g pc_b pc_e pc_a :
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a).
  Proof.
    intros. inversion H; subst.
    - destruct H2. apply andb_prop_intro. split.
      + destruct H6,pc_p; inversion H1; try inversion H2; auto; try congruence.
      + apply andb_prop_intro.
        split; apply Is_true_eq_left; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma not_isCorrectPC_perm p g b e a :
    p ≠ RX ∧ p ≠ RWX ∧ p ≠ RWLX → ¬ isCorrectPC (inr ((p,g),b,e,a)).
  Proof.
    intros (Hrx & Hrwx & Hrwlx).
    intros Hvpc. inversion Hvpc;
      destruct H5 as [Hrx' | [Hrwx' | Hrwlx']]; contradiction.
  Qed.

  Lemma not_isCorrectPC_bounds p g b e a :
   ¬ (b <= a < e)%a → ¬ isCorrectPC (inr ((p,g),b,e,a)).
  Proof.
    intros Hbounds.
    intros Hvpc. inversion Hvpc.
    by exfalso.
  Qed.

  Lemma isCorrectPC_bounds p g b e (a0 a1 a2 : Addr) :
    isCorrectPC (inr (p, g, b, e, a0)) →
    isCorrectPC (inr (p, g, b, e, a2)) →
    (a0 ≤ a1 < a2)%Z → isCorrectPC (inr (p, g, b, e, a1)).
  Proof.
    intros Hvpc0 Hvpc2 [Hle Hlt].
    inversion Hvpc0.
    - subst; econstructor; auto.
      inversion Hvpc2; subst.
      + destruct H1 as [Hb He]. destruct H2 as [Hb2 He2]. split.
        { apply Z.le_trans with a0; auto. }
        { apply Z.lt_trans with a2; auto. }
  Qed.

  Lemma isCorrectPC_bounds_alt p g b e (a0 a1 a2 : Addr) :
    isCorrectPC (inr (p, g, b, e, a0))
    → isCorrectPC (inr (p, g, b, e, a2))
    → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
    → isCorrectPC (inr (p, g, b, e, a1)).
  Proof.
    intros Hvpc0 Hvpc2 [Hle0 Hle2].
    apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
    - apply isCorrectPC_bounds with a0 a2; auto.
    - apply z_of_eq in Heq2. rewrite Heq2. auto.
  Qed.

  Definition updatePcPerm (w: Word): Word :=
    match w with
    | inr ((E, g), b, e, a) => inr ((RX, g), b, e, a)
    | _ => w
    end.

  Lemma updatePcPerm_cap_non_E p g b e a :
    p ≠ E →
    updatePcPerm (inr (p, g, b, e, a)) = inr (p, g, b, e, a).
  Proof.
    intros HnE. cbn. destruct p; auto. contradiction.
  Qed.

  Definition nonZero (w: Word): bool :=
    match w with
    | inr _ => true
    | inl n => Zneq_bool n 0
    end.

  Definition withinBounds (c: Cap): bool :=
    match c with
    | (_, b, e, a) => (b <=? a)%a && (a <? e)%a
    end.

  Lemma withinBounds_le_addr p l b e a:
    withinBounds (p, l, b, e, a) = true ->
    (b <= a)%a ∧ (a < e)%a.
  Proof.
    simpl; intros A. eapply andb_true_iff in A.
    unfold le_addr, lt_addr, leb_addr, ltb_addr in *.
    generalize (proj1 (Z.leb_le _ _) (proj1 A)).
    generalize (proj1 (Z.ltb_lt _ _) (proj2 A)).
    lia.
  Qed.

  Lemma isCorrectPC_withinBounds p g p' g' b e a :
    isCorrectPC (inr (p, g, b, e, a)) →
    withinBounds (p', g', b, e, a) = true.
  Proof.
    intros HH. inversion HH; subst.
    rewrite /withinBounds !andb_true_iff Z.leb_le Z.ltb_lt. auto.
  Qed.

  Lemma isWithinBounds_bounds_alt p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma isWithinBounds_bounds_alt' p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 < a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma le_addr_withinBounds p l b e a:
    (b <= a)%a → (a < e)%a →
    withinBounds (p, l, b, e, a) = true .
  Proof.
    intros. eapply andb_true_iff. unfold ltb_addr, leb_addr.
    unfold le_addr, lt_addr in *. rewrite Z.leb_le Z.ltb_lt. lia.
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

  Definition isLocal (l: Locality): bool :=
    match l with
    | Local => true
    | _ => false
    end.

  Definition isLocalWord (w : Word): bool :=
    match w with
    | inl _ => false
    | inr ((_,l),_,_,_) => isLocal l
    end.

  Lemma isLocalWord_cap_isLocal (c0:Cap):
    isLocalWord (inr c0) = true →
    ∃ p g b e a, c0 = (p,g,b,e,a) ∧ isLocal g = true.
  Proof.
    intros. destruct c0, p, p, p.
    cbv in H. destruct l; first by congruence.
    eexists _, _, _, _, _. split; eauto.
  Qed.

  Definition LocalityFlowsTo (l1 l2: Locality): bool :=
    match l1 with
    | Local => true
    | Global => match l2 with
               | Global => true
               | _ => false
               end
    end.

  Definition PermFlowsTo (p1 p2: Perm): bool :=
    match p1 with
    | O => true
    | E => match p2 with
          | E | RX | RWX | RWLX => true
          | _ => false
          end
    | RX => match p2 with
           | RX | RWX | RWLX => true
           | _ => false
           end
    | RWX => match p2 with
            | RWX | RWLX => true
            | _ => false
            end
    | RWLX => match p2 with
             | RWLX => true
             | _ => false
             end
    | RO => match p2 with
           | E | O | URW | URWL | URWX | URWLX => false
           | _ => true
           end
    | RW => match p2 with
           | RW | RWX | RWL | RWLX => true
           | _ => false
           end
    | RWL => match p2 with
            | RWL | RWLX => true
            | _ => false
            end
    | URW => match p2 with
            | URW | URWL | URWX | URWLX | RW | RWX | RWL | RWLX => true
            | _ => false
            end
    | URWL => match p2 with
             | URWL | RWL | RWLX | URWLX => true
             | _ => false
             end
    | URWX => match p2 with
             | URWX | RWX | RWLX | URWLX => true
             | _ => false
             end
    | URWLX => match p2 with
              | URWLX | RWLX => true
              | _ => false
              end
    end.

  (* Sanity check *)
  Lemma PermFlowsToTransitive:
    transitive _ PermFlowsTo.
  Proof.
    red; intros; destruct x; destruct y; destruct z; try congruence; auto.
  Qed.

  (* Sanity check 2 *)
  Lemma PermFlowsToReflexive:
    forall p, PermFlowsTo p p.
  Proof.
    intros; destruct p; auto.
  Qed.

  Definition PermPairFlowsTo (pg1 pg2: Perm * Locality): bool :=
    PermFlowsTo (fst pg1) (fst pg2) && LocalityFlowsTo (snd pg1) (snd pg2).

  Definition isWithin (n1 n2 b e: Addr) : bool :=
    ((b <=? n1) && (n2 <=? e))%a.

  Definition canStore (p: Perm) (w: Word): bool :=
    match w with
    | inl _ => true
    | inr ((_, g), _, _, _) => if isLocal g then
                                 if pwl p then true
                                 else false
                               else true
    end.

  Definition canStoreU (p: Perm) (w: Word): bool :=
    match w with
    | inl _ => true
    | inr ((_, g), _, _, _) => if isLocal g then
                                 if pwlU p then true
                                 else false
                               else true
    end.

  Definition promote_perm (p: Perm): Perm :=
    match p with
    | URW => RW
    | URWL => RWL
    | URWX => RWX
    | URWLX => RWLX
    | _ => p
    end.

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

  Inductive step: Conf -> Conf -> Prop :=
  | step_exec_fail:
      forall φ,
        not (isCorrectPC (RegLocate (reg φ) PC)) ->
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c,
        RegLocate (reg φ) PC = inr ((p, g), b, e, a) ->
        isCorrectPC (RegLocate (reg φ) PC) ->
        decode (MemLocate (mem φ) a) = i ->
        exec i φ = c ->
        step (Executable, φ) (c.1, c.2).

  Lemma isCorrectPC_dec:
    forall w, { isCorrectPC w } + { not (isCorrectPC w) }.
  Proof.
    destruct w.
    - right. red; intros.
      inv H.
    - destruct c as ((((p & g) & b) & e) & a).
      case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      + destruct (Addr_le_dec b a).
        * destruct (Addr_lt_dec a e).
            { left. econstructor; simpl; eauto. split; auto.
              destruct p; simpl in H; try congruence; auto. }
            { right. red; intro. inv H0.
              apply n. destruct H3. exact H1. }
        * right. red; intros; inv H0.
          { destruct e. destruct H3. elim n; eauto. }
      + right. red; intros. inv H0; destruct H7 as [A | [A | A]]; subst p; congruence.
  Qed.

  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros; destruct (isCorrectPC_dec (RegLocate (reg φ) PC)).
    - inversion i; subst; do 2 eexists; eapply step_exec_instr; eauto.
    - exists Failed, φ. constructor 1; eauto.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) ->
      step (c1, σ1) (c2', σ2') ->
      c2 = c2' /\ σ2 = σ2'.
  Proof.
    intros; split; inv H; inv H0; auto; try congruence.
  Qed.

   Lemma regs_lookup_eq (regs: Reg) (r: RegName) (v: Word) :
     regs !! r = Some v ->
     regs !r! r = v.
   Proof. rewrite /RegLocate. intros HH. rewrite HH//. Qed.

   Lemma mem_lookup_eq (m: Mem) (a: Addr) (v: Word) :
     m !! a = Some v ->
     m !m! a = v.
   Proof. rewrite /MemLocate. intros HH. rewrite HH//. Qed.

   Lemma regs_lookup_inr_eq (regs: Reg) (r: RegName) p g b e a :
     regs !r! r = inr ((p, g), b, e, a) ->
     regs !! r = Some (inr ((p, g), b, e, a)).
   Proof. rewrite /RegLocate. intros HH. destruct (regs !! r); first by apply f_equal.  discriminate.
   Qed.

   Lemma mem_lookup_inr_eq (m: Mem) (a: Addr) p g b e i :
     m !m! a = inr ((p, g), b, e, i) ->
     m !! a = Some (inr ((p, g), b, e, i)).
   Proof. rewrite /MemLocate. intros HH. destruct (m !! a); first by apply f_equal.  discriminate.
   Qed.

   Lemma regs_lookup_inl_eq (regs: Reg) (r: RegName) z :
     is_Some (regs !! r) →
     regs !r! r = inl z ->
     regs !! r = Some (inl z).
   Proof. rewrite /RegLocate. intros Hall HH.
          destruct (regs !! r) eqn:HRead; first by apply f_equal.
          destruct Hall as (s & Hsr). rewrite Hsr in HRead; discriminate.
   Qed.

   Lemma step_exec_inv (r: Reg) p g b e a m w instr (c: ConfFlag) (σ: ExecConf) :
     r !! PC = Some (inr ((p, g), b, e, a)) →
     isCorrectPC (inr ((p, g), b, e, a)) →
     m !! a = Some w →
     decode w = instr →
     step (Executable, (r, m)) (c, σ) ->
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
    forall e v, to_val e = Some v ->
           of_val v = e.
  Proof.
    intros. destruct e; try destruct c; simpl in H; inv H; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof.
    destruct v; reflexivity.
  Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | SeqCtx => Seq e
    end.

  Inductive prim_step: expr -> state -> list Empty_set -> expr -> state -> list expr -> Prop :=
  | PS_no_fork_instr σ e' σ' :
      step (Executable, σ) (e', σ') → prim_step (Instr Executable) σ [] (Instr e') σ' []
  | PS_no_fork_seq σ : prim_step (Seq (Instr NextI)) σ [] (Seq (Instr Executable)) σ []
  | PS_no_fork_halt σ : prim_step (Seq (Instr Halted)) σ [] (Instr Halted) σ []
  | PS_no_fork_fail σ : prim_step (Seq (Instr Failed)) σ [] (Instr Failed) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs ->
      to_val e = None.
  Proof.
    intros. inversion H. inversion H0; eauto. by simpl. by simpl. by simpl.
  Qed.

  Lemma prim_step_exec_inv σ1 l1 e2 σ2 efs :
    cap_lang.prim_step (Instr Executable) σ1 l1 e2 σ2 efs ->
    l1 = [] ∧ efs = [] ∧
    exists (c: ConfFlag),
      e2 = Instr c ∧
      cap_lang.step (Executable, σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec σ1 e2 σ2 l1 e2' σ2' efs :
    cap_lang.step (Executable, σ1) (e2, σ2) ->
    cap_lang.prim_step (Instr Executable) σ1 l1 e2' σ2' efs ->
    l1 = [] ∧ e2' = (Instr e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
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
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  Lemma cap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
  Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

End cap_lang.

Canonical Structure cap_ectxi_lang := EctxiLanguage cap_lang.cap_lang_mixin.
Canonical Structure cap_ectx_lang := EctxLanguageOfEctxi cap_ectxi_lang.
Canonical Structure cap_lang := LanguageOfEctx cap_ectx_lang.

Export cap_lang.

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

(* Countable instances *)

Instance perm_countable : Countable Perm.
Proof.
  set encode := fun p => match p with
    | O => 1
    | RO => 2
    | RW => 3
    | RWL => 4
    | RX => 5
    | E => 6
    | RWX => 7
    | RWLX => 8
    | URW => 9
    | URWL => 10
    | URWX => 11
    | URWLX => 12
    end%positive.
  set decode := fun n => match n with
    | 1 => Some O
    | 2 => Some RO
    | 3 => Some RW
    | 4 => Some RWL
    | 5 => Some RX
    | 6 => Some E
    | 7 => Some RWX
    | 8 => Some RWLX
    | 9 => Some URW
    | 10 => Some URWL
    | 11 => Some URWX
    | 12 => Some URWLX
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Qed.

Instance locality_countable : Countable Locality.
Proof.
  set encode := fun l => match l with
    | Local => 1
    | Global => 2
    end%positive.
  set decode := fun n => match n with
    | 1 => Some Local
    | 2 => Some Global
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro l. destruct l; reflexivity.
Qed.

Instance cap_countable : Countable Cap.
Proof.
  (* NB: this relies on the fact that cap_eq_dec has been Defined, because the
  eq decision we have for Cap has to match the one used in the conclusion of the
  lemma... *)
  apply prod_countable.
Qed.

Instance word_countable : Countable Word.
Proof. apply sum_countable. Qed.

(****)

Definition get_addr_pointsto (w : Word) (conf : ExecConf) : option Word :=
  match w with
  | inl z => None
  | inr ((p,g),b,e,a) => Some (MemLocate (mem conf) a)
  end.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Instr _ => True
  | _ => False
  end.

Ltac flatten :=
  repeat match goal with
         | |- context [ if ?b then ?X else ?Y ] => destruct b
         | |- context [ match ?t with _ => _ end ] => destruct t
         end.

Lemma updatePC_atomic φ :
  ∃ φ', updatePC φ = (Failed,φ') ∨ (updatePC φ = (NextI,φ')) ∨
        (updatePC φ = (Halted,φ')).
Proof.
  rewrite /updatePC; flatten; eauto.
Qed.

Lemma instr_atomic i φ :
  ∃ φ', (exec i φ = (Failed, φ')) ∨ (exec i φ = (NextI, φ')) ∨
        (exec i φ = (Halted, φ')).
Proof.
  unfold exec; flatten; eauto; try (eapply updatePC_atomic; eauto).
Qed.

Global Instance is_atomic_correct s (e : expr) : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic, ectx_language_atomic.
  - destruct e.
    + destruct c; rewrite /Atomic; intros ????? Hstep;
        inversion Hstep. inversion H; eauto.
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

Lemma head_reducible_from_step σ1 e2 σ2 :
  step (Executable, σ1) (e2, σ2) ->
  head_reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /head_reducible /head_step //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_head_reducible σ :
  head_reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply head_reducible_from_step. eauto.
Qed.

(* Destruct pairs & capabilities *)

Ltac destruct_pair_l c n :=
  match eval compute in n with
  | 0 => idtac
  | _ => let sndn := fresh c in
        destruct c as (c,sndn); destruct_pair_l c (pred n)
  end.

Ltac destruct_cap c :=
  destruct_pair_l c 4.
