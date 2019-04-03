From iris.algebra Require Export base.
From iris.base_logic Require Import upred.
From iris.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants.

From iris.program_logic Require Export language.

From stdpp Require Import gmap fin_maps.

Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)

Ltac inv H := inversion H; clear H; subst.

Module cap_lang.

  Definition RegNum: nat := 31.

  (*Hypothesis RegNum_not_zero: RegNum > O.*)

  Definition Addr: Type := Z.

  Definition addr_eq_dec: forall (x y: Addr), {x = y} + {x <> y} := Z_eq_dec.

  Inductive Perm: Type :=
  | O
  | RO
  | RW
  | RWL
  | RX
  | E
  | RWX
  | RWLX.

  Inductive Locality: Type :=
  | Global
  | Local.

  (* None = infinity bound *)
  Definition Cap: Type :=
    (Perm * Locality) * Addr * option Addr * Addr.

  Definition Word := (Z + Cap)%type.

  Inductive RegName: Type :=
  | PC
  | R (n: nat) (fin: n <=? RegNum = true).

  Definition reg_eq_dec:
    forall (r1 r2: RegName), { r1 = r2 } + { r1 <> r2 }.
  Proof.
    intros. destruct r1; destruct r2.
    - left. reflexivity.
    - right. discriminate.
    - right. discriminate.
    - destruct (nat_eq_dec n n0).
      + subst n0. left.
        assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
        { intros. apply eq_proofs_unicity.
          intros; destruct x; destruct y; auto. }
        rewrite (H _ _ _ fin fin0). reflexivity.
      + right. congruence.
  Qed.

  Definition Reg := RegName -> Word.

  Definition Mem := Addr -> Word.

  Definition ExecConf := (Reg * Mem)%type.

  Definition MemSeg := Addr -> option Word.

  Definition disjoint_memseg: Disjoint MemSeg := fun ms1 ms2 => forall a w1 w2, ms1 a = Some w1 -> ms2 a = Some w2 -> False.

  Definition union_memseg (ms1 ms2: MemSeg): MemSeg :=
    fun a => match ms1 a with
          | Some w1 => Some w1
          | None => match ms2 a with
                   | Some w2 => Some w2
                   | None => None
                   end
          end.

  Definition coerce_memseg_to_mem (ms: MemSeg) (H: forall a, ms a <> None): Mem :=
    fun a => match ms a as o return (ms a = o → Word) with
          | Some w => λ _ : ms a = Some w, w
          | None => λ H0 : ms a = None, False_rect Word (H a H0)
          end eq_refl.

  Inductive Conf: Type :=
  | Normal (ϕ: ExecConf)
  | Halted (m: Mem)
  | Failed.

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
  | Halt.

  (* Use fundamental theorem of arithmetic/unique prime factorization theorem to define them ? *)
  Axiom decode: Word -> instr.

  Axiom encode: instr -> Word.

  Hypothesis decode_encode_inv:
    forall i, decode (encode i) = i.

  Hypothesis decode_cap_fail:
    forall c, decode (inr c) = Fail.

  Hypothesis encode_decode_not_fail:
    forall w, decode w <> Fail ->
         encode (decode w) = w.

  Axiom encodePerm: Perm -> Z.

  Axiom encodeLoc: Locality -> Z.

  (*Axiom encodePermPair: (Perm * Locality) -> Z.*)

  Axiom decodePermPair: Z -> (Perm * Locality).

  Inductive isCorrectPC: Word -> Prop :=
  | isCorrectPC_intro:
      forall p g b e a,
        (b <= a < e)%Z ->
        p = RX \/ p = RWX \/ p = RWLX ->
        isCorrectPC (inr ((p, g), b, (Some e), a))
  | isCorrectPC_intro_infinity:
      forall p g b a,
        (b <= a)%Z ->
        p = RX \/ p = RWX \/ p = RWLX ->
        isCorrectPC (inr ((p, g), b, None, a)).

  Definition reg (ϕ: ExecConf) := fst ϕ.

  Definition mem (ϕ: ExecConf) := snd ϕ.

  Definition executeAllowed (p: Perm): bool :=
    match p with
    | RWX | RWLX | RX | E => true
    | _ => false
    end.

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

  Definition updatePcPerm (w: Word): Word :=
    match w with
    | inr ((E, g), b, e, a) => inr ((RX, g), b, e, a)
    | _ => w
    end.

  Definition nonZero (w: Word): bool :=
    match w with
    | inr _ => true
    | inl n => Zneq_bool n 0
    end.

  Definition withinBounds (c: Cap): bool :=
    match c with
    | (_, b, e, a) =>
      match e with
      | None => Z.leb b a
      | Some e => Z.leb b a && Z.leb a e
      end
    end.

  Definition update_reg (ϕ: ExecConf) (r: RegName) (w: Word): ExecConf :=
    (fun x => if reg_eq_dec x r then w else reg ϕ x , mem ϕ).

  Definition update_mem (ϕ: ExecConf) (a: Addr) (w: Word): ExecConf :=
    (reg ϕ, fun x => if addr_eq_dec x a then w else mem ϕ x).

  Definition updatePC (ϕ: ExecConf): Conf :=
    match reg ϕ PC with
    | inr ((p, g), b, e, a) =>
      Normal (update_reg ϕ PC (inr ((p, g), b, e, (a + 1)%Z)))
    | _ => Failed
    end.

  Definition isLocal (l: Locality): bool :=
    match l with
    | Local => true
    | _ => false
    end.

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
           | E | O => false
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
    end.

  Definition PermPairFlowsTo (pg1 pg2: Perm * Locality): bool :=
    PermFlowsTo (fst pg1) (fst pg2) && LocalityFlowsTo (snd pg1) (snd pg2).

  Definition isWithin (n1 n2 b: Z) (e: option Z): bool :=
    match e with
    | None => Z.leb 0 b && Z.leb b n1 && (Z.leb 0 n2 || (Z.eqb n2 (-42)))
    | Some e => Z.leb 0 b && Z.leb b n1 && Z.leb 0 n2 && Z.leb n2 e
    end.

  Definition exec (i: instr) (ϕ: ExecConf): Conf :=
    match i with
    | Fail => Failed
    | Halt => Halted (mem ϕ)
    | Jmp r => Normal (update_reg ϕ PC (updatePcPerm (reg ϕ r)))
    | Jnz r1 r2 =>
      if nonZero (reg ϕ r2) then
        Normal (update_reg ϕ PC (updatePcPerm (reg ϕ r1)))
      else updatePC ϕ
    | Load dst src =>
      match reg ϕ src with
      | inl n => Failed
      | inr ((p, g), b, e, a) =>
        if readAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_reg ϕ dst (mem ϕ a))
        else Failed
      end
    | Store dst (inr src) =>
      match reg ϕ dst with
      | inl n => Failed
      | inr ((p, g), b, e, a) =>
        if writeAllowed p && withinBounds ((p, g), b, e, a) then
          match reg ϕ src with
          | inl n => updatePC (update_mem ϕ a (reg ϕ src))
          | inr ((_, g'), _, _, _) => if isLocal g' then
                                       match p with
                                       | RWLX | RWL => updatePC (update_mem ϕ a (reg ϕ src))
                                       | _ => Failed
                                       end
                                     else updatePC (update_mem ϕ a (reg ϕ src))
          end
        else Failed
      end
    | Store dst (inl n) =>
      match reg ϕ dst with
      | inl n => Failed
      | inr ((p, g), b, e, a) =>
        if writeAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_mem ϕ a (inl n)) else Failed
      end
    | Mov dst (inl n) => updatePC (update_reg ϕ dst (inl n))
    | Mov dst (inr src) => updatePC (update_reg ϕ dst (reg ϕ src))
    | Lea dst (inl n) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ => let c := ((p, g), b, e, (a + n)%Z) in
              updatePC (update_reg ϕ dst (inr c))
        end
      end
    | Lea dst (inr r) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ => match reg ϕ r with
              | inr _ => Failed
              | inl n =>
                let c := ((p, g), b, e, (a + n)%Z) in
                updatePC (update_reg ϕ dst (inr c))
              end
        end
      end
    | Restrict dst (inl n) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr (permPair, b, e, a) =>
        if PermPairFlowsTo (decodePermPair n) permPair then
          updatePC (update_reg ϕ dst (inr (decodePermPair n, b, e, a)))
        else Failed
      end
    | Restrict dst (inr r) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr (permPair, b, e, a) =>
        match reg ϕ r with
        | inr _ => Failed
        | inl n =>
          if PermPairFlowsTo (decodePermPair n) permPair then
            updatePC (update_reg ϕ dst (inr (decodePermPair n, b, e, a)))
          else Failed
        end
      end
    | Add dst (inr r1) (inr r2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => match reg ϕ r2 with
                 | inr _ => Failed
                 | inl n2 => updatePC (update_reg ϕ dst (inl (n1 + n2)%Z))
                 end
      end
    | Add dst (inl n1) (inr r2) =>
      match reg ϕ r2 with
      | inr _ => Failed
      | inl n2 => updatePC (update_reg ϕ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inr r1) (inl n2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => updatePC (update_reg ϕ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inl n1) (inl n2) =>
      updatePC (update_reg ϕ dst (inl (n1 + n2)%Z))
    | Sub dst (inr r1) (inr r2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => match reg ϕ r2 with
                 | inr _ => Failed
                 | inl n2 => updatePC (update_reg ϕ dst (inl (n1 - n2)%Z))
                 end
      end
    | Sub dst (inl n1) (inr r2) =>
      match reg ϕ r2 with
      | inr _ => Failed
      | inl n2 => updatePC (update_reg ϕ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inr r1) (inl n2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => updatePC (update_reg ϕ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inl n1) (inl n2) =>
      updatePC (update_reg ϕ dst (inl (n1 - n2)%Z))
    | Lt dst (inr r1) (inr r2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => match reg ϕ r2 with
                 | inr _ => Failed
                 | inl n2 => updatePC (update_reg ϕ dst (inl (Z.b2z (Z.ltb n1 n2))))
                 end
      end
    | Lt dst (inl n1) (inr r2) =>
      match reg ϕ r2 with
      | inr _ => Failed
      | inl n2 => updatePC (update_reg ϕ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inr r1) (inl n2) =>
      match reg ϕ r1 with
      | inr _ => Failed
      | inl n1 => updatePC (update_reg ϕ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inl n1) (inl n2) =>
      updatePC (update_reg ϕ dst (inl (Z.b2z (Z.ltb n1 n2))))
    | Subseg dst (inr r1) (inr r2) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ =>
          match reg ϕ r1 with
          | inr _ => Failed
          | inl n1 =>
            match reg ϕ r2 with
            | inr _ => Failed
            | inl n2 => if isWithin n1 n2 b e then 
                         updatePC (update_reg ϕ dst (inr ((p, g), n1, if Z.eqb n2 (-42)%Z then None else Some n2, a)))
                       else Failed
            end
          end
        end
      end
    | Subseg dst (inl n1) (inr r2) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ =>
          match reg ϕ r2 with
          | inr _ => Failed
          | inl n2 => if isWithin n1 n2 b e then 
                       updatePC (update_reg ϕ dst (inr ((p, g), n1, if Z.eqb n2 (-42)%Z then None else Some n2, a)))
                     else Failed
          end
        end
      end
    | Subseg dst (inr r1) (inl n2) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ =>
          match reg ϕ r1 with
          | inr _ => Failed
          | inl n1 =>
            if isWithin n1 n2 b e then 
              updatePC (update_reg ϕ dst (inr ((p, g), n1, if Z.eqb n2 (-42)%Z then None else Some n2, a)))
            else Failed
          end
        end
      end
    | Subseg dst (inl n1) (inl n2) =>
      match reg ϕ dst with
      | inl _ => Failed
      | inr ((p, g), b, e, a) =>
        match p with
        | E => Failed
        | _ =>
          if isWithin n1 n2 b e then 
            updatePC (update_reg ϕ dst (inr ((p, g), n1, if Z.eqb n2 (-42)%Z then None else Some n2, a)))
          else Failed
        end
      end
    | GetA dst r =>
      match reg ϕ r with
      | inl _ => Failed
      | inr (_, _, _, a) => updatePC (update_reg ϕ dst (inl a))
      end
    | GetB dst r =>
      match reg ϕ r with
      | inl _ => Failed
      | inr (_, b, _, _) => updatePC (update_reg ϕ dst (inl b))
      end
    | GetE dst r =>
      match reg ϕ r with
      | inl _ => Failed
      | inr (_, _, e, _) =>
        match e with
        | None => updatePC (update_reg ϕ dst (inl (-42)%Z))
        | Some e => updatePC (update_reg ϕ dst (inl e))
        end
      end
    | GetP dst r =>
      match reg ϕ r with
      | inl _ => Failed
      | inr ((p, _), _, _, _) => updatePC (update_reg ϕ dst (inl (encodePerm p)))
      end
    | GetL dst r =>
      match reg ϕ r with
      | inl _ => Failed
      | inr ((_, g), _, _, _) => updatePC (update_reg ϕ dst (inl (encodeLoc g)))
      end
    | IsPtr dst r =>
      match reg ϕ r with
      | inl _ => updatePC (update_reg ϕ dst (inl 0%Z))
      | inr _ => updatePC (update_reg ϕ dst (inl 1%Z))
      end
    end.

  Inductive step: Conf -> Conf -> Prop :=
  | step_exec_fail:
      forall ϕ,
        not (isCorrectPC (reg ϕ PC)) ->
        step (Normal ϕ) Failed
  | step_exec_instr:
      forall ϕ p g b e a i c,
        reg ϕ PC = inr ((p, g), b, e, a) ->
        isCorrectPC (reg ϕ PC) ->
        decode (mem ϕ a) = i ->
        exec i ϕ = c ->
        step (Normal ϕ) c.

  Lemma isCorrectPC_dec:
    forall w, { isCorrectPC w } + { not (isCorrectPC w) }. 
  Proof.
    destruct w.
    - right. red; intros.
      inv H.
    - destruct c as ((((p & g) & b) & e) & a).
      case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      + destruct (Z_le_dec b a).
        * destruct e.
          { destruct (Z_lt_dec a a0).
            - left. econstructor; eauto.
              destruct p; simpl in H; try congruence; auto.
            - right. red; intros. inv H0.
              destruct H3. congruence. }
          { left. econstructor; eauto.
            destruct p; simpl in H; try congruence; auto. }
        * right. red; intros; inv H0.
          { destruct H3. elim n; eauto. }
          { elim n; auto. }
      + right. red; intros. inv H0; destruct H7 as [A | [A | A]]; subst p; congruence.
  Qed.

  Lemma normal_always_step:
    forall ϕ, exists c, step (Normal ϕ) c.
  Proof.
    intros; destruct (isCorrectPC_dec (reg ϕ PC)).
    - inversion i; subst; eexists; eapply step_exec_instr; eauto.
    - exists Failed. constructor 1; eauto.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2',
      step c1 c2 ->
      step c1 c2' ->
      c2 = c2'.
  Proof.
    intros; inv H; inv H0; auto; try congruence.
  Qed.

  (* Actually nsteps from stdpp *)
  Inductive starN {A: Type} (step: A -> A -> Prop): nat -> A -> A -> Prop :=
  | starN_refl:
      forall (s: A), starN step 0 s s
  | starN_step:
      forall n s1 s2 s3,
        step s1 s2 ->
        starN step n s2 s3 ->
        starN step (S n) s1 s3.

  Lemma starN_step_deterministic:
    forall n c1 c2 c2',
      starN step n c1 c2 ->
      starN step n c1 c2' ->
      c2 = c2'.
  Proof.
    induction 1; intros.
    - inv H; auto.
    - inv H1. generalize (step_deterministic _ _ _ H H3).
      intros; subst s4. eapply IHstarN; eauto.
  Qed.

  Lemma starN_halted:
    forall n c m,
      starN step n c (Halted m) ->
      forall n' c', starN step n' c c' ->
               (n' <= n)%nat /\ starN step (n - n')%nat c' (Halted m).
  Proof.
    induction n; intros.
    - inv H0.
      + split; auto.
      + inv H. inv H1.
    - inv H. inv H0.
      + split; try lia.
        econstructor; eauto.
      + assert (s0 = s2) by (eapply step_deterministic; eauto); subst s0.
      generalize (IHn _ _ H3 _ _ H1).
      intros [A B]. split; try omega.
      replace (S n - S n0) with (n - n0) by omega.
      assumption.
  Qed.

  Inductive val: Type :=
  | HaltedV: Mem -> val
  | FailedV: val.

  Definition expr := Conf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV m => Halted m
    | FailedV => Failed
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | Normal _ => None
    | Failed => Some FailedV
    | Halted m => Some (HaltedV m)
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v ->
           of_val v = e.
  Proof.
    intros. destruct e; simpl in H; inv H; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof.
    destruct v; reflexivity.
  Qed.

  Definition state: Type := ().

  Definition prim_step: expr -> state -> list Empty_set -> expr -> state -> list expr -> Prop :=
    fun e σ o e' σ' efs => step e e'.

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs ->
      to_val e = None.
  Proof.
    unfold prim_step; simpl; intros.
    inv H; reflexivity.
  Qed.

  Definition cap_lang_mixin: LanguageMixin of_val to_val prim_step.
  Proof.
    constructor.
    - exact to_of_val.
    - exact of_to_val.
    - exact val_stuck.
  Qed.

End cap_lang.

Canonical Structure cap_lang: language :=
  @Language _ _ _ _ _ _ _ cap_lang.cap_lang_mixin.

Export cap_lang.

Section macros.

  Variables RT1 RT2 RT3: RegName.

  Definition Fname := Z.

  Variable f_malloc: Fname.

  Definition fetch (r: RegName) (f: Fname): list instr :=
    [
      Mov r (inr PC);
      GetB RT1 r;
      GetA RT2 r;
      Sub RT1 (inr RT2) (inr RT2);
      Lea r (inr RT1);
      Load r r;
      Lea r (inl f);
      Mov RT1 (inl 0%Z);
      Mov RT2 (inl 0%Z);
      Load r r
    ].

  Definition malloc (r: RegName) (n: Z): list instr :=
    fetch r f_malloc ++
    [      
      Mov (R 1 eq_refl) (inl n);
      Mov RT1 (inr (R 0 eq_refl));
      Mov (R 0 eq_refl) (inr PC);
      Lea (R 0 eq_refl) (inl 4%Z);
      Restrict (R 0 eq_refl) (inl (encodePerm E));
      Jmp r;
      Mov r (inr (R 1 eq_refl));
      Mov (R 0 eq_refl) (inr RT1);
      Mov (R 1 eq_refl) (inl 0%Z);
      Mov RT1 (inl 0%Z)
    ].

      (* TODO others macro *)
End macros.


Require Coq.Logic.FunctionalExtensionality.

Section ExamplePrograms.

  Fixpoint make_prog_mem_aux (l: list instr) (k: Mem) (n: Z): Mem :=
    match l with
    | nil => k
    | i::l => make_prog_mem_aux l (fun a => if addr_eq_dec a n then encode i else k a) (n + 1)
    end.

  Definition make_prog_mem (l: list instr): Mem :=
    make_prog_mem_aux l (fun _ => inl 0%Z) 0.

  Definition R0 := R 0 eq_refl.

  Definition loop_mem: Mem := make_prog_mem [Jmp PC].

  Definition init_reg: Reg :=
    fun r => match r with
          | PC => inr ((RX, Global), 0%Z, None, 0%Z)
          | _ => inl 0%Z
          end.

  Definition loop_init_conf: Conf := Normal (init_reg, loop_mem).

  Lemma loop_is_loop:
    forall n, starN step n loop_init_conf loop_init_conf.
  Proof.
    induction n; econstructor.
    - econstructor 2; eauto.
      simpl. econstructor 2; eauto. lia.
    - simpl. replace (loop_mem 0%Z) with (encode (Jmp PC)) by reflexivity.
      rewrite cap_lang.decode_encode_inv. simpl.
      unfold update_reg. simpl.
      assert ((fun x => if reg_eq_dec x PC then inr (RX, Global, 0%Z, None, 0%Z) else init_reg x) = init_reg).
      { apply FunctionalExtensionality.functional_extensionality. intros.
        destruct (reg_eq_dec x PC); auto.
        subst x. reflexivity. }
      rewrite H. exact IHn.
  Qed.

End ExamplePrograms.