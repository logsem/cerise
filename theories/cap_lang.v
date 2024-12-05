From iris.prelude Require Import prelude.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg machine_base machine_parameters.
Set Warnings "-redundant-canonical-projection".

Ltac inv H := inversion H; clear H; subst.

Record ExecConf := MkExecConf {
      reg : Reg;
      mem : Mem;
      etable : ETable; (* representation of enclave table as part of the machine configuration *)
      enumcur : ENum; (* EC register, keeps track of num. enclaves registered *)
  }.

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

(* NOTE: could use TChajed's coq-record-update library if this gets much more annoying https://github.com/tchajed/coq-record-update/tree/master/src *)
Definition update_regs (φ: ExecConf) (reg' : Reg) : ExecConf := MkExecConf reg' (mem φ) (etable φ) (enumcur φ).
Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf := update_regs φ (<[ r := w ]> (reg φ)).
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf := MkExecConf (reg φ) (<[a:=w]>(mem φ)) (etable φ) (enumcur φ).
Definition update_etable (φ: ExecConf) (i: TIndex) (eid : EId) (enum : ENum): ExecConf := MkExecConf (reg φ) (mem φ) (<[i := (eid,enum)]>(etable φ)) (enumcur φ).
Definition remove_from_etable (φ : ExecConf) (i : TIndex) : ExecConf :=
   match φ with
   | {| reg := reg; mem := mem; etable := etable; enumcur := enumcur |} =>
     {| reg := reg; mem := mem; etable := (delete i etable); enumcur := enumcur |}
   end.

(* global freshness, alt: axiomatize a freshness function
   -- keeps it implementation independent *)
Definition gen_fresh_idx {K V} `{EqDecision K} `{Countable K} (m : gmap K V) : option ENum :=
  Some (map_fold (λ _ _ n, 1 + n) 1 m)%Z.

Definition update_enumcur (φ: ExecConf) (enumcur : ENum): ExecConf := MkExecConf (reg φ) (mem φ) (etable φ) enumcur.

(* Note that the `None` values here also undo any previous changes that were tentatively made in the same step. This is more consistent across the board. *)
Definition updatePC (φ: ExecConf): option Conf :=
  match (reg φ) !! PC with
  | Some (WCap p b e a) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ PC (WCap p b e a')) in
                Some (NextI, φ')
    | None => None
    end
  | _ => None
  end.

(*--- z_of_argument ---*)

Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! r with
    | Some (WInt z) => Some z
    | _ => None
    end
  end.

Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z) ∧ regs' !! r = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma z_of_arg_mono (regs r: Reg) arg argz:
regs ⊆ r
-> z_of_argument regs arg = Some argz
-> z_of_argument r arg = Some argz.
Proof.
  intros.
  unfold z_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply lookup_weaken in Heq as ->; auto.
Qed.

(*--- word_of_argument ---*)

Definition word_of_argument (regs: Reg) (a: Z + RegName): option Word :=
  match a with
  | inl n => Some (WInt n)
  | inr r => regs !! r
  end.

Lemma word_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !! r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma word_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !! r = Some w ∧ regs' !! r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma word_of_argument_inr (regs: Reg) (arg: Z + RegName) p b e a:
  word_of_argument regs arg = Some (WCap p b e a) →
  (∃ r : RegName, arg = inr r ∧ regs !! r = Some (WCap p b e a)).
Proof.
  intros HStoreV.
  unfold word_of_argument in HStoreV.
  destruct arg.
      - by inversion HStoreV.
      - exists r. destruct (regs !! r) eqn:Hvr0; last by inversion HStoreV.
        split; auto.
Qed.

Lemma word_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> word_of_argument regs arg = Some w
-> word_of_argument r arg = Some w.
Proof.
  intros.
  unfold word_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply lookup_weaken in Heq as ->; auto.
Qed.

(*--- addr_of_argument ---*)

Definition addr_of_argument regs src :=
  match z_of_argument regs src with
  | Some n => z_to_addr n
  | None => None
  end.

Lemma addr_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma addr_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  regs ⊆ regs' →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z) ∧ regs' !! r = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma addr_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> addr_of_argument regs arg = Some w
-> addr_of_argument r arg = Some w.
Proof.
  intros.
  unfold addr_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply lookup_weaken in Heq as ->; auto.
Qed.

(*--- otype_of_argument ---*)

Definition otype_of_argument regs src : option OType :=
  match z_of_argument regs src with
  | Some n => (z_to_otype n) : option OType
  | None => None : option OType
  end.

Lemma otype_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z)).
Proof.
  unfold otype_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma otype_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  regs ⊆ regs' →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (WInt z) ∧ regs' !! r = Some (WInt z)).
Proof.
  unfold otype_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma otype_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> otype_of_argument regs arg = Some w
-> otype_of_argument r arg = Some w.
Proof.
  intros.
  unfold otype_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !! _)  eqn:Heq; [| congruence].
  eapply lookup_weaken in Heq as ->; auto.
Qed.


Definition is_scap (w : Word) :=
  match w with
    | WCap p b e a => true
    | WSealed _ (SCap p b e a) => true
    | _ => false end.
Definition get_scap (w : Word) : option Sealable :=
  match w with
    | WCap p b e a => Some (SCap p b e a)
    | WSealed _ (SCap p b e a) => Some (SCap p b e a)
    | _ => None end.
Lemma get_is_scap w sb : get_scap w = Some sb → is_scap w = true.
Proof. unfold get_scap, is_scap. repeat (case_match); auto. all: intro; by exfalso. Qed.

Definition overlap_wordb (w1 w2 : Word) : bool :=
  match get_scap w1, get_scap w2 with
  | Some (SCap _ b1 e1 _), Some (SCap _ b2 e2 _) =>
      if (b1 <? b2)%a
      then (b2 <=? (e1 ^+ (-1)))%a
      else (b1 <=? (e2 ^+ (-1)))%a
  | _, _ => false
  end.

Definition overlap_word (w1 w2 : Word) : Prop :=
  match get_scap w1, get_scap w2 with
  | Some (SCap _ b1 e1 _), Some (SCap _ b2 e2 _) =>
      if (b1 <? b2)%a
      then (b2 <= (e1 ^+ (-1)))%a
      else (b1 <= (e2 ^+ (-1)))%a
  | _, _ => False
  end.

Global Instance overlap_word_dec (w1 w2 : Word) : Decision (overlap_word w1 w2).
Proof.
  rewrite /overlap_word.
  destruct (get_scap w1); last solve_decision.
  destruct s ; last solve_decision.
  destruct (get_scap w2); last solve_decision.
  destruct s ; last solve_decision.
  destruct (b <? b0)%a; solve_decision.
Defined.

Definition unique_in_registers (regs : Reg) (wsrc : Word) (exclsrc : option RegName) : Prop :=
  (map_Forall
     (λ (r : RegName) (wr : Word),
       match exclsrc with
       | None => ¬ overlap_word wsrc wr
       | Some src => if decide (r = src) then True else ¬ overlap_word wsrc wr
       end)
     regs).

Global Instance unique_in_registers_dec (regs : Reg) (wsrc : Word) (src : option RegName)
  : Decision (unique_in_registers regs wsrc src).
Proof.
  apply map_Forall_dec.
  move=> r rw.
  destruct src.
  { case_decide; solve_decision. }
  { solve_decision. }
Defined.

(* Returns [true] if [r] is unique. *)
Definition sweep_registers_reg (regs : Reg) (src : RegName) : bool :=
  match regs !! src with
  | None => true (* if we don't find the register src, then it cannot overlap *)
  | Some wsrc => (bool_decide (unique_in_registers regs wsrc (Some src)))
  end.

Definition sweep_registers_addr (mem : Mem) (regs : Reg) (a : Addr) : bool :=
  match mem !! a with
  | None => true (* if we don't find the register src, then it cannot overlap *)
  | Some wsrc => (bool_decide (unique_in_registers regs wsrc None))
  end.

Lemma sweep_registers_reg_spec (regs : Reg) (src : RegName) (wsrc : Word) :
  sweep_registers_reg regs src = true ->
  regs !! src = Some wsrc ->
  unique_in_registers regs wsrc (Some src).
Proof.
  move=> Hsweep Hsrc.
  rewrite /sweep_registers_reg Hsrc in Hsweep.
  by apply bool_decide_eq_true in Hsweep.
Qed.

Lemma sweep_registers_addr_spec (mem : Mem) (regs : Reg) (excla : Addr) (wsrc : Word) :
  sweep_registers_addr mem regs excla = true ->
  mem !! excla = Some wsrc ->
  unique_in_registers regs wsrc None.
Proof.
  move=> Hsweep Hsrc.
  rewrite /sweep_registers_addr Hsrc in Hsweep.
  by apply bool_decide_eq_true in Hsweep.
Qed.

Definition unique_in_memory (mem : Mem) (wsrc : Word) (excla : option Addr) : Prop :=
  (map_Forall
     (λ (a : Addr) (wa : Word),
       match excla with
       | None        => ¬ overlap_word wsrc wa
       | Some wexcla => if decide (a = wexcla) then True else ¬ overlap_word wsrc wa
       end)
     mem).

Global Instance unique_in_memory_dec (mem : Mem) (wsrc : Word) (excla : option Addr)
  : Decision (unique_in_memory mem wsrc excla).
Proof.
  apply map_Forall_dec.
  move=> r rw.
  destruct excla.
  { case_decide; solve_decision. }
  { solve_decision. }
Defined.

(* Returns [true] if [r] is unique. *)
Definition sweep_memory_reg (mem : Mem) (regs : Reg) (src : RegName) : bool :=
  match regs !! src with
  | None => true (* if we don't find the register src, then it cannot overlap *)
  | Some wsrc => (bool_decide (unique_in_memory mem wsrc None))
  end.

Definition sweep_memory_addr (mem : Mem) (regs : Reg) (a : Addr) : bool :=
  match mem !! a with
  | None => true (* if we don't find the addr src, then it cannot overlap *)
  | Some w => (bool_decide (unique_in_memory mem w (Some a)))
  end.

Lemma sweep_memory_reg_spec (mem : Mem) (regs : Reg) (src : RegName) (wsrc : Word) :
  sweep_memory_reg mem regs src = true ->
  regs !! src = Some wsrc ->
  unique_in_memory mem wsrc None.
Proof.
  intros Hsweep Hsrc.
  rewrite /sweep_memory_reg Hsrc in Hsweep.
  by apply bool_decide_eq_true in Hsweep.
Qed.

Lemma sweep_memory_addr_spec (mem : Mem) (regs : Reg) (excla : Addr) (wexcla : Word) :
  sweep_memory_addr mem regs excla = true ->
  mem !! excla = Some wexcla ->
  unique_in_memory mem wexcla (Some excla).
Proof.
  intros Hsweep Hsrc.
  rewrite /sweep_memory_addr Hsrc in Hsweep.
  by apply bool_decide_eq_true in Hsweep.
Qed.

(* Returns [true] if [r] is unique. *)
(* src is the register that is excluded in the sweeping *)
Definition sweep_reg (mem : Mem) (regs : Reg) (src : RegName) : bool :=
  let unique_mem := sweep_memory_reg mem regs src in
  let unique_reg := sweep_registers_reg regs src in
  unique_mem && unique_reg
.

Definition sweep_addr (mem : Mem) (regs : Reg) (a : Addr) : bool :=
  let unique_mem := sweep_memory_addr mem regs a in
  let unique_reg := sweep_registers_addr mem regs a in
  unique_mem && unique_reg
.

Definition unique_in_machine_reg (mem : Mem) (regs : Reg) (src : RegName) (wsrc : Word) :=
  regs !! src = Some wsrc ->
  unique_in_registers regs wsrc (Some src) /\ unique_in_memory mem wsrc None.

Definition unique_in_machine_addr (mem : Mem) (regs : Reg) (excla : Addr) (wexcla : Word) :=
  mem !! excla = Some wexcla ->
  unique_in_registers regs wexcla None /\ unique_in_memory mem wexcla (Some excla).

Lemma sweep_reg_spec (mem : Mem) (regs : Reg) (src : RegName) (wsrc : Word) :
  sweep_reg mem regs src = true →
  regs !! src = Some wsrc ->
  unique_in_machine_reg mem regs src wsrc.
Proof.
  move=> Hsweep Hsrc.
  rewrite /sweep_reg andb_true_iff in Hsweep.
  by destruct Hsweep; split
  ; [eapply sweep_registers_reg_spec | eapply sweep_memory_reg_spec].
Qed.

Lemma sweep_addr_spec (mem : Mem) (regs : Reg) (excla : Addr) (wexcla : Word) :
  sweep_addr mem regs excla = true →
  mem !! excla = Some wexcla ->
  unique_in_machine_addr mem regs excla wexcla.
Proof.
  move=> Hsweep Hsrc.
  rewrite /sweep_reg andb_true_iff in Hsweep.
  by destruct Hsweep; split
  ; [eapply sweep_registers_addr_spec | eapply sweep_memory_addr_spec].
Qed.

Section opsem.
  Context `{MachineParameters}.

  Definition get_wcap : Word -> option (Perm * Addr * Addr * Addr) :=
    fun w => match  w with WCap p b e a => Some (p, b, e, a)
                         | _ => None end.

  Definition get_wcap_scap : Word -> option (Perm * Addr * Addr * Addr) :=
    fun w => match  w with WCap p b e a | WSealed _ (SCap p b e a) => Some (p, b, e, a)
                         | _ => None end.

  Definition contains_cap (mem : Mem) (b : Addr) (e : Addr) : Prop :=
    map_Forall (λ (a : Addr) (wa : Word),
        if decide ((a <= b)%a ∧ (b <= e)%a)
        then is_cap wa
        else false)
      mem.

  Global Instance contains_cap_dec (mem : Mem) (b : Addr) (e : Addr)
    : Decision (contains_cap mem b e).
  Proof. apply map_Forall_dec. intros a w. destruct w; case_decide; solve_decision. Defined.

  Definition no_cap (mem : Mem) (b: Addr) (e : Addr) : bool :=
    bool_decide (not (contains_cap mem b e)).

  Definition retrieve_eid (i : TIndex) (tb : ETable) : option EId :=
    match (tb !! i) with
    | Some p => Some (fst p)
    | None => None
    end.

  Definition retrieve_enum (i : TIndex) (tb : ETable) : option ENum :=
    match (tb !! i) with
    | Some p => Some (snd p)
    | None => None
    end.

  Definition finz_div_nat {bound} (f : finz bound) (off : nat) : option (finz bound).
    refine (
    match off with
    | Coq.Init.Datatypes.O => None
    | _ => let z := (finz.to_z f / off)%Z in
           match (Z_lt_dec z bound) with
           | left _ =>
               match (Z_le_dec 0%Z z) with
               | left _ => Some (finz.FinZ z _ _)
               | right _ => None
               end
           | right _ => None
           end
    end). apply Z.ltb_lt. auto. apply Z.leb_le. auto.
  Defined.

  Definition seal_of_oa (oa : OType) : option ENum :=
    finz.to_z <$> if (Z.even (finz.to_z oa))
                  then (finz_div_nat oa 2)
                  else finz_div_nat (oa^-1)%f 2.

  Definition has_seal : Word -> option ENum :=
    λ σ, (match σ with
          | WSealRange _ _ _ oa => seal_of_oa oa
          | _ => None (* rs does not contain seals *)
          end).

  Axiom measure : Mem -> Addr -> Addr -> Z.

  Definition eid_of_enum (etable : ETable) (enum : ENum) : option EId :=
   map_fold
     (λ idx p oi,
       match oi with
       | Some i => Some i
       | None => if decide (enum = p.2) then Some p.1 else None
       end)
     None
     etable.

  Definition tindex_of_eid (etable : ETable) (eid : EId) : option TIndex :=
   map_fold
     (λ idx p oi,
       match oi with
       | Some i => Some i
       | None => if decide (eid = p.1) then Some idx else None
       end)
     None
     etable.

  (* cannot stand the nested indentation *)
  Notation "'when' A 'then' B" := (if decide A then B else None) (at level 60).
  Notation "a |>> f" := (f a) (at level 10, only parsing, left associativity).

  Definition exec_opt (i: instr) (φ: ExecConf): option Conf :=
    match i with
    | Fail => Some (Failed, φ)
    | Halt => Some (Halted, φ)
    | Jmp r =>
      wr ← (reg φ) !! r;
      let φ' := (update_reg φ PC (updatePcPerm wr)) in Some (NextI, φ') (* Note: allow jumping to integers, sealing ranges etc; machine will crash later *)
    | Jnz r1 r2 =>
      wr2 ← (reg φ) !! r2;
      wr1 ← (reg φ) !! r1;
      if nonZero wr2 then
        let φ' := (update_reg φ PC (updatePcPerm wr1)) in Some (NextI, φ')
      else updatePC φ
    | Load dst src =>
      wsrc ← (reg φ) !! src;
      match wsrc with
      | WCap p b e a =>
        if readAllowed p && withinBounds b e a then
          asrc ← (mem φ) !! a;
          updatePC (update_reg φ dst asrc)
        else None
      | _ => None
      end
    | Store dst ρ =>
      tostore ← word_of_argument (reg φ) ρ;
      wdst ← (reg φ) !! dst;
      '(p, b, e, a) ← get_wcap wdst;
        if writeAllowed p && withinBounds b e a
        then updatePC (update_mem φ a tostore)
        else None
    | Mov dst ρ =>
      tomov ← word_of_argument (reg φ) ρ;
      updatePC (update_reg φ dst tomov)
    | Lea dst ρ =>
      n ← z_of_argument (reg φ) ρ;
      wdst ← (reg φ) !! dst;
      match wdst with
      | WCap p b e a =>
        match p with
        | E => None
        | _ => match (a + n)%a with
               | Some a' => updatePC (update_reg φ dst (WCap p b e a'))
               | None => None
               end
        end
      | WSealRange p b e a =>
         match (a + n)%ot with
          | Some a' => updatePC (update_reg φ dst (WSealRange p b e a'))
          | None => None
          end
      | _ => None
      end
    | Restrict dst ρ =>
      n ← z_of_argument (reg φ) ρ ;
      wdst ← (reg φ) !! dst;
      match wdst with
      | WCap permPair b e a =>
        match permPair with
        | E => None
        | _ => if PermFlowsTo (decodePerm n) permPair then
                updatePC (update_reg φ dst (WCap (decodePerm n) b e a))
              else None
        end
      | WSealRange p b e a =>
        if SealPermFlowsTo (decodeSealPerms n) p then
              updatePC (update_reg φ dst (WSealRange (decodeSealPerms n) b e a))
        else None
      | _ => None
      end
    | Add dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 + n2)%Z))
    | Sub dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 - n2)%Z))
    | Lt dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (Z.b2z (Z.ltb n1 n2))))
  | Subseg dst ρ1 ρ2 =>
    wdst ← (reg φ) !! dst;
    match wdst with
    | WCap p b e a =>
      a1 ← addr_of_argument (reg φ) ρ1;
      a2 ← addr_of_argument (reg φ) ρ2;
      match p with
      | E => None
      | _ =>
        if isWithin a1 a2 b e then
          updatePC (update_reg φ dst (WCap p a1 a2 a))
        else None
      end
    | WSealRange p b e a =>
      o1 ← otype_of_argument (reg φ) ρ1;
      o2 ← otype_of_argument (reg φ) ρ2;
      if isWithin o1 o2 b e then
        updatePC (update_reg φ dst (WSealRange p o1 o2 a))
      else None
    | _ => None
    end
  | GetA dst r =>
    wr ← (reg φ) !! r;
    match wr with
    | WCap _ _ _ a => updatePC (update_reg φ dst (WInt a))
    | WSealRange _ _ _ a => updatePC (update_reg φ dst (WInt a))
    | _ => None
    end
  | GetB dst r =>
    wr ← (reg φ) !! r;
    match wr with
    | WCap _ b _ _ => updatePC (update_reg φ dst (WInt b))
    | WSealRange _ b _ _ => updatePC (update_reg φ dst (WInt b))
    | _ => None
    end
  | GetE dst r =>
    wr ← (reg φ) !! r;
    match wr with
    | WCap _ _ e _ => updatePC (update_reg φ dst (WInt e))
    | WSealRange _ _ e _ => updatePC (update_reg φ dst (WInt e))
    | _ => None
    end
  | GetP dst r =>
    wr ← (reg φ) !! r;
    match wr with
    | WCap p _ _ _ => updatePC (update_reg φ dst (WInt (encodePerm p)))
    | WSealRange p _ _ _ => updatePC (update_reg φ dst (WInt (encodeSealPerms p)))
    | _ => None
    end

  | GetOType dst r =>
    wr ← (reg φ) !! r;
    match wr with
    | WSealed o _ => updatePC (update_reg φ dst (WInt o))
    (* NOTE if not a sealed, return -1 in any other case ? What if not a sealable ? *)
    | _ => updatePC (update_reg φ dst (WInt (-1)))
    end

  | GetWType dst r =>
    wr ← (reg φ) !! r; updatePC (update_reg φ dst (WInt (encodeWordType wr)))

  | Seal dst r1 r2 =>
    wr1 ← (reg φ) !! r1;
    wr2 ← (reg φ) !! r2;
    match wr1,wr2 with
    | WSealRange p b e a, WSealable sb =>
      if permit_seal p && withinBounds b e a then updatePC (update_reg φ dst (WSealed a sb))
      else None
    | _, _ => None
    end
  | UnSeal dst r1 r2 =>
    wr1 ← (reg φ) !! r1;
    wr2 ← (reg φ) !! r2;
    match wr1, wr2 with
    | WSealRange p b e a, WSealed a' sb =>
        if decide (permit_unseal p = true ∧ withinBounds b e a = true ∧ a' = a) then updatePC (update_reg φ dst (WSealable sb))
        else None
    | _,_ => None
    end
    (* enclave initialization *)
  | EInit rd rs =>

    (* obtain RX_ permissions for code section *)
    ccap          ← (reg φ) !! rs; (* get code capability *)
    '(p, b, e, a) ← get_wcap ccap;
    when (readAllowed p && executeAllowed p) then

    (* obtain RW_ permissions for data section *)
    dcap              ← (mem φ) !! b;
    '(p', b', e', a') ← get_wcap dcap;
    when (readAllowed p' && writeAllowed p') then

    (* MEMORY SWEEP *)
    when ( (sweep_addr (mem φ) (reg φ) b) && (* sweep the memory excluding the data cap at location b *)
           (sweep_reg (mem φ) (reg φ) rs) && (* sweep the registers excluding the code cap in register rs *)
           (no_cap (mem φ) (b^+1)%a e) ) then (* ccap does not contain capabilities except dcap at addr b *)

    (* ALLOCATION OF THE ENCLAVE'S SEALS *)
    (* IIUC: the EC register acts as a bump allocator for enclave otypes *)
    (* therefore, to generate the seals for the enclave, it is sufficient to use the value of the EC register
       and (by convention) assume 2 * EC is seal and 2 * EC + 1 is unseal. *)
    let ec := enumcur φ in
    s_b ← finz.of_z (2*ec); (* coerce seal base and end addresses into the finZ ONum type *)
    s_e ← finz.of_z (2*ec + 2);
    let seals := (WSealRange (true, true) s_b s_e s_b) in (* permitSeal & permitUnseal *)

    (* MEASURE THE CODE FOOTPRINT OF THE ENCLAVE *)
    incr_b ← finz.of_z (b+1);
    let identity := measure (mem φ) incr_b e in

    fresh_idx ← gen_fresh_idx (etable φ); (* generate a fresh index in the ETable *)
    let incr_ec := ((enumcur φ)+1)%Z in

    (* UPDATE THE MACHINE STATE *)
    φ  |>> update_mem b' seals    (* store seals at base address of enclave's data sec.*)
       |>> update_etable fresh_idx identity ec (* create a new index in the ETable *)
       |>> update_enumcur incr_ec  (* EC := EC + 1 *)
       |>> update_reg rd (WCap E b e a) (* Position cursor at address a: client specifies entry point *)
       |>> updatePC

    (* enclave deinitialization *)
  | EDeInit rd rs =>
      σ   ← (reg φ) !! rs; (* σ should be a seal/unseal pair *)
      eid ← has_seal σ;
      i   ← tindex_of_eid (etable φ) eid;

      (* UPDATE THE MACHINE STATE *)
      φ |>> remove_from_etable i
        |>> update_reg rd (WInt 1) (* write 1 (success) to rd reg *) (* Denis says: no longer needed since machine either fails or ends up in this state *)
        |>> updatePC

    (* enclave local attestation *)
  | EStoreId rd rs1 rs2 =>
      σ             ← (reg φ) !! rs1;
      enum          ← has_seal σ;
      id            ← eid_of_enum (etable φ) enum;
      wrs2          ← (reg φ) !! rs2;
      '(p, b, e, a) ← get_wcap wrs2;

      (* UPDATE THE MACHINE STATE *)
      when (writeAllowed p && withinBounds b e a) then
      φ |>> update_mem a (WInt id)
        |>> update_reg rd (WInt 1)
        |>> updatePC

    (* memory sweep *)
  | IsUnique dst src =>
       (* exclude registers, but also the address a itself !! *)
      wsrc          ← (reg φ) !! src;
      '(p, b, e, a) ← get_wcap_scap wsrc; (* TODO ask: does IsUnique also work with sealed cap ? *)
           (* cf. Sail: https://github.com/proteus-core/cheritree/blob/e969919a30191a4e0ceec7282bb9ce982db0de73/sail/sail-cheri-riscv/src/cheri_insts.sail#L2414-L2428
         *)
      φ |>> update_reg dst (WInt 1%Z)
        |>> updatePC
  end.

  Definition exec (i : instr) (φ : ExecConf) : Conf :=
    match exec_opt i φ with
    | None => (Failed, φ)
    | Some conf => conf
    end.

  (* Definition exec (i: instr) (φ: ExecConf) : Conf := *)
  (*    match exec_opt i φ with *)
  (*    | None => *)
  (*        match i with *)
  (*        | EInit _ _ => (* failure retains initial machine state @TODO: what happens to PC? *) *)
  (*            match (φ |>> updatePC) with *)
  (*            | Some conf => conf *)
  (*            | None => (Failed, φ) *)
  (*            end *)
  (*        | EDeInit rd _ | EStoreId rd _ _ | IsUnique rd _ => *)
  (*            match (φ |>> update_reg rd (WInt 0) |>> updatePC) with (* write 0 to RD register *) *)
  (*            | Some conf => conf *)
  (*            | None => (Failed, φ) *)
  (*            end *)
  (*        | _ => (Failed, φ) *)
  (*                 end *)
  (*    | Some conf => conf *)
  (*    end . *)

  Lemma exec_opt_exec_some :
    forall φ i c,
      exec_opt i φ = Some c →
      exec i φ = c.
  Proof. unfold exec. by intros * ->. Qed.
  Lemma exec_opt_exec_none :
    forall φ i,
      exec_opt i φ = None →
      exec i φ = (Failed, φ).
  Proof. unfold exec. by intros * ->. Qed.

  Inductive step: Conf → Conf → Prop :=
  | step_exec_regfail:
      forall φ,
        (reg φ) !! PC = None →
        step (Executable, φ) (Failed, φ)
  | step_exec_corrfail:
      forall φ wreg,
        (reg φ) !! PC = Some wreg →
        not (isCorrectPC wreg) →
        step (Executable, φ) (Failed, φ)
  | step_exec_memfail:
      forall φ p b e a,
        (reg φ) !! PC = Some (WCap p b e a) →
        (mem φ) !! a = None →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p b e a i c wa,
        (reg φ) !! PC = Some (WCap p b e a) → (* only works for caps *)
        (mem φ) !! a = Some wa →
        isCorrectPC (WCap p b e a) →
        decodeInstrW wa = i →
        exec i φ = c →
        step (Executable, φ) (c.1, c.2).

  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros. destruct (reg φ !! PC) as [wpc | ] eqn:Hreg.
    destruct (isCorrectPC_dec wpc) as [Hcorr | ].
    set (Hcorr' := Hcorr).
    inversion Hcorr' as [???? _ _ Hre]. subst wpc.
    destruct (mem φ !! a) as [wa | ] eqn:Hmem.
    all: eexists _,_; by econstructor.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.

  Lemma step_exec_inv (r: Reg) p b e a m w instr (c: ConfFlag) (σ: ExecConf) etbl ecur :
    r !! PC = Some (WCap p b e a) →
    isCorrectPC (WCap p b e a) →
    m !! a = Some w →
    decodeInstrW w = instr →
    step (Executable, {| reg := r; mem := m; etable := etbl ; enumcur := ecur |}) (c, σ) →
    exec instr {| reg := r; mem := m; etable := etbl ; enumcur := ecur |} = (c, σ).
  Proof.
    intros HPC Hpc Hm Hinstr. inversion 1; cbn in *.
    1,2,3: congruence.
    simplify_eq. by destruct (exec _ _).
  Qed.

  Lemma step_fail_inv wpc c (σ σ': ExecConf) :
    reg σ !! PC = Some wpc →
    ¬ isCorrectPC wpc →
    step (Executable, σ) (c, σ') →
    c = Failed ∧ σ' = σ.
  Proof.
    intros Hw HPC Hs. inversion Hs; subst; auto.
    congruence.
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

  Definition to_val (e: expr): option val :=
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
    match goal with HH : _ !! _ = _ |- _ => rewrite ->HH in * end.
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

  Lemma updatePC_some φ c:
    updatePC φ = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /updatePC; repeat case_match; try congruence. inversion 1. eauto.
  Qed.

  Lemma instr_atomic i φ :
    ∃ φ', (exec i φ = (Failed, φ') ) ∨ (exec i φ = (NextI, φ')) ∨
          (exec i φ = (Halted, φ')).
  Proof.
    unfold exec, exec_opt, get_wcap;
    repeat case_match; simplify_eq; eauto;rename H0 into Heqo.
    (* Create more goals through *_of_argument, now that some have been pruned *)
    all: repeat destruct (addr_of_argument (reg φ) _)
    ; repeat destruct (otype_of_argument (reg φ) _)
    ; repeat destruct (word_of_argument (reg φ) _)
    ; repeat destruct (z_of_argument (reg φ) _)
    ; try destruct (sweep src (reg φ) (mem φ))
    ; cbn in *; try by exfalso.
    all: repeat destruct (reg _ !! _); cbn in *; repeat case_match.
    all: repeat destruct (mem _ !! _); cbn in *; repeat case_match.
    all: simplify_eq; try by exfalso.
    all: try apply updatePC_some in Heqo as [φ' Heqo]; eauto.
    all: repeat (
             destruct (mem _ !! _); cbn in *; repeat case_match
             ; simplify_eq
             ; cbn in *
             ; case_match).
    all: repeat destruct (finz.of_z _); cbn in *
    ; repeat destruct (has_seal _); cbn in *
    ; repeat destruct (tindex_of_eid _); cbn in *
    ; repeat destruct (eid_of_enum _); cbn in *
    ; repeat destruct (get_wcap_scap _); cbn in *.
    all: repeat destruct p.
    all: try apply updatePC_some in Heqo as [φ' Heqo]; eauto.
    all: simplify_eq; try by exfalso.
  Qed.

End opsem.

Canonical Structure cap_ectxi_lang `{MachineParameters} := EctxiLanguage cap_lang_mixin.
Canonical Structure cap_ectx_lang `{MachineParameters} := EctxLanguageOfEctxi cap_ectxi_lang.
Canonical Structure cap_lang `{MachineParameters} := LanguageOfEctx cap_ectx_lang.

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
Instance Reflexive_ofe_equiv_Word : (Reflexive (ofe_equiv (leibnizO Word))).
Proof. intro; reflexivity. Qed.

(****)

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

#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : core.
#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

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

Global Instance ExecConf_inhabited : Inhabited ExecConf.
Proof.
  refine (populate
            {| reg := gmap_empty ;
              mem := gmap_empty ;
              etable := gmap_empty ;
              enumcur := 0%Z |}).
  (* eexists. Unshelve. 3: exact 0%Z. all: solve_finz. *)
Defined.
