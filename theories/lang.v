From iris.algebra Require Import base.
From iris.program_logic Require Import language.
From stdpp Require Import gmap fin_maps list.

Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)

Ltac inv H := inversion H; clear H; subst.

Module cap_lang.

  Definition RegNum: nat := 31.
  Definition MemNum: Z := 2000000. 

  (*Hypothesis RegNum_not_zero: RegNum > O.*)

  Inductive Addr: Type :=
  | A (z : Z) (fin: Z.leb z MemNum = true). 
  
  Instance addr_eq_dec: EqDecision Addr.
    intros x y. destruct x,y. destruct (Z_eq_dec z z0).
    - left. simplify_eq.
      assert (forall (b: bool) (n m: Z) (P1 P2: Z.leb n m = b), P1 = P2).
      { intros. apply eq_proofs_unicity.
        intros; destruct x; destruct y; auto. }
        by rewrite (H true z0 MemNum fin fin0).
    - right. inversion 1. simplify_eq. 
  Defined.

  Definition z_to_addr (z : Z) : option Addr.
  Proof. 
    destruct (Z_le_dec z MemNum).
    - apply (Z.leb_le z MemNum) in l.
      exact (Some (A z l)).
    - exact None. 
  Defined. 

  Instance addr_countable : Countable Addr.
  Proof. 
    refine {| encode r := encode match r with
                          | A z fin => z
                          end ;
              decode n := match (decode n) with
                          | Some z => z_to_addr z
                          | None => None
                          end ;
              decode_encode := _ |}. 
    intro r. destruct r; auto. 
    rewrite decode_encode.
    unfold z_to_addr.
    destruct (Z_le_dec z MemNum).
    - do 2 f_equal. apply eq_proofs_unicity. decide equality.
    - exfalso. by apply (Z.leb_le z MemNum) in fin. 
  Qed.
      
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

  (* None = MemNum bound *)
  Definition Cap: Type :=
    (Perm * Locality) * Addr * option Addr * Addr.

  Definition Word := (Z + Cap)%type.

  Inductive RegName: Type :=
  | PC
  | R (n: nat) (fin: n <=? RegNum = true).

  Instance reg_eq_dec : EqDecision RegName.
  Proof. intros r1 r2.  destruct r1,r2; [by left | by right | by right |].
    destruct (nat_eq_dec n n0).
    + subst n0. left.
      assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
      { intros. apply eq_proofs_unicity.
        intros; destruct x; destruct y; auto. }
      rewrite (H _ _ _ fin fin0). reflexivity.
    + right. congruence.
  Defined.

  Definition n_to_regname (n : nat) : option RegName.
  Proof. 
    destruct (nat_le_dec n RegNum).
    - apply (Nat.leb_le n RegNum) in l.
      exact (Some (R n l)).
    - exact None. 
  Defined. 

  Instance reg_countable : Countable RegName.
  Proof. 
    refine {| encode r := encode match r with
                          | PC => inl ()
                          | R n fin => inr n
                          end ;
              decode n := match (decode n) with
                          | Some (inl ()) => Some PC
                          | Some (inr n) => n_to_regname n
                          | None => None
                          end ;
              decode_encode := _ |}. 
    intro r. destruct r; auto. 
    rewrite decode_encode.
    unfold n_to_regname.
    destruct (nat_le_dec n RegNum).
    - do 2 f_equal. apply eq_proofs_unicity. decide equality.
    - exfalso. by apply (Nat.leb_le n RegNum) in fin. 
  Qed.

  
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

  Notation "mem !m! a" := (MemLocate mem a) (at level 20). 
  Notation "reg !r! r" := (RegLocate reg r) (at level 20). 
  
  Definition ExecConf := (Reg * Mem)%type.

  (* Definition MemSeg := Addr option Word. *)

  (* Definition disjoint_memseg: Disjoint MemSeg := fun ms1 ms2 => forall a w1 w2, ms1 a = Some w1 -> ms2 a = Some w2 -> False. *)

  (* Definition union_memseg (ms1 ms2: MemSeg): MemSeg := *)
  (*   fun a => match ms1 a with *)
  (*         | Some w1 => Some w1 *)
  (*         | None => match ms2 a with *)
  (*                  | Some w2 => Some w2 *)
  (*                  | None => None *)
  (*                  end *)
  (*         end. *)

  (* Definition coerce_memseg_to_mem (ms: MemSeg) (H: forall a, ms a <> None): Mem := *)
  (*   fun a => match ms a as o return (ms a = o → Word) with *)
  (*         | Some w => λ _ : ms a = Some w, w *)
  (*         | None => λ H0 : ms a = None, False_rect Word (H a H0) *)
  (*         end eq_refl. *)

  Inductive ConfFlag : Type :=
  | Executable
  | Halted
  | Failed. 
  
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

  Definition le_lt_addr : Addr → Addr → Addr → Prop :=
    λ a1 a2 a3, match a1,a2,a3 with
                | A z1 fin1, A z2 fin2, A z3 fin3 => (z1 <= z2 < z3)%Z
                end.
  Definition le_addr : Addr → Addr → Prop :=
    λ a1 a2, match a1,a2 with
             | A z1 fin1, A z2 fin2 => (z1 <= z2)%Z
             end.
  Definition lt_addr : Addr → Addr → Prop :=
    λ a1 a2, match a1,a2 with
             | A z1 fin1, A z2 fin2 => (z1 < z2)%Z
             end.
  Definition leb_addr : Addr → Addr → bool :=
    λ a1 a2, match a1,a2 with
             | A z1 _, A z2 _ => Z.leb z1 z2
             end.
  Definition ltb_addr : Addr → Addr → bool :=
    λ a1 a2, match a1,a2 with
             | A z1 _, A z2 _ => Z.ltb z1 z2
             end.
  Definition eqb_addr : Addr → Addr → bool :=
    λ a1 a2, match a1,a2 with
             | A z1 _,A z2 _ => Z.eqb z1 z2
             end.
  Definition za : Addr. Proof. refine (A 0%Z _); eauto. Defined.  
  Definition special_a : Addr. Proof. refine (A (-42)%Z _); eauto. Defined.
  Definition top : Addr. Proof. refine (A MemNum _); eauto. Defined. 
  Delimit Scope Addr_scope with a.
  Notation "a1 <= a2 < a3" := (le_lt_addr a1 a2 a3): Addr_scope.
  Notation "a1 <= a2" := (le_addr a1 a2): Addr_scope.
  Notation "a1 <=? a2" := (leb_addr a1 a2): Addr_scope.
  Notation "a1 <? a2" := (ltb_addr a1 a2): Addr_scope.
  Notation "a1 =? a2" := (eqb_addr a1 a2): Addr_scope.
  Notation "0" := (za) : Addr_scope.
  Notation "- 42" := (special_a) : Addr_scope.

  Instance Addr_le_dec : RelDecision le_addr. 
  Proof. intros x y. destruct x,y. destruct (Z_le_dec z z0); [by left|by right]. Defined.
  Instance Addr_lt_dec : RelDecision lt_addr. 
  Proof. intros x y. destruct x,y. destruct (Z_lt_dec z z0); [by left|by right]. Defined.
  
  Inductive isCorrectPC: Word -> Prop :=
  | isCorrectPC_intro:
      forall p g (b e a : Addr),
        (b <= a < e)%a ->
        p = RX \/ p = RWX \/ p = RWLX ->
        isCorrectPC (inr ((p, g), b, (Some e), a))
  | isCorrectPC_intro_infinity:
      forall p g (b a : Addr),
        (b <= a)%a ->
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
      | None => (b <=? a)%a
      | Some e => (b <=? a)%a && (a <=? e)%a
      end
    end.

  Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf := (<[r:=w]>(reg φ),mem φ).
  Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf := (reg φ, <[a:=w]>(mem φ)).

  (* (fun x => if reg_eq_dec x r then w else reg ϕ x , mem ϕ). *)

  (* Definition update_mem (ϕ: ExecConf) (a: Addr) (w: Word): ExecConf := *)
  (*   (reg ϕ, fun x => if addr_eq_dec x a then w else mem ϕ x). *)

  Definition incr_addr : Addr → Z → option Addr.
  Proof.
    destruct 1. intros z'. 
    destruct (Z.leb (z + z')%Z MemNum) eqn:Hlt.
    - refine (Some (A (z + z')%Z _)).
      by apply Z.leb_le; apply Z.leb_le. 
    - exact None. 
  Defined.
  Notation "a1 + z" := (incr_addr a1 z): Addr_scope.
    
  Definition updatePC (φ: ExecConf): Conf :=
    match RegLocate (reg φ) PC with
    | inr ((p, g), b, e, a) =>
      match (a + 1)%a with
      | Some a' => let φ' := (update_reg φ PC (inr ((p, g), b, e, a'))) in
                   (Executable, φ')
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

  Definition isWithin (n1 n2 b: Addr) (e: option Addr): bool :=
    match e with
    | None => ((0 <=? b) && (b <=? n1) && (0 <=? n2) || (n2 =? -42))%a
    | Some e => ((0 <=? b) && (b <=? n1) && (0 <=? n2) && (n2 <=? e))%a
    end.

  Definition exec (i: instr) (φ: ExecConf): Conf :=
    match i with
    | Fail => (Failed, φ)
    | Halt => (Halted, φ)
    | Jmp r => let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r))) in (Executable, φ')
    | Jnz r1 r2 =>
      if nonZero (RegLocate (reg φ) r2) then
        let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r1))) in (Executable, φ')
      else updatePC φ
    | Load dst src =>
      match RegLocate (reg φ) src with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        if readAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_reg φ dst (MemLocate (mem φ) a))
        else (Failed, φ)
      end
    | Store dst (inr src) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
        if writeAllowed p && withinBounds ((p, g), b, e, a) then
          match RegLocate (reg φ) src with
          | inl n => updatePC (update_mem φ a (RegLocate (reg φ) src))
          | inr ((_, g'), _, _, _) => if isLocal g' then
                                       match p with
                                       | RWLX | RWL => updatePC (update_mem φ a (RegLocate (reg φ) src))
                                       | _ => (Failed, φ)
                                       end
                                     else updatePC (update_mem φ a (RegLocate (reg φ) src))
          end
        else (Failed, φ)
      end
    | Store dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr ((p, g), b, e, a) =>
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
        if PermPairFlowsTo (decodePermPair n) permPair then
          updatePC (update_reg φ dst (inr (decodePermPair n, b, e, a)))
        else (Failed, φ)
      end
    | Restrict dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (permPair, b, e, a) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          if PermPairFlowsTo (decodePermPair n) permPair then
            updatePC (update_reg φ dst (inr (decodePermPair n, b, e, a)))
          else (Failed, φ)
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
                  updatePC (update_reg φ dst (inr ((p, g), a1, if (a2 =? (-42))%a then None else Some a2, a)))
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
                updatePC (update_reg φ dst (inr ((p, g), a1, if (a2 =? (-42))%a then None else Some a2, a)))
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
                updatePC (update_reg φ dst (inr ((p, g), a1, if (a2 =? (-42))%a then None else Some a2, a)))
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
              updatePC (update_reg φ dst (inr ((p, g), a1, if (a2 =? -42)%a then None else Some a2, a)))
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
        | A a' _ => updatePC (update_reg φ dst (inl a'))
        end
      end
    | GetB dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (_, b, _, _) =>
        match b with
        | A b' _ => updatePC (update_reg φ dst (inl b'))
        end
      end
    | GetE dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (_, _, e, _) =>
        match e with
        | None => updatePC (update_reg φ dst (inl (-42)%Z))
        | Some e =>
          match e with
          | A e' _ => updatePC (update_reg φ dst (inl e'))
          end
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
        * destruct e. 
          { destruct (Addr_lt_dec a a0).
            - left. destruct a,a0,b. simpl in *. econstructor; simpl; eauto. 
              destruct p; simpl in H; try congruence; auto.
            - right. destruct a,a0,b. simpl in *. red; intros. inv H0.
              destruct H3. congruence. }
          { left. destruct a,b. simpl in *. econstructor; eauto.
            destruct p; simpl in H; try congruence; auto. }
        * right. destruct a,b. simpl in *. red; intros; inv H0. 
          { destruct e0. destruct H3. elim n; eauto. }
          { elim n; auto. }
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

  (* Actually nsteps from stdpp *)
  (* Inductive starN {A: Type} {B : Type} (step: A -> B -> A -> B -> Prop): nat -> A -> B -> A -> B -> Prop := *)
  (* | starN_refl: *)
  (*     forall (s: A) (σ : B), starN step 0 s σ s σ *)
  (* | starN_step: *)
  (*     forall n s1 s2 s3 σ σ' σ'', *)
  (*       step s1 σ s2 σ' -> *)
  (*       starN step n s2 σ' s3 σ'' -> *)
  (*       starN step (S n) s1 σ s3 σ''. *)

  (* Lemma starN_step_deterministic: *)
  (*   forall n c1 c2 c2' σ1 σ2 σ2', *)
  (*     starN step n c1 σ1 c2 σ2 -> *)
  (*     starN step n c1 σ1 c2' σ2'-> *)
  (*     c2 = c2' ∧ σ2 = σ2'. *)
  (* Proof. *)
  (*   induction 1; intros; split. *)
  (*   - inv H; auto. *)
  (*   - inv H; auto.  *)
  (*   - inv H1. generalize (step_deterministic _ _ _ _ _ _ H H3). *)
  (*     intros [? ->]; subst s4. eapply IHstarN; eauto. *)
  (*   - inv H1. generalize (step_deterministic _ _ _ _ _ _ H H3). *)
  (*     intros [? ->]; subst s4. eapply IHstarN; eauto. *)
  (* Qed. *)

  (* Lemma starN_halted: *)
  (*   forall n c m σ σ', *)
  (*     starN step n c σ (Halted m) σ' -> *)
  (*     forall n' c' σ'', starN step n' c σ c' σ'' -> *)
  (*              (n' <= n)%nat /\ starN step (n - n')%nat c' σ'' (Halted m) σ'. *)
  (* Proof. *)
  (*   induction n; intros. *)
  (*   - inv H0. *)
  (*     + split; auto. *)
  (*     + inv H. inv H1. *)
  (*   - inv H. inv H0. *)
  (*     + split; try lia. *)
  (*       econstructor; eauto. *)
  (*     + assert (s0 = s2) by (eapply step_deterministic; eauto); subst s0. *)
  (*       assert (σ'0 = σ'1) by (eapply step_deterministic; eauto); subst σ'0. *)
  (*     generalize (IHn _ _ _ _ H3 _ _ _ H1). *)
  (*     intros [A B]. split; try omega. *)
  (*     replace (S n - S n0) with (n - n0) by omega. *)
  (*     assumption. *)
  (* Qed. *)

  Inductive val: Type :=
  | HaltedV: val
  | FailedV: val.

  Definition expr := ConfFlag.
  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => Halted
    | FailedV => Failed
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | Executable => None
    | Failed => Some FailedV
    | Halted => Some HaltedV
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

  Inductive prim_step: expr -> state -> list Empty_set -> expr -> state -> list expr -> Prop :=
  | PS_no_fork e σ o e' σ' :
        step (e, σ) (e', σ') → prim_step e σ o e' σ' [].
    (* fun e σ o e' σ' efs =>  step (e, σ) (e', σ'). *)

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs ->
      to_val e = None.
  Proof.
    intros. inversion H. inversion H0; eauto. (* by simpl.  *)
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

Definition get_addr_pointsto (w : Word) (conf : ExecConf) : option Word :=
  match w with
  | inl z => None
  | inr ((p,g),b,e,a) => Some (MemLocate (mem conf) a)
  end. 

Definition is_atomic (e : expr) (φ : state) : Prop :=
  match e,φ with
  | Halted,_ => True
  | Failed,_ => True
  | Executable,φ => ¬isCorrectPC (RegLocate (reg φ) PC) ∨
                (∃ w, get_addr_pointsto (RegLocate (reg φ) PC) φ
                      = Some w ∧ decode w = Halt) ∨
                (∃ w, get_addr_pointsto (RegLocate (reg φ) PC) φ
                      = Some w ∧ decode w = Fail)
  end.

(* Atomic is for all states, which does not really make sense in a machine where the 
   state determines whether there can be an atomic step to a value (i.e. the PC.) 
   rather than quantify over all states (which is pretty nonsensical), we should 
   restrict the definition to states where PC points to some value. 
   idea: change the definition of expr so that the executable flag connects a PC 
   value to the state. *)
Global Instance is_atomic_correct s (e : expr) :
  (forall φ, is_atomic e φ) ->  Atomic s e.
  Proof.
    intros Hσ; apply strongly_atomic_atomic.
    rewrite /Atomic. intros; simpl in *. destruct H.
    specialize Hσ with σ. 
    destruct e.
    - destruct Hσ.
      + inversion H; eauto.
        tauto. 
      + destruct H0.
        * destruct H0 as [w [Hs Hd]]. 
          inversion H; eauto.
          rewrite H3 in Hs. simpl in Hs. inversion Hs.
          rewrite H8 in H5. rewrite Hd in H5.
          rewrite <- H5 in H6. simpl in H6.  
          destruct H6. simpl. eauto.
        * destruct H0 as [w [Hs Hd]]. 
          inversion H; eauto.
          rewrite H3 in Hs. simpl in Hs. inversion Hs.
          rewrite H8 in H5. rewrite Hd in H5.
          rewrite <- H5 in H6. simpl in H6.  
          destruct H6. simpl. eauto.
    - destruct Hσ. rewrite /Atomic. intros; simpl in *.
      inversion H.
    - destruct Hσ. rewrite /Atomic. intros; simpl in *.
      inversion H. 
Defined.  

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


(* Require Coq.Logic.FunctionalExtensionality. *)

(* Section ExamplePrograms. *)

(*   Fixpoint make_prog_mem_aux (l: list instr) (k: Mem) (n: Z): Mem := *)
(*     match l with *)
(*     | nil => k *)
(*     | i::l => make_prog_mem_aux l (fun a => if addr_eq_dec a n then encode i else k a) (n + 1) *)
(*     end. *)

(*   Definition make_prog_mem (l: list instr): Mem := *)
(*     make_prog_mem_aux l (fun _ => inl 0%Z) 0. *)

(*   Definition R0 := R 0 eq_refl. *)

(*   Definition loop_mem: Mem := make_prog_mem [Jmp PC]. *)

(*   Definition init_reg: Reg := *)
(*     fun r => match r with *)
(*           | PC => inr ((RX, Global), 0%Z, None, 0%Z) *)
(*           | _ => inl 0%Z *)
(*           end. *)

(*   Definition loop_init_execconf : ExecConf := (init_reg, loop_mem). *)
(*   Definition loop_init_conf: Conf := Normal loop_init_execconf. *)

(*   Lemma loop_is_loop: *)
(*     forall n, starN step n loop_init_conf loop_init_execconf loop_init_conf loop_init_execconf. *)
(*   Proof. *)
(*     induction n; econstructor. *)
(*     - econstructor 2; eauto. *)
(*       simpl. econstructor 2; eauto. lia. *)
(*     - simpl. replace (loop_mem 0%Z) with (encode (Jmp PC)) by reflexivity. *)
(*       rewrite cap_lang.decode_encode_inv. simpl. *)
(*       unfold update_reg. simpl. *)
(*       assert ((fun x => if reg_eq_dec x PC then inr (RX, Global, 0%Z, None, 0%Z) else init_reg x) = init_reg). *)
(*       { apply FunctionalExtensionality.functional_extensionality. intros. *)
(*         destruct (reg_eq_dec x PC); auto. *)
(*         subst x. reflexivity. } *)
(*       rewrite H. exact IHn. *)
(*   Qed. *)

(* End ExamplePrograms. *)