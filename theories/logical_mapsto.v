From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import gmap excl agree.
From iris.algebra.lib Require Import excl_auth.
From stdpp Require Import sorting.
From cap_machine Require Export cap_lang iris_extra stdpp_extra machine_parameters.

Definition Version := nat.

Definition LAddr : Type := Addr * Version.
Inductive LSealable: Type :=
| LSCap: Perm -> Addr -> Addr -> Addr -> Version -> LSealable
| LSSealRange: SealPerms -> OType -> OType -> OType -> LSealable.

Inductive LWord: Type :=
| LWInt (z : Z)
| LWSealable (sb : LSealable)
| LWSealed: OType → LSealable → LWord.

Notation LCap p b e a v := (LWSealable (LSCap p b e a v)).
Notation LSealRange p b e a := (LWSealable (LSSealRange p b e a)).
Notation LSealedCap o p b e a v := (LWSealed o (LSCap p b e a v)).
Notation LInt z := (LWInt z).

Global Instance lword_inhabited: Inhabited LWord := populate (LInt 0).

Instance version_eq_dec : EqDecision Version.
Proof. solve_decision. Qed.
Instance lsealb_eq_dec : EqDecision LSealable.
Proof. solve_decision. Qed.
Instance lword_eq_dec : EqDecision LWord.
Proof. solve_decision. Qed.

Instance lsealable_countable : Countable LSealable.
Proof.
  set (enc := fun sb =>
       match sb with
       | LSCap p b e a v => inl (p,b,e,a,v)
       | LSSealRange p b e a => inr (p,b,e,a) end
      ).
  set (dec := fun e =>
       match e with
       | inl (p,b,e,a,v) => LSCap p b e a v
       | inr (p,b,e,a) => LSSealRange p b e a end
      ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

Instance lword_countable : Countable LWord.
Proof.
  set (enc := fun w =>
      match w with
      | LWInt z => inl z
      | LWSealable sb => inr (inl sb)
      | LWSealed x x0 => inr (inr (x, x0))
      end ).
  set (dec := fun e =>
      match e with
      | inl z => LWInt z
      | inr (inl sb) => LWSealable sb
      | inr (inr (x, x0)) => LWSealed x x0
      end ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Qed.

Ltac destruct_lword lw :=
  let z := fresh "z" in
  let p := fresh "p" in
  let b := fresh "b" in
  let e := fresh "e" in
  let a := fresh "a" in
  let v := fresh "v" in
  let o := fresh "o" in
  let sr := fresh "sr" in
  let sd := fresh "sd" in
  destruct lw as [ z | [p b e a v | p b e a] | o [p b e a v | p b e a]].

(* Setters and Getters lword and laddr *)

Definition sealable_to_lsealable (sb : Sealable) (v : Version) :=
  match sb with
  | SCap p b e a => LSCap p b e a v
  | SSealRange p b e a => LSSealRange p b e a
  end.

Definition lsealable_get_sealable (lsb : LSealable) : Sealable :=
  match lsb with
  | LSCap p b e a v => SCap p b e a
  | LSSealRange p ob oe oa => SSealRange p ob oe oa
  end.

Definition word_to_lword (w : Word) (v : Version) :=
  match w with
  | WInt z => LInt z
  | WSealable sb => LWSealable (sealable_to_lsealable sb v)
  | WSealed ot sb => LWSealed ot (sealable_to_lsealable sb v)
  end.

Definition lword_get_word (lw : LWord) : Word :=
  match lw with
  | LWInt z => WInt z
  | LWSealable lsb => WSealable (lsealable_get_sealable lsb)
  | LWSealed o lsb => WSealed o (lsealable_get_sealable lsb)
  end.

Definition lword_get_version (lw : LWord) : option Version :=
  match lw with
  | LCap _ _ _ _ v | (LSealedCap _ _ _ _ _ v) => Some v
  | _ => None
  end.
Definition laddr_get_addr (la : LAddr) := la.1.
Definition laddr_get_version (la : LAddr) := la.2.

Lemma laddr_inv la : (laddr_get_addr la, laddr_get_version la) = la.
Proof. destruct la ; auto. Qed.

Definition logical_region ( region : list Addr ) (v : Version) : list LAddr :=
  (fun a => (a,v)) <$> region.

Definition is_log_cap (lw : LWord) : bool :=
  match lw with
  | LCap _ _ _ _ _ => true
  | _ => false
  end.

Lemma is_log_cap_is_cap_true_iff (lw : LWord) : is_log_cap lw = true <-> is_cap (lword_get_word lw) = true.
Proof.
  split; intros
  ; destruct lw; cbn in *; try congruence
  ; destruct sb; cbn in *; try congruence.
Qed.

Lemma is_log_cap_is_cap_false_iff (lw : LWord) : is_log_cap lw = false <-> is_cap (lword_get_word lw) = false.
Proof.
  split; intros
  ; destruct lw; cbn in *; try congruence
  ; destruct sb; cbn in *; try congruence.
Qed.

Class ReservedAddresses :=
  ReservedAddressesG {
      reserved_addresses : list Addr;
      init_version : Version
  }.

Definition VMap : Type := gmap Addr Version.
Definition LReg := gmap RegName LWord.
Definition LMem := gmap LAddr LWord.
Definition LDFrac := gmap LAddr iris.algebra.dfrac.dfrac.


Section Logical_mapsto.
  Context `{ reservedaddresses : ReservedAddresses}.

Definition lreg_strip (lr : LReg) : Reg :=
 (fun lw : LWord => lword_get_word lw) <$> lr.

Definition is_cur_addr (la : LAddr) (vmap : VMap) : Prop :=
  vmap !! la.1 = Some la.2. (* check whether the version of `la` matches in cur_map *)

Definition is_cur_word (lw : LWord) (vmap : VMap) : Prop :=
  match lw with
  | LCap _ b e _ v | LSealedCap _ _ b e _ v =>
      forall a, a ∈ finz.seq_between b e -> (vmap !! a = Some v)
  | _ => True
  end.

Definition is_cur_regs (lr : LReg) (vmap : VMap) : Prop :=
  map_Forall (λ _ lw, is_cur_word lw vmap) lr.

Lemma is_cur_regs_mono {lr1 lr2 vmap} :
  lr1 ⊆ lr2 -> is_cur_regs lr2 vmap -> is_cur_regs lr1 vmap.
Proof.
  intros Hsubset.
  rewrite <- (map_subseteq_union _ _ Hsubset).
  now apply map_Forall_union_1_1.
Qed.

Global Instance is_cur_addr_dec (la : LAddr) (vmap : VMap) :
  Decision (is_cur_addr la vmap).
Proof.
  rewrite /is_cur_addr.
  destruct (vmap !! la.1) eqn:Heq; solve_decision.
Defined.

Lemma is_cur_addr_same (a : Addr) (v v' : Version) (vmap : VMap) :
  is_cur_addr (a, v) vmap ->
  is_cur_addr (a, v') vmap ->
  v = v'.
Proof.
  rewrite /is_cur_addr /=.
  move=> Hcur_a Hcur_a'.
  by rewrite Hcur_a in Hcur_a' ; simplify_eq.
Qed.

Definition get_wlcap_slcap : LWord -> option (Perm * Addr * Addr * Addr * Version) :=
  fun lw => match lw with
            | LCap p b e a v | LWSealed _ (LSCap p b e a v) => Some (p, b, e, a, v)
            | _ => None
            end.

Definition is_lword_version (lw : LWord) (p : Perm) (b e a : Addr) (v : Version) : Prop :=
  (get_wlcap_slcap lw) = Some (p, b, e, a, v).

Lemma is_lword_inv (lw : LWord) (p : Perm) (b e a : Addr) (v : Version) :
  is_lword_version lw p b e a v ->
  (exists o, lw = LSealedCap o p b e a v)  \/ lw = LCap p b e a v.
Proof.
  intros Hversion.
  destruct_lword lw; cbn in Hversion ; try done
  ; rewrite /is_lword_version /= in Hversion; simplify_eq
  ; [right | left ; eexists]; done.
Qed.

Lemma cur_lword_cur_addr lw p b e a (v : Version) (vmap : VMap):
  is_lword_version lw p b e a v ->
  is_cur_word lw vmap →
  withinBounds b e a = true →
  is_cur_addr (a,v) vmap.
Proof.
  intros Hlword Hcur_lw Hbounds.
  unfold is_cur_addr ; simpl.
  rewrite /is_cur_word /= in Hcur_lw.
  apply is_lword_inv in Hlword.
  destruct Hlword as [[o ?]| ?] ; subst
  ; apply withinBounds_true_iff, elem_of_finz_seq_between in Hbounds
  ; by apply Hcur_lw.
Qed.

Lemma is_cur_lword_lea
  (vmap : VMap) (p p' : Perm) (b b' e e' a a' : Addr) (v : Version) (lw lw' : LWord) :
  isWithin b' e' b e ->
  get_wlcap_slcap lw = Some (p, b, e, a, v) ->
  get_wlcap_slcap lw' = Some (p', b', e', a', v) ->
  is_cur_word lw vmap ->
  is_cur_word lw' vmap.
Proof.
  intros Hlw Hlw'.
  destruct_lword lw ; destruct_lword lw' ; cbn in * ; simplify_eq
  ; rewrite /is_cur_word; intros Hcur; auto ; simplify_eq.
  all: intros Hin a0 Ha0in ; apply Hin.
  all: rewrite !elem_of_finz_seq_between in Ha0in |- *.
  all: apply Is_true_true in Hlw; apply isWithin_implies in Hlw; solve_addr.
Qed.

Lemma is_cur_addr_insert_ne
  (vmap : VMap) (a a' : Addr) (v v' : Version) :
  a ≠ a' ->
  is_cur_addr (a,v) vmap ->
  is_cur_addr (a,v) (<[a' := v']> vmap).
Proof.
  intros Hneq Hcur.
  rewrite /is_cur_addr /= in Hcur |- *.
  by simplify_map_eq.
Qed.

Lemma is_cur_addr_insert
  (vmap : VMap) (a : Addr) (v : Version) :
  is_cur_addr (a,v) (<[a := v]> vmap).
Proof.
  rewrite /is_cur_addr //=.
  by simplify_map_eq.
Qed.

Lemma insert_reg_lreg_strip (lregs : LReg) (r : RegName) (lw : LWord) :
  lregs !! r = Some lw ->
  <[ r := lword_get_word lw ]> (lreg_strip lregs) = lreg_strip lregs.
Proof.
  intros Hr.
  rewrite -/lreg_strip -fmap_insert insert_id //.
Qed.

Definition next_version_lword (lw : LWord ) : LWord :=
  match lw with
  | LCap p b e a v => LCap p b e a (v+1)
  | LSealedCap ot p b e a v => LSealedCap ot p b e a (v+1)
  | _ => lw
  end.

Lemma lword_get_word_next_version (lw : LWord):
  lword_get_word (next_version_lword lw) = lword_get_word lw.
Proof.
  by destruct_lword lw; cbn.
Qed.

(** The `reg_phys_log_corresponds` states that, the physical register file `phr` corresponds
    to the the logical register file `lr`, according to the view map `vmap` if:
    - the content of the register `phr` is the same as the words in `lr` w/o the version
    - the version of the capabilities in `lr` are the same as the version of its addresses
      in the view map `vmap`
 *)
Definition reg_phys_log_corresponds (phr : Reg) (lr : LReg) (vmap : VMap) :=
    lreg_strip lr = phr ∧ is_cur_regs lr vmap.

Definition is_legal_address (lm : LMem) vmap la : Prop :=
  ∃ cur_v,
        is_cur_addr (laddr_get_addr la, cur_v) vmap
        ∧ laddr_get_version la <= cur_v
        /\ is_Some ( lm !! (laddr_get_addr la, cur_v)).

(** for each logical address in the logical memory,
    - the version is less than or equal to the current version of the address
    - the current version of the address also exists in the logical memory *)
Definition mem_current_version (lm : LMem) (vmap : VMap) : Prop :=
  map_Forall (λ la _ , is_legal_address lm vmap la) lm.

(** for all entries in the view/curr map,
    - there exists a logical word `lw` in the logical memory `lm`
      ( i.e. dom(vmap) ⊆ dom(lm) ) s.t.
    - the logical word `lw` corresponds to the actual word in the physical memory `phm`
      for the same address
    - the logical word `lw` is the current view of the word *)
Definition mem_vmap_root (phm : Mem) (lm : LMem) (vmap : VMap) : Prop :=
  map_Forall
    (λ a v,
      ∃ lw,
        lm !! (a,v) = Some lw
        ∧ phm !! a = Some (lword_get_word lw)
        ∧ is_cur_word lw vmap)
    vmap. (* subset in other direction, and every current address is gc root *)

Definition mem_gcroot (vmap : VMap) : Prop :=
  map_Forall (λ a v, a ∈ reserved_addresses → v = init_version ) vmap.

Definition mem_phys_log_corresponds (phm : Mem) (lm : LMem) (vmap : VMap) :=
  (mem_current_version lm vmap) ∧ (mem_vmap_root phm lm vmap) ∧ (mem_gcroot vmap).

Definition state_phys_log_corresponds
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap):=
  reg_phys_log_corresponds phr lr vmap ∧ mem_phys_log_corresponds phm lm vmap.

(* Lemmas about lreg_corresponds *)

Lemma lreg_corresponds_read_iscur
  (phr : Reg) (lr : LReg) (vmap : VMap) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr vmap →
  lr !! r = Some lw →
  is_cur_word lw vmap.
Proof.
  intros [_ Hcur_regs] Hr.
  destruct_lword lw; try done; eapply map_Forall_lookup_1 in Hr; eauto; done.
Qed.

Lemma lreg_corresponds_get_word
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (r : RegName) (lw : LWord) :
  reg_phys_log_corresponds phr lr vmap  ->
  lr !! r = Some lw ->
  phr !! r = Some (lword_get_word lw).
Proof.
  intros [<- Hcurreg] Hlr.
  apply lookup_fmap_Some.
  eexists; eauto.
Qed.

Lemma lreg_corresponds_insert_respects
  (phr : Reg) (lr : LReg) (vmap : VMap) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr vmap →
  is_cur_word lw vmap →
  reg_phys_log_corresponds (<[r := lword_get_word lw]> phr) (<[r := lw]> lr) vmap.
Proof.
  intros [Hstrip Hcur_regs] Hlw.
  split.
  - rewrite <- Hstrip.
    unfold lreg_strip.
    by rewrite fmap_insert.
  - apply map_Forall_insert_2; auto.
Qed.

Lemma lreg_corresponds_delete
  (phr : Reg) (lr : LReg) (vmap : VMap) (src : RegName) :
  reg_phys_log_corresponds phr lr vmap ->
  reg_phys_log_corresponds (delete src phr) (delete src lr) vmap.
Proof.
  intros [Hstrip Hcur].
  split.
  - by rewrite /lreg_strip fmap_delete -/(lreg_strip lr) Hstrip.
  - apply map_Forall_lookup_2.
    intros r lw Hr.
    destruct (decide (r = src)); subst.
    rewrite lookup_delete in Hr; congruence.
    rewrite lookup_delete_ne in Hr; eauto.
Qed.

Lemma lreg_corresponds_cap_cur_word_1
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (lw : LWord) (p : Perm) (b e a : Addr) (la : LAddr) (r : RegName):
  reg_phys_log_corresponds phr lr vmap ->
  lword_get_word lw = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lw ->
  lword_get_version lw = Some (laddr_get_version la) -> is_cur_addr la vmap.
Proof.
  intros [_ Hcur_regs] Hlcap Hla Hbounds Hr Hv; cbn in *.
  destruct_lword lw; cbn in *; try congruence.
  simplify_eq.
  eapply map_Forall_lookup_1 in Hcur_regs ; last eauto; clear Hr.
  cbn in *.
  destruct la as [a v]; cbn in *.
  apply Hcur_regs; cbn.
  by apply withinBounds_in_seq.
Qed.

Lemma lreg_corresponds_cap_cur_word_2
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (lw : LWord) (p : Perm) (b e a : Addr) (la : LAddr) (r : RegName):
  reg_phys_log_corresponds phr lr vmap ->
  lword_get_word lw = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lw ->
  is_cur_addr la vmap -> lword_get_version lw = Some (laddr_get_version la).
Proof.
  intros [Hstrip Hcur_regs] Hlr Hla Hinbounds Hr Hcur_la.
  eapply map_Forall_lookup_1 in Hcur_regs; eauto.
  unfold is_cur_word in Hcur_regs.
  destruct_lword lw; simplify_eq ; cbn in Hlr; simplify_eq; cbn in *.
  apply withinBounds_in_seq in Hinbounds.
  apply Hcur_regs in Hinbounds.
  unfold is_cur_addr in Hcur_la.
  destruct la ; cbn in *; congruence.
Qed.

Lemma lreg_corresponds_cap_cur_word
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (lw : LWord) (p : Perm) (b e a : Addr) (la : LAddr) (r : RegName):
  reg_phys_log_corresponds phr lr vmap ->
  lword_get_word lw = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lw ->
  (lword_get_version lw = Some (laddr_get_version la) <-> is_cur_addr la vmap).
Proof.
  intros HInvReg Hlr Hla Hinbounds Hr.
  split ; intros
  ; [ eapply lreg_corresponds_cap_cur_word_1
    | eapply lreg_corresponds_cap_cur_word_2 ]
  ; eauto.
Qed.

Lemma lreg_corresponds_correct_PC
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (lw : LWord) (p : Perm) (b e a : Addr) (la : LAddr) (r : RegName):
  reg_phys_log_corresponds phr lr vmap ->
  lword_get_word lw = WCap p b e a ->
  laddr_get_addr la = a ->
  isCorrectPC (WCap p b e a) ->
  lr !! r = Some lw ->
  lword_get_version lw = Some (laddr_get_version la) ->
  is_cur_addr la vmap.
Proof.
  intros HinvReg Hlw Hla Hvpc Hr Hv; cbn in *.
  apply isCorrectPC_withinBounds in Hvpc.
  eapply lreg_corresponds_cap_cur_word ; eauto.
Qed.

Lemma lreg_corresponds_cap_is_cur
  (phr : Reg) (lr : LReg) (vmap : VMap)
  (src : RegName) (p : Perm)  (b e a a' : Addr) (v : Version) :
  reg_phys_log_corresponds phr lr vmap  ->
  lr !! src = Some (LCap p b e a v) ->
  a' ∈ finz.seq_between b e ->
  is_cur_addr (a', v) vmap.
Proof.
  move=> Hreg_inv Hlr_src Ha'.
  eapply lreg_corresponds_read_iscur in Hlr_src; eauto.
  eapply is_cur_lword_lea with (lw' := LCap p b e a' v) in Hlr_src; eauto.
  apply withinBounds_in_seq_2 in Ha'.
  eapply cur_lword_cur_addr; eauto.
  rewrite /is_lword_version //=.
  by apply isWithin_refl.
Qed.

(* Lemmas about lmem_corresponds *)
Lemma lmem_corresponds_read_iscur
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm vmap →
  is_cur_addr la vmap →
  lm !! la = Some lw →
  is_cur_word lw vmap.
Proof.
  intros (Hdom & Hroot & _) Hla Hlw.
  rewrite /is_cur_addr in Hla.
  eapply map_Forall_lookup_1 in Hla; eauto; cbn in Hla.
  destruct Hla as (lw' & Hlw' & Hphm & Hcur_lw').
  destruct la as [a v]; cbn in *.
  by rewrite Hlw in Hlw'; simplify_eq.
Qed.

Lemma lmem_corresponds_insert_respects
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm vmap →
  is_cur_addr la vmap →
  is_cur_word lw vmap →
  mem_phys_log_corresponds
    (<[laddr_get_addr la := lword_get_word lw]> phm)
    (<[la := lw]> lm) vmap.
Proof.
  intros (Hdom & Hroot & Hgcroot) Hla Hlw.
  split; [|split].
  - apply map_Forall_insert_2; auto.
    exists (laddr_get_version la). rewrite laddr_inv.
    do 2 (split; auto). by simplify_map_eq.
    eapply map_Forall_impl; eauto.
    intros la' lw' H ; simpl in H.
    destruct H as (cur_v & H1 & H2 & H3).
    exists cur_v. do 2 (split; auto).
    destruct (decide (la = (laddr_get_addr la', cur_v))); by simplify_map_eq.

  - eapply map_Forall_lookup.
    intros a' v' Hp ; cbn in *.
    pose proof (Hp' := Hp).

    eapply (map_Forall_lookup_1 _ _ _ _ Hroot) in Hp'; eauto ; cbn in Hp'.
    destruct Hp' as (lw' & Hlw' & Hw' & Hcur_lw').
    destruct la as [a v].
    rewrite /is_cur_addr /= in Hla.

    destruct (decide (a' = a)) as [Heq | Hneq]; simplify_eq.
    + exists lw. eapply is_cur_addr_same in Hp; last eapply Hla.
      split ; [ by simplify_map_eq|].
      split ; [ by simplify_map_eq|].
      auto; cbn ;by simplify_map_eq.
    + exists lw'.
      split; [rewrite lookup_insert_ne; auto ; intro; simplify_pair_eq|].
      split; by simplify_map_eq.

  - auto.
Qed.

Lemma lmem_corresponds_get_word
  (phm : Mem) (lm : LMem) (vmap : VMap)
  (a : Addr) (v : Version) (lw : LWord) :
  mem_phys_log_corresponds phm lm vmap  ->
  is_cur_addr (a,v) vmap ->
  lm !! (a, v) = Some lw ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros (Hdom & Hroot & _) Hcur Hlm.
  eapply map_Forall_lookup_1 in Hdom; eauto; cbn in Hdom.
  destruct Hdom as (cur_v & Hcur_addr & Hle_cur & Hsome).
  rewrite /is_cur_addr /= in Hcur, Hcur_addr; simplify_eq.
  eapply map_Forall_lookup_1 in Hroot; eauto.
  destruct Hroot as (lw' & Hlm' & Hpm' & Hcurword).
  by rewrite Hlm in Hlm'; simplify_map_eq.
Qed.

Lemma lmem_corresponds_current_word
  (phm : Mem) (lm : LMem) (vmap : VMap)
  (a : Addr) (v : Version) (lw : LWord) :
  mem_phys_log_corresponds phm lm vmap  ->
  lm !! (a, v) = Some lw ->
  is_cur_addr (a,v) vmap ->
  is_cur_word lw vmap.
Proof.
  intros (Hdom & Hroot & _) Hlm Hcur.
  eapply map_Forall_lookup_1 in Hdom; eauto; cbn in Hdom.
  destruct Hdom as (cur_v & Hcur_addr & Hle_cur & Hsome).
  rewrite /is_cur_addr /= in Hcur, Hcur_addr; simplify_eq.
  eapply map_Forall_lookup_1 in Hroot; eauto.
  destruct Hroot as (lw' & Hlm' & Hpm' & Hcurword).
  by rewrite Hlm in Hlm'; simplify_map_eq.
Qed.

(* Lemmas about state_corresponds *)

Lemma state_corresponds_reg_get_word
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (r : RegName) (lw : LWord):
  state_phys_log_corresponds phr phm lr lm vmap  ->
  lr !! r = Some lw ->
  phr !! r = Some (lword_get_word lw).
Proof.
  intros [Hreg _] ? ; eapply lreg_corresponds_get_word ; eauto.
Qed.

Lemma state_corresponds_reg_get_word_cap
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (r : RegName) (p : Perm) (b e a : Addr) (v : Version):
  state_phys_log_corresponds phr phm lr lm vmap  ->
  lr !! r = Some (LCap p b e a v) ->
  phr !! r = Some (WCap p b e a).
Proof.
  intros HLinv Hlr.
  rewrite -/(lword_get_word (LCap p b e a v)).
  eapply state_corresponds_reg_get_word ; eauto.
Qed.

Lemma state_corresponds_mem_get_word
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (a : Addr) (v : Version) (lw : LWord):
  state_phys_log_corresponds phr phm lr lm vmap  ->
  is_cur_addr (a,v) vmap ->
  lm !! (a, v) = Some lw ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [_ Hmem] ? ? ; eapply lmem_corresponds_get_word ; eauto.
Qed.

Lemma state_corresponds_cap_cur_word
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (lw : LWord) (p : Perm) (b e a : Addr) (la : LAddr) (r : RegName):
  state_phys_log_corresponds phr phm lr lm vmap ->
  lword_get_word lw = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lw ->
  (lword_get_version lw = Some (laddr_get_version la) <-> is_cur_addr la vmap).
Proof.
  intros [HinvReg _] Hlw Hla Hbounds Hr; cbn in *.
  eapply lreg_corresponds_cap_cur_word; eauto.
Qed.

Lemma state_corresponds_mem_correct_PC
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (p : Perm) (b e a : Addr) (v : Version) (r : RegName) (lw : LWord) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  isCorrectPC (WCap p b e a) ->
  lr !! r = Some (LCap p b e a v) ->
  lm !! (a,v) = Some lw ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros * HLinv Hvpc Hlr Hlm.
  eapply state_corresponds_mem_get_word; eauto.
  destruct HLinv as [ HinvReg _ ].
  eapply lreg_corresponds_correct_PC; eauto; by cbn.
Qed.

Lemma state_corresponds_cap_all_current
  (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (vmap : VMap)
  (src : RegName) (lwsrc : LWord) (p : Perm) (b e a : Addr) (v : Version) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  lr !! src = Some lwsrc ->
  Forall (λ a0 : Addr, vmap !! a0 = Some v) (finz.seq_between b e).
Proof.
  move=> [ [_ Hcur_regs] Hmem_inv] Hget_lw Hlr_src.
  assert (is_cur_word lwsrc vmap) as Hcur_src
      by (eapply map_Forall_lookup_1 in Hcur_regs; eauto).
  destruct_lword lwsrc ; cbn in * ; simplify_eq.
  all: by eapply Forall_forall.
Qed.

Lemma state_corresponds_last_version_lword_region
  (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (vmap : VMap)
  (p : Perm) (b e a : Addr) (v : Version) (src : RegName) (lwsrc : LWord) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  lr !! src = Some lwsrc ->
  Forall (λ a0 : Addr, lm !! (a0, v+1) = None) (finz.seq_between b e).
Proof.
  move=> [ [_ Hcur_regs] Hmem_inv] Hget Hlr_src.
  assert (is_cur_word lwsrc vmap) as Hcur_src
      by (eapply map_Forall_lookup_1 in Hcur_regs; eauto).
  apply Forall_forall.
  intros a0 Ha0_inbounds.
  destruct_lword lwsrc ; cbn in * ; simplify_eq.
  all: apply Hcur_src in Ha0_inbounds.
  all: assert (is_cur_addr (a0, v) vmap) as Hcur_a0 by done.
  all: destruct (lm !! (a0, v + 1)) eqn:Hv' ; [|done].
  all: destruct Hmem_inv as (Hroot & Hcur & _).
  all: eapply map_Forall_lookup_1 in Hroot; eauto.
  all: destruct Hroot as (cur_v & Hcur_v & cur & Hsome & Hmaxv); cbn in *.
  all: eapply map_Forall_lookup_1 in Hcur; eauto.
  all: destruct Hcur as (lw & Hlm & _) ; cbn in *.
  all: eapply is_cur_addr_same in Hcur_a0; eauto; simplify_eq; lia.
Qed.

Lemma state_corresponds_access_lword_region
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord) (p : Perm) (b e a : Addr) (v : Version) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  lr !! src = Some lwsrc ->
  (Forall (λ a' : Addr, is_Some (lm !! (a', v))) (finz.seq_between b e)).
Proof.
  intros [ [_ ?] [? [ ? _ ] ] ] Hget Hlsrc.
  eapply map_Forall_lookup_1 in Hlsrc; eauto; cbn in Hlsrc.
  eapply Forall_forall.
  intros a' Ha'.
  destruct_lword lwsrc ; cbn in * ; simplify_eq.
  all: eapply Hlsrc in Ha'.
  all: eapply map_Forall_lookup_1 in Ha'; eauto; cbn in Ha'.
  all: destruct Ha' as (? & ? & _).
  all: eexists ; eauto.
Qed.



(** Machinery for word access and unique_in_machine *)

Definition word_access_addr (a : Addr) (w : Word) : Prop :=
  match get_scap w with
  | Some (SCap _ b e _) => (b <= a < e)%a
  | _ => False
  end.

Definition word_access_addrL (a : Addr) (lw : LWord) : Prop :=
  word_access_addr a (lword_get_word lw).

Lemma update_cur_word
  (lm : LMem) (vmap: VMap) (a : Addr) (v : Version) (lw : LWord) :
  ¬ word_access_addrL a lw ->
  is_cur_word lw vmap ->
  is_cur_word lw ( <[a := v]> vmap ).
Proof.
  intros Hnaccess Hcur.
  destruct_lword lw ; auto; cbn in *; intros * Ha1.
  all: assert (a1 <> a) by (apply elem_of_finz_seq_between in Ha1; solve_addr).
  all: apply Hcur in Ha1.
  all: by simplify_map_eq.
Qed.

(* Update version number of a memory region *)

(* For all the content of a logical memory `lm`,
   no current logical address has a lword that can access the address `a`.

   Put another way, the "current view" of the memory cannot access `a`.
 *)
Definition lmem_not_access_addrL (lm : LMem) (vmap : VMap) (a : Addr) : Prop :=
  map_Forall
  (λ (la : LAddr) (lw : LWord),
    is_cur_addr la vmap → (¬ word_access_addrL a lw)
  ) lm.

(** Sweep in logical memory *)
Definition overlap_wordL (lw1 lw2 : LWord) : Prop :=
  (overlap_word (lword_get_word lw1) (lword_get_word lw2)).

Global Instance overlap_wordL_dec (lw1 lw2 : LWord) : Decision (overlap_wordL lw1 lw2).
Proof. solve_decision. Defined.

Lemma not_overlap_wordL_seq_between
  (p p' : Perm) (b b' e e' a a' : Addr) (v v' : Version) (lw lw' : LWord) :
  get_wlcap_slcap lw = Some (p, b, e, a, v) ->
  get_wlcap_slcap lw' = Some (p', b', e', a', v') ->
  ¬ overlap_wordL lw lw' ->
  (forall a0, a0 ∈ finz.seq_between b' e' -> a0 ∉ finz.seq_between b e).
Proof.
  move=> Hget_lw Hget_lw' Hnot_overlap a0 Ha_in Ha_in'.
  apply Hnot_overlap.
  rewrite /overlap_wordL /= /overlap_word /=.
  destruct_lword lw ; destruct_lword lw' ; cbn in * ; simplify_eq.
  all: apply elem_of_finz_seq_between in Ha_in, Ha_in'.
  all: destruct (b <? b')%a eqn:Hb; solve_addr.
Qed.


(* No register except `src` contains `lwsrc` *)
Definition unique_in_registersL (lregs : LReg) (osrc : option RegName) (lwsrc : LWord) : Prop :=
  match osrc with
  | Some src =>
    (map_Forall
       (λ (r : RegName) (lwr : LWord),
         if decide (r = src) then True else ¬ overlap_wordL lwsrc lwr)
       lregs)
  | None => map_Forall (λ _ lwr, ¬ overlap_wordL lwsrc lwr) lregs
  end.

Global Instance unique_in_registersL_dec (lregs : LReg) (osrc : option RegName) (lwsrc : LWord)
  : Decision (unique_in_registersL lregs osrc lwsrc).
Proof.
  destruct osrc as [rn|].
  - apply map_Forall_dec.
    move=> r rw.
    case_decide; solve_decision.
  - apply map_Forall_dec. move=>r rw. solve_decision.
Defined.

(* Returns [true] if [r] is unique. *)
Definition unique_in_memoryL (lmem : LMem) (vmap : VMap) (lwsrc : LWord) : Prop :=
  (map_Forall
     (λ (la : LAddr) (lwa : LWord),
       is_cur_addr la vmap -> ¬ overlap_wordL lwsrc lwa)
     lmem).

Global Instance unique_in_memoryL_dec (lmem : LMem) (vmap : VMap) (lwsrc : LWord) :
  Decision (unique_in_memoryL lmem vmap lwsrc).
Proof.
  apply map_Forall_dec.
  move=> la lwa.
  apply impl_dec; solve_decision.
Defined.

Definition unique_in_machineL
    (lregs : LReg) (lmem : LMem) (vmap : VMap) (src : RegName) (lwsrc : LWord) :=
  lregs !! src = Some lwsrc ->
  unique_in_registersL lregs (Some src) lwsrc /\ unique_in_memoryL lmem vmap lwsrc.


Lemma unique_in_registersL_mono
  (lregs lr : LReg) (src : RegName) (lwsrc : LWord) :
  lregs ⊆ lr ->
  unique_in_registersL lr (Some src) lwsrc ->
  unique_in_registersL lregs (Some src) lwsrc.
Proof.
  intros Hincl Hunique.
  rewrite /unique_in_registersL in Hunique |- *.
  eapply map_Forall_lookup.
  intros r lw Hlregs_r.
  case_decide as Hr ; simplify_eq; first done.
  eapply lookup_weaken in Hlregs_r ; eauto.
  eapply map_Forall_lookup in Hlregs_r ; eauto.
  rewrite /= decide_False // in Hlregs_r.
Qed.

Lemma unique_in_machineL_insert_reg
  (lr : LReg) (lm : LMem)  (vmap : VMap)
  (src r: RegName) (lwsrc lwr : LWord) :
  r <> src ->
  lr !! src = Some lwsrc ->
  ¬ overlap_wordL lwsrc lwr ->
  unique_in_machineL lr lm vmap src lwsrc ->
  unique_in_machineL (<[r := lwr ]> lr) lm vmap src lwsrc.
Proof.
  move=> Hr_neq_src Hlr_src Hlr_r Hunique.
  specialize (Hunique Hlr_src).
  move: Hunique => [Hunique_reg Hunique_src] _.
  split; last done.
  apply map_Forall_insert_2; last done.
  case_decide; auto.
Qed.

Lemma unique_in_machineL_not_overlap_word
  (lr : LReg) (lm : LMem) (vmap : VMap)
  (src r : RegName) (lwsrc lwr : LWord) :
  r ≠ src ->
  lr !! src = Some lwsrc ->
  lr !! r = Some lwr ->
  unique_in_machineL lr lm vmap src lwsrc ->
  ¬ overlap_wordL lwsrc lwr.
Proof.
  move=> Hr_neq_src Hlr_src Hlr_r Hunique.
  specialize (Hunique Hlr_src).
  move: Hunique => [Hunique_reg _].
  eapply map_Forall_lookup_1 in Hunique_reg; eauto.
  by case_decide; simplify_eq.
Qed.

Lemma state_corresponds_unique_in_registers
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord):
  state_phys_log_corresponds phr phm lr lm vmap ->
  lr !! src = Some lwsrc ->
  unique_in_registers phr (lword_get_word lwsrc) (Some src) ->
  unique_in_registersL lr (Some src) lwsrc.
Proof.
  move=> [Hreg_inv Hmem_inv] Hlr_src Hunique.
  eapply map_Forall_lookup_2.
  move=> r lwr Hlr_r.
  assert (Hphr_r : phr !! r = Some (lword_get_word lwr))
    by (by eapply state_corresponds_reg_get_word).
  eapply map_Forall_lookup_1 in Hphr_r; eapply Hunique ; cbn in Hphr_r.
  destruct (decide (r = src)) ; simplify_eq ; auto.
  rewrite Hlr_src in Hlr_r; simplify_eq ; by eapply state_corresponds_reg_get_word.
  by eapply state_corresponds_reg_get_word.
Qed.

Lemma state_corresponds_unique_in_memory
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord):
  state_phys_log_corresponds phr phm lr lm vmap ->
  lr !! src = Some lwsrc ->
  unique_in_memory phm (lword_get_word lwsrc) None ->
  unique_in_memoryL lm vmap lwsrc.
Proof.
  move=> [Hreg_inv Hmem_inv] Hlr_src Hunique.
  eapply map_Forall_lookup_2.
  move=> [a v] lw_la Hlm_la His_cur_la.
  assert (Hphm_a : phm !! a = Some (lword_get_word lw_la))
    by (by eapply lmem_corresponds_get_word).
  pose proof Hphm_a as H'phm_a.
  eapply map_Forall_lookup_1 in Hphm_a; eapply Hunique ; cbn in Hphm_a; eauto.
Qed.

(* link between
   sweep of the physical machine
   and unique_in_machine of logical memory *)
Lemma sweep_true_specL
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord):
  state_phys_log_corresponds phr phm lr lm vmap →
  lr !! src = Some lwsrc →
  sweep_reg phm phr src = true →
  unique_in_machineL lr lm vmap src lwsrc.
Proof.
  intros HLinv Hlr_src Hsweep.
  assert (Hphr_src : phr !! src = Some (lword_get_word lwsrc))
    by (by eapply state_corresponds_reg_get_word).
  apply sweep_reg_spec with (wsrc := (lword_get_word lwsrc)) in Hsweep ; auto.
  specialize (Hsweep Hphr_src).
  destruct Hsweep as [Hunique_reg Hunique_mem].
  intros _.
  split ;
    [ eapply state_corresponds_unique_in_registers
    | eapply state_corresponds_unique_in_memory ]
  ; eauto.
Qed.

Lemma no_overlap_word_no_access_addrL
  (p : Perm) (b e a a' : Addr) (v : Version) (lw : LWord):
  a' ∈ finz.seq_between b e ->
  ¬ overlap_wordL (LCap p b e a v) lw ->
  ¬ word_access_addrL a' lw.
Proof.
  move=> Ha' Hno_overlap Haccess.
  apply Hno_overlap.
  rewrite /word_access_addrL /word_access_addr /= in Haccess.
  rewrite /overlap_wordL /overlap_word /=.
  destruct (get_scap (lword_get_word lw)); last done.
  destruct s as [p0 b0 e0 a0|] ; last done.
  apply elem_of_finz_seq_between in Ha'.
  destruct (b <? b0)%a ; solve_addr.
Qed.

Lemma unique_in_machine_no_accessL
  (phm : Mem) (lm : LMem) (lr : LReg) (vmap : VMap)
  (p : Perm) (b e a : Addr) ( v : Version ) (src : RegName) (lw : LWord) :
  mem_phys_log_corresponds phm lm vmap ->
  get_wlcap_slcap lw = Some (p, b, e, a, v) ->
  lr !! src = Some lw ->
  is_cur_word lw vmap ->
  unique_in_machineL lr lm vmap src lw ->
  Forall (λ a' : Addr, lmem_not_access_addrL lm vmap a') (finz.seq_between b e).
Proof.
  move=> Hmem_inv Hlw Hlr_src His_cur Hunique.
  apply Forall_forall; move=> a' Ha'.
  destruct_lword lw ; cbn in Hlw ; simplify_eq.
  1: assert (is_cur_word (LCap p b e a' v) vmap)
    by (eapply is_cur_lword_lea with (lw := LCap p b e a v); eauto; apply isWithin_refl).
  2: assert (is_cur_word (LSealedCap o p b e a' v) vmap)
    by (eapply is_cur_lword_lea with (lw := LCap p b e a v); eauto; apply isWithin_refl).
  all: assert (Hcur_a': is_cur_addr (a',v) vmap).
  1: { eapply cur_lword_cur_addr; [|eauto|].
    by rewrite /is_lword_version.
    by apply withinBounds_in_seq.
  }
  2: { eapply cur_lword_cur_addr; [|eauto|].
       by rewrite /is_lword_version.
       by apply withinBounds_in_seq.
  }
  all: rewrite /unique_in_machineL in Hunique.
  all: specialize (Hunique Hlr_src).
  all: destruct Hunique as [Hunique_reg Hunique_mem].
  all: eapply map_Forall_impl ; first eapply Hunique_mem.
  all: move=> [a0 v0] lw0 Hlast_v Hcur_v0.
  all: eapply no_overlap_word_no_access_addrL ; eauto.
  all: eapply Hlast_v.
  all: eapply mem_corresponds_cur_addr_last_version_1; eauto.
  Unshelve. all: eauto.
Qed.

Lemma unique_in_registersL_twice
  (rcode rdata : RegName) (lregs : LReg)
  p b e a v
  p' b' e' a' v' :
  rcode ≠ rdata ->
  lregs !! rcode = Some (LCap p b e a v) ->
  lregs !! rdata = Some (LCap p' b' e' a' v') ->
  unique_in_registersL lregs (Some rcode) (LCap p b e a v) ->
  unique_in_registersL lregs (Some rdata) (LCap p' b' e' a' v') ->
  (finz.seq_between b e) ## (finz.seq_between b' e').
Proof.
  intros Hneq Hrcode Hrdata Hunique_code Hunique_data.
  rewrite /unique_in_registersL in Hunique_code.
  rewrite /unique_in_registersL in Hunique_data.
  eapply map_Forall_lookup_1 in Hunique_code; last eapply Hrdata.
  eapply map_Forall_lookup_1 in Hunique_data; last eapply Hrcode.
  rewrite decide_False // in Hunique_code.
  rewrite decide_False // in Hunique_data.
  rewrite /overlap_wordL /overlap_word /= in Hunique_code, Hunique_data.
  intros x Hx Hx'.
  rewrite !elem_of_finz_seq_between in Hx, Hx'.
  destruct ((b <? b')%a) eqn:Hbb'; solve_finz.
Qed.
(** Machinery to update the lmemory *)

(** Machinery to update the memory for a given version,
    without knowing the view map *)

(* Update the lmemory for the address a.
   Note that llmem might not contain (a,v),
   because llmem is only a *local* view of the actual lmemory.
   For this reason, we take the new values from global view glmem.
 *)
Definition update_version_addr
  (glmem : LMem) (a : Addr) (v : Version) (llmem : LMem): LMem :=
  match glmem !! (a,v) with
  | Some lw => <[ (a, v+1) := lw ]> llmem
  | None => llmem
  end.

(* Update the lmemory region for a given lregion.
   Note that it only updates the *local* view of the lmemory,
   which might not contain some of the addresses in la.
   For this reason, we take the new values from global view glmem.
 *)
Definition update_version_region
  (glmem : LMem) (la : list Addr) (v : Version) (llmem : LMem) : LMem :=
  foldr (fun a lmem' => update_version_addr glmem a v lmem') llmem la.

Definition update_version_addr_vmap
  (a : Addr) (v : Version) (vmap : VMap) : VMap :=
  <[ a := v +1 ]> vmap.

Definition update_version_region_vmap
  (la : list Addr) (v : Version) (vmap : VMap) : VMap :=
  foldr (fun a vm => update_version_addr_vmap a v vm) vmap la.

Lemma update_version_addr_lookup
  (glmem llmem : LMem) (a a' : Addr) (v v': Version) (lw' : LWord) :
  llmem !! (a', v') = Some lw' ->
  llmem !! (a, v+1) = None ->
  update_version_addr glmem a v llmem !! (a', v') = Some lw'.
Proof.
  intros Hlw' Hmax.
  rewrite /update_version_addr.
  destruct (glmem !! (a,v)) eqn:Hglm;eauto.
  destruct (decide ((a', v') = (a,v+1))); simplify_map_eq ; auto.
  by rewrite Hmax in Hlw'.
Qed.

Lemma update_version_region_vmap_lookup {vmap : VMap} {v la} :
  NoDup la ->
  ∀ a : Addr, a ∈ la -> update_version_region_vmap la v vmap !! a = Some (v + 1).
Proof.
  induction la; intros Hnd a' Ha'; first inversion Ha'.
  apply elem_of_cons in Ha'.
  destruct Ha' as [->|Ha'].
  - by rewrite lookup_insert.
  - rewrite lookup_insert_ne.
    + apply IHla; last done.
      by apply (NoDup_cons_1_2 a).
    + intros <-.
      apply (NoDup_cons_1_1 a la Hnd Ha').
Qed.

Lemma update_version_addr_lookup_neq
  (glmem llmem : LMem) (a a' : Addr) (v v': Version) :
  a ≠ a' ->
  update_version_addr glmem a v llmem !! (a', v') = llmem !! (a', v').
Proof.
  intros Hneq.
  rewrite /update_version_addr.
  destruct (glmem !! (a,v)); auto.
  rewrite lookup_insert_ne //=; by intro ; simplify_eq.
Qed.

Lemma update_version_addr_mono
  (glmem lmem1 lmem2 : LMem) (a : Addr) (v : Version) :
  lmem1 ⊆ lmem2 ->
  update_version_addr glmem a v lmem1 ⊆ update_version_addr glmem a v lmem2.
Proof.
  intros Hincl.
  rewrite /update_version_addr.
  destruct (glmem !! (a,v)) as [lw|]; auto.
  by apply insert_mono.
Qed.

Lemma update_version_region_mono
  (glmem lmem1 lmem2 : LMem) (la : list Addr) (v : Version) :
  lmem1 ⊆ lmem2 ->
  update_version_region glmem la v lmem1 ⊆ update_version_region glmem la v lmem2.
Proof.
  induction la as [|a la IHla] ; intros Hincl ; cbn in *; eauto.
  apply IHla in Hincl; clear IHla ; rename Hincl into IH.
  rewrite -/(update_version_region glmem la v lmem1).
  rewrite -/(update_version_region glmem la v lmem2).
  by apply update_version_addr_mono.
Qed.

Lemma update_version_region_preserves_lmem
  (glmem llmem : LMem) (la : list Addr) (a : Addr) (v : Version) :
  update_version_region glmem la v llmem !! (a, v) = llmem !! (a, v).
Proof.
  move: glmem llmem a v.
  induction la as [|a' la IHla] ; intros *.
  - by cbn in *.
  - rewrite
      /update_version_region /=
        -/(update_version_region glmem la v llmem)
        /update_version_addr.
    destruct (glmem !! (a', v)) as [lwa|] eqn:Hlwa.
    + rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
    + eapply IHla; eauto.
Qed.

Lemma update_version_region_notin_preserves_lmem
  (glmem llmem : LMem) (la : list Addr) (a' : Addr) (v v': Version) :
  a' ∉ la ->
  update_version_region glmem la v llmem !! (a', v') = llmem !! (a', v').
Proof.
  move: glmem llmem a' v v'.
  induction la as [|a la IHla] ; intros * Ha'_notin_la.
  - by cbn in *.
  - destruct_cons.
    rewrite
      /update_version_region /=
        -/(update_version_region glmem la v llmem)
        /update_version_addr.
    assert (update_version_region glmem la v llmem !! (a', v') = llmem !! (a', v'))
      as IH by (eapply IHla ; eauto).
    destruct (glmem !! (a, v)) as [lwa|] eqn:Hlwa; eauto.
    rewrite lookup_insert_ne //=; intro ; simplify_eq ; lia.
Qed.

Lemma update_version_region_preserves_lmem_next
  (glmem llmem : LMem) (la : list Addr) (a' : Addr) (v : Version) :
  NoDup la ->
  a' ∈ la ->
  llmem !! (a', v+1) = None ->
  update_version_region glmem la v llmem !! (a', v + 1) = glmem !! (a', v).
Proof.
  move: glmem llmem a' v.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la Hlmem_next
  ; first (by set_solver).
  destruct_cons.
  rewrite
    /update_version_region /=
      -/(update_version_region glmem la v llmem)
      /update_version_addr.
  destruct Ha'_in_la as [|Ha'_in_la] ; simplify_map_eq.
  - destruct (glmem !! (a, v)) as [lwa|] eqn:Hlwa.
    + now rewrite lookup_insert //=.
    + rewrite update_version_region_notin_preserves_lmem; eauto.
  - assert
      (update_version_region glmem la v llmem !! (a', v + 1) = glmem !! (a', v))
        as IH by (erewrite IHla; eauto).
    destruct (glmem !! (a, v)) as [lwa|] eqn:Hlwa; auto.
    by rewrite lookup_insert_ne //= ; intro ; simplify_eq ; set_solver.
Qed.

Lemma update_version_addr_updated_incl
  (glmem llmem llmem' : LMem) (la : list Addr) (a : Addr) (v : Version) :
  update_version_region glmem la v llmem !! (a, v + 1) = None ->
  update_version_addr glmem a v (update_version_region glmem la v llmem) ⊆ llmem' ->
  update_version_region glmem la v llmem ⊆ llmem'.
Proof.
  intros Hupd_max Hupd.
  rewrite /update_version_addr in Hupd.
  destruct (glmem !! (a, v)) eqn:Hupd_a
  ; last done.
  eapply insert_subseteq_r_inv in Hupd; eauto.
Qed.

Lemma update_version_addr_insert
  (glmem lmem lmem' : LMem) (a a' : Addr) (v v' : Version) (la : list Addr) (lw : LWord) :
  lmem !! (a', v') = None ->
  update_version_addr glmem a v (update_version_region glmem la v (<[(a', v'):=lw]> lmem)) ⊆ lmem' ->
  update_version_region glmem la v lmem ⊆ lmem' ->
  update_version_addr glmem a v (update_version_region glmem la v lmem) ⊆ lmem'.
Proof.
  intros Hlmem_None Hupd Hupd_mem_incl.
  rewrite /update_version_addr in Hupd |- *.
  destruct (glmem !! (a, v)) eqn:Hupd_a; last done.
  eapply insert_subseteq_l; eauto.
  eapply lookup_weaken; eauto.
  now eapply lookup_insert.
Qed.

Lemma update_version_region_insert
  (glmem lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord):
  NoDup la ->
  a' ∉ la ->
  lmem !! (a', v') = None ->
  Forall (fun a => lmem !! (a, v+1) = None) la ->
  update_version_region glmem la v (<[(a', v'):=lw]> lmem) ⊆ lmem' ->
  update_version_region glmem la v lmem ⊆ lmem'.
Proof.
  move: glmem lmem lmem' a' v v' lw.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None HmaxMap Hupd.
  - cbn in *.
    eapply insert_delete_subseteq in Hupd; eauto.
    apply map_subseteq_spec ; intros [a0 v0] lw0 Hlw0.
    eapply lookup_weaken in Hlw0 ; last eauto.
    assert ((a0, v0) ≠ (a', v')) as Hneq by (intro ; simplify_map_eq).
    rewrite lookup_delete_ne in Hlw0 ; eauto.
  - destruct_cons.
    rewrite /= -/(update_version_region (<[(a', v'):=lw]> lmem) la v) in Hupd.
    rewrite /= -/(update_version_region lmem la v).
    eapply update_version_addr_insert ; cycle 1 ; eauto.
    eapply IHla with (a' := a') (v' := v') (lw := lw); eauto.
    eapply update_version_addr_updated_incl ; eauto.
    rewrite update_version_region_notin_preserves_lmem //=.
    rewrite lookup_insert_ne //=; intro ; simplify_eq.
Qed.

Lemma update_version_region_insert_inv
  (glmem lmem : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
  NoDup la ->
  lmem !! (a', v) = None ->
  Forall (fun a => lmem !! (a, v+1) = None) la ->
  update_version_region glmem la v lmem ⊆
    update_version_region glmem la v (<[(a', v):=lw]> lmem).
Proof.
  revert glmem lmem a' v lw.
  induction la as [|a la IHla] ; intros * HNoDup Hlmem_None HmaxMap ; cbn in *.
  - by apply insert_subseteq.
  - rewrite -!/(update_version_region _ _ v).
    destruct_cons.
    specialize (IHla glmem lmem a' v lw HNoDup_la Hlmem_None HmaxMap).
    rewrite /update_version_addr.
    destruct (glmem !! (a,v)); last done.
    now apply insert_mono.
Qed.

Lemma update_version_addr_notin_preserves_cur
  (vmap vmap' : VMap) (a a' : Addr) (v : Version) :
  vmap' = update_version_addr_vmap a' v vmap
  → a ≠ a'
  → vmap' !! a = vmap !! a.
Proof.
  move=> -> Hneq.
  now rewrite lookup_insert_ne.
Qed.

Lemma update_version_region_notin_preserves_cur:
  ∀ (vmap vmap' : VMap)
    (la : list Addr) (a : Addr) (v : Version),
    vmap' = update_version_region_vmap la v vmap
    → a ∉ la
    → vmap' !! a = vmap !! a.
Proof.
  move=> vmap vmap' la.
  move: vmap vmap'.
  induction la as [|a la IH]
  ; intros * Hupd Ha_notin_la
  ; first (cbn in *; by simplify_eq).
  destruct_cons.
  cbn in Hupd.
  set (vmap0 := foldr (λ (a : Addr) (vm : VMap), update_version_addr_vmap a v vm) vmap la).
  assert (vmap !! a0 = vmap0 !! a0) as Hcur0 by (symmetry ; eapply IH ; eauto).
  rewrite Hcur0.
  erewrite update_version_addr_notin_preserves_cur; cycle 1 ; eauto.
Qed.

Lemma update_version_notin_is_cur_word
  (vmap vmap' : VMap)
  (p : Perm) (b e a : Addr) (v : Version)
  (lw lwsrc : LWord) :
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  vmap' = update_version_region_vmap (finz.seq_between b e) v vmap ->
  ¬ overlap_wordL lwsrc lw ->
  is_cur_word lw vmap ->
  is_cur_word lw vmap'.
Proof.
  move=> Hget Hupd Hno_overlap His_cur_lw.
  destruct_lword lw ; cbn; try done
  ; intros a'0 Ha'0 ; cbn in His_cur_lw
  ; pose proof (His_cur_lw a'0 Ha'0) as Ha'0_cur
  ; (erewrite <- update_version_region_notin_preserves_cur in Ha'0_cur; eauto)
  ; by eapply not_overlap_wordL_seq_between; [| | eauto..].
Qed.

Lemma update_version_region_lreg_corresponds_src
  (phr : Reg) (phm : Mem) (lr : LReg) (lmem lm lmem' lm' : LMem) (vmap vmap' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) (lwsrc: LWord) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  is_cur_word (next_version_lword lwsrc) vmap' ->
  lr !! src = Some lwsrc ->
  unique_in_machineL lr lm vmap src lwsrc ->
  vmap' = update_version_region_vmap (finz.seq_between b e) v vmap ->
  reg_phys_log_corresponds (<[src := lword_get_word (next_version_lword lwsrc)]> phr) (<[src:= next_version_lword lwsrc]> lr) vmap'.
Proof.
  move=>  [Hreg_inv Hmem_inv] Hget Hcur_lw Hlr_src Hunique Heq.
  subst vmap'.
  split.
  - rewrite /lreg_strip fmap_insert /= -/(lreg_strip lr).
    by replace phr with (lreg_strip lr) by (by destruct Hreg_inv as [? _]).
  - rewrite -insert_delete_insert.
    eapply lreg_corresponds_insert_respects with (phr := (delete src phr)).
    2: {  by cbn. }
    destruct Hreg_inv as [Hstrip Hcur_reg].
    split.
    + by rewrite /lreg_strip fmap_delete -/(lreg_strip lr) Hstrip.
    + apply map_Forall_lookup_2.
      intros r lw' Hr.
      destruct (decide (r = src)); subst.
      rewrite lookup_delete in Hr; congruence.
      rewrite lookup_delete_ne in Hr; eauto.
      apply Hunique in Hlr_src. destruct Hlr_src as [Hunique_reg _].
      rewrite /unique_in_registersL in Hunique_reg.
      eapply map_Forall_lookup_1 in Hunique_reg ; eauto.
      rewrite decide_False in Hunique_reg; auto.
      eapply map_Forall_lookup_1 in Hcur_reg ; eauto.
      eapply update_version_notin_is_cur_word ; eauto.
Qed.


Lemma update_version_region_lreg_corresponds_src'
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap vmap' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) (lwsrc: LWord) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_wlcap_slcap lwsrc = Some (p, b, e, a, v) ->
  is_cur_word (next_version_lword lwsrc) vmap' ->
  lr !! src = Some lwsrc ->
  unique_in_machineL lr lm vmap src lwsrc ->
  vmap' = update_version_region_vmap (finz.seq_between b e) v vmap ->
  reg_phys_log_corresponds phr (<[src:= next_version_lword lwsrc]> lr) vmap'.
Proof.
  move=> HLinv Hget Hcur_lw Hlr_src Hunique Hupd.
  rewrite (_: phr = (<[src:=(lword_get_word (next_version_lword lwsrc))]> phr)).
  * eapply update_version_region_lreg_corresponds_src; eauto.
  * rewrite insert_id; first done.
    rewrite lword_get_word_next_version.
    eapply state_corresponds_reg_get_word; eauto.
Qed.

Lemma update_version_word_region_update_lword {vmap vmap' : VMap} {lw : LWord} {p b e a v} :
   get_wlcap_slcap lw = Some (p, b, e, a, v) ->
    update_version_region_vmap (finz.seq_between b e) v vmap = vmap'
    → is_cur_word lw vmap → is_cur_word (next_version_lword lw) vmap'.
Proof.
  intros Hgclw <- Hcw.
  destruct lw as [|[*|]|f [*|*]]; inversion Hgclw; subst; cbn;
    apply update_version_region_vmap_lookup, finz_seq_between_NoDup.
Qed.

Lemma update_version_addr_preserves_mem_current_version
  (lm lm': LMem) (vmap vmap' : VMap) (a : Addr) v :
  lm !! (a, v + 1) = None ->
  is_cur_addr (a , v) vmap ->
  lm' = update_version_addr lm a v lm ->
  vmap' = update_version_addr_vmap a v vmap ->
  lmem_not_access_addrL lm vmap a →
  mem_current_version lm vmap ->
  mem_current_version lm' vmap'.
Proof.
  intros Hmaxv Hcur_addr -> -> Hnaccess_mem Hdom.
  rewrite /update_version_addr /update_version_addr_vmap.
  rewrite /mem_current_version in Hdom |- *.
  destruct (lm !! (a,v)) as [lw |] eqn:Hla; cbn in * ; simplify_eq ; rewrite Hla.
  - eapply map_Forall_insert; eauto.
    split.
    + exists (v+1).
      split ; [|split] ; cbn ; eauto.
      by apply is_cur_addr_insert.
      by simplify_map_eq.
    + eapply map_Forall_impl; eauto.
    cbn ; intros la' lw' Hlegal.
    destruct Hlegal as (cur_v' & Hcur_la' & Hcurv'_max & Hsome_la').
    destruct (decide (laddr_get_addr la' = a)) as [Heq|Hneq] ; subst.
    {
      exists (v+1).
      split ; [|split] ; cbn ; eauto.
      apply is_cur_addr_insert.
      eapply is_cur_addr_same in Hcur_addr ; eauto ; subst.
      lia.
      by simplify_map_eq.
    }
    {
      exists cur_v'.
      split ; [|split] ; eauto.
      rewrite /is_cur_addr in Hcur_la' |- * ; cbn in *.
      by simplify_map_eq.
      rewrite lookup_insert_ne; auto. intro Heq ; destruct Heq ; subst.
      eapply is_cur_addr_same in Hcur_addr ; eauto ; subst.
      lia.
    }
  - eapply map_Forall_impl; eauto.
    cbn ; intros la' lw' Hlegal.
    destruct Hlegal as (cur_v' & Hcur_la' & Hcurv'_max & Hsome_la').
    exists cur_v'.
    split ; [|split] ; eauto.
    assert (a ≠ laddr_get_addr la') as Hneq_a.
    {
      intro ; subst. destruct Hsome_la'.
      eapply is_cur_addr_same in Hcur_addr ; eauto ; subst.
      by rewrite H in Hla.
    }
    rewrite /is_cur_addr in Hcur_la' |- * ; cbn in *.
    by simplify_map_eq.
Qed.


Lemma update_cur_version_notin_is_cur_word
  (lm : LMem) (vmap : VMap) (a : Addr) (v : Version) (lw : LWord) :
  lmem_not_access_addrL lm vmap a ->
  lm !! (a, v) = Some lw ->
  is_cur_addr (a,v) vmap ->
  is_cur_word lw vmap ->
  is_cur_word lw (<[a:=v + 1]> vmap).
Proof.
  move=> Hno_access Hlm Hcur His_cur_lw.
  destruct_lword lw ; cbn; try done
  ; intros a' Ha' ; cbn in His_cur_lw
  ; pose proof (His_cur_lw a' Ha') as Ha'_cur
  ; eapply map_Forall_lookup in Hlm ; eauto; cbn in *
  ; eapply Hlm in Hcur.
  all: assert (a ≠ a')
    as Hneq by by (intro ; simplify_eq; by apply elem_of_finz_seq_between in Ha').
  all: try rewrite lookup_insert_ne ; auto.
Qed.

Lemma update_version_addr_preserves_mem_vmap_root
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (a : Addr) v :
  lm !! (a, v + 1) = None ->
  is_cur_addr (a , v) vmap ->
  lm' = update_version_addr lm a v lm ->
  vmap' = update_version_addr_vmap a v vmap ->
  lmem_not_access_addrL lm vmap a →
  mem_current_version lm vmap ->
  mem_vmap_root phm lm vmap ->
  mem_vmap_root phm lm' vmap'.
Proof.
  intros Hmax Hcur_addr -> -> Hnaccess_mem Hdom Hroot.
  rewrite /update_version_addr /update_version_addr_vmap.
  destruct (lm !! (a,v)) as [lw |] eqn:Hla; cbn in * ; rewrite Hla ; simplify_eq.
  - assert (not (word_access_addrL a lw)) as Hnaccess by eauto.
    pose proof (Hla' := Hla).
    eapply map_Forall_lookup_1 in Hla'; eauto; cbn in Hla'.
    destruct Hla' as (va & Hcur_va & Hle_va & [lwa Hlwa]).
    rewrite /is_cur_addr /= in Hcur_addr, Hcur_va.
    rewrite Hcur_addr in Hcur_va ; simplify_eq.
    apply map_Forall_insert_2.
    { pose proof (Hla' := Hla).
      eapply map_Forall_lookup_1 in Hla; eauto ; cbn in *.
      destruct Hla as (cur_v & Hcur_v & Hcur_max & [cur_lw Hcur_lw]).
      rewrite /is_cur_addr /= Hcur_addr in Hcur_v; simplify_map_eq.
      exists lw. split. by simplify_map_eq.
      eapply map_Forall_lookup_1 in Hcur_addr ; eauto ; cbn in Hcur_addr.
      destruct Hcur_addr as (lw' & Hlw' & Hw' & Hcur_lw').
      rewrite Hlw' in Hla' ; simplify_eq.
      split; auto.
      eapply update_cur_word ; eauto.
    }
    eapply map_Forall_lookup; eauto.
    intros a' v' Hcur_a'.
    pose proof (Hcur_a'' := Hcur_a').
    eapply map_Forall_lookup_1 in Hcur_a'' ; eauto ; cbn in Hcur_a''.
    destruct Hcur_a'' as (lw' & Hlw' & Hw' & Hcur_lw').
    destruct (decide (a = a')); simplify_eq.
    + eapply update_cur_word with (v := va+1) in Hcur_lw'; eauto.
      exists lw.
      assert ((a', va + 1) ≠ (a', va)) by (intro ; simplify_eq ; lia).
      rewrite Hcur_addr in Hcur_a' ; simplify_eq.
      rewrite Hlwa in Hla ; simplify_eq.
      by simplify_map_eq.
    + exists lw'.
      assert ((a, va + 1) ≠ (a', v')) by (intro ; simplify_eq).
      split ; [|split] ; try by simplify_map_eq.
      eapply update_cur_word;eauto.
  - rewrite /mem_vmap_root in Hroot |- *.
    eapply map_Forall_lookup in Hcur_addr ; eauto; cbn in *.
    destruct Hcur_addr as (lw & Hlm_lw & Hphm_lw & Hcur_lw).
    rewrite Hlm_lw in Hla ; simplify_eq.
Qed.

Lemma update_version_addr_preserves_mem_corresponds
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (a : Addr) v :
   a ∉ reserved_addresses ->
  lm !! (a, v + 1) = None ->
  is_cur_addr (a , v) vmap ->
  lm' = update_version_addr lm a v lm ->
  vmap' = update_version_addr_vmap a v vmap ->
  lmem_not_access_addrL lm vmap a →
  mem_phys_log_corresponds phm lm vmap ->
  mem_phys_log_corresponds phm lm' vmap'.
Proof.
  intros Hnotres Hmax Hcur_addr -> -> Hnaccess_mem (Hdom & Hroot & Hgcroot).
  repeat split.
  - eapply update_version_addr_preserves_mem_current_version ; eauto.
  - eapply update_version_addr_preserves_mem_vmap_root ; eauto.
  - now apply map_Forall_insert_2.
Qed.

(* If an address `a'` is not reachable from the current view of the lmem, *)
(*    then updating the version number of another address `a` *)
(*    does not make it reachable *)
Lemma update_version_addr_preserves_notin_not_access
  (lm lm' : LMem) (a : Addr) (vmap vmap': VMap) (v : Version) (a' : Addr) :
  a ≠ a' ->
  lm ⊆ lm' ->
  is_Some (lm !! (a', v)) ->
  is_cur_addr (a', v) vmap' ->
  lm !! (a' , v+1) = None ->
  lmem_not_access_addrL lm' vmap' a ->
  lmem_not_access_addrL (update_version_addr lm a' v lm')
    (update_version_addr_vmap a' v vmap') a.
Proof.
  intros Hneq Hincl [lw Hlm] Hcur Hmaxv Hno_access.
  rewrite /update_version_addr /update_version_addr_vmap.
  rewrite Hlm.
  apply map_Forall_lookup.
  intros la' lw' Hsome' Hcur'.
  destruct la' as [a0 v0].
  destruct (decide (a0 = a')) ; simplify_eq.
  - assert (v0 = (v + 1)) by (rewrite /is_cur_addr in Hcur'; by simplify_map_eq).
    simplify_map_eq.
    eapply lookup_weaken in Hlm ; eauto.
  - assert ((a', v + 1) ≠ (a0, v0)) by (intro ; simplify_eq).
    simplify_map_eq.
    apply (map_Forall_lookup_1 _ _ _ _ Hno_access) in Hsome'; auto.
    by rewrite /is_cur_addr /= in Hcur'; simplify_map_eq.
Qed.

Lemma update_version_addr_expands (lm lm' : LMem) (a : Addr) ( v : Version ) :
  lm ⊆ lm' ->
  lm !! (a, v + 1) = None ->
  lm ⊆ update_version_addr lm a v lm'.
Proof.
  intros Hincl Hmaxv.
  rewrite /update_version_addr.
  destruct (lm !! (a,v)) as [lw|]; eauto.
  eapply insert_subseteq_r; eauto.
Qed.

Lemma update_version_region_expands (lm : LMem) (la : list Addr) (v : Version) :
  NoDup la ->
  Forall (fun a => lm !! (a , v+1) = None) la ->
  lm ⊆ update_version_region lm la v lm.
Proof.
  induction la as [|a la IHla] ; cbn in * ; eauto.
  intros HNoDup HmaxMap ; destruct_cons. apply IHla in HNoDup_la; eauto.
  rewrite -/(update_version_region lm la v lm).
  eapply update_version_addr_expands; eauto.
Qed.

Lemma update_version_addr_vmap_neq_preserves_cur
  (vmap : VMap) (a' : Addr) (v : Version) (a: Addr) :
  a ≠ a' ->
  is_cur_addr (a, v) vmap ->
  is_cur_addr (a, v) (update_version_addr_vmap a' v vmap).
Proof.
  intros Hneq Hcur.
  rewrite /update_version_addr_vmap /is_cur_addr.
  by simplify_map_eq.
Qed.

Lemma update_version_region_vmap_notin_preserves_cur
  (vmap : VMap) (la : list Addr) (v : Version) (a : Addr) :
  a ∉ la ->
  is_cur_addr (a, v) vmap ->
  is_cur_addr (a, v) (update_version_region_vmap la v vmap).
Proof.
  induction la as [|a' la IHla] ; cbn in * ; intros Hnot_in Hcur; auto.
  rewrite -/(update_version_region_vmap la v vmap).
  destruct_cons.
  apply IHla in Ha_notin_la; auto.
  by eapply update_version_addr_vmap_neq_preserves_cur.
Qed.

Lemma update_version_region_preserves_notin_not_access
  (lm : LMem) (la : list Addr) (vmap : VMap) (v : Version) (a : Addr) :
  a ∉ la ->
  NoDup la ->
  Forall (fun a => is_Some (lm !! (a , v))) la ->
  Forall (fun a => is_cur_addr (a , v) vmap) la ->
  Forall (fun a => lm !! (a , v+1) = None) la ->
  lmem_not_access_addrL lm vmap a ->
  lmem_not_access_addrL (update_version_region lm la v lm)
    (update_version_region_vmap la v vmap) a.
Proof.
  move: a.
  induction la as [|a' la]; intros a Hnotin HNoDup Hmap HcurMap HmaxvMap Hnot_access; cbn; auto.
  rewrite -/(update_version_region lm la v lm).
  rewrite -/(update_version_region_vmap la v vmap).
  destruct_cons.
  apply IHla in Hnot_access; eauto.
  eapply update_version_addr_preserves_notin_not_access; eauto.
  apply update_version_region_expands; auto.
  by apply update_version_region_vmap_notin_preserves_cur.
Qed.

(* TODO generalize to update with glm instead of lm *)
Lemma update_version_region_preserves_mem_corresponds
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (la : list Addr) v:
  vmap' = update_version_region_vmap la v vmap ->
  lm' = update_version_region lm la v lm ->
  NoDup la →
  Forall (fun a => a ∉ reserved_addresses) la ->
  Forall (fun a => is_Some (lm !! (a, v))) la ->
  Forall (fun a => is_cur_addr (a , v) vmap) la ->
  Forall (fun a => lm !! (a , v+1) = None) la ->
  Forall (fun a => lmem_not_access_addrL lm vmap a) la →
  mem_phys_log_corresponds phm lm vmap ->
  mem_phys_log_corresponds phm lm' vmap'.
Proof.
  move: phm lm lm' vmap vmap'.
  induction la as [| a la IH]; intros * -> -> Hno_dup Hnotres Hmap Hcur Hmax Hall_naccess_mem Hmem_corr.
  - by cbn in * ; simplify_eq.
  - destruct_cons.
    assert (mem_phys_log_corresponds phm
              (update_version_region lm la v lm)
              (update_version_region_vmap la v vmap)) as Hinv
    by (eapply IH ;eauto).
    eapply update_version_addr_preserves_mem_corresponds
             in Hinv
    ; eauto.
    { erewrite update_version_region_notin_preserves_lmem; eauto. }
    {
      rewrite /is_cur_addr ; cbn.
      erewrite update_version_region_notin_preserves_cur; eauto.
    }
    { cbn.
      rewrite -/(update_version_region lm la v lm).
      rewrite /update_version_addr.
      rewrite update_version_region_notin_preserves_lmem; eauto.
    }
    {
      eapply update_version_region_preserves_notin_not_access; eauto.
    }
Qed.


(** Machinery for valid update of the lmemory *)

(* We require ⊆, because lmem might contain only a subset of the updated region,
           which means that lmem' contains both:
           - the updated addresses known from lmem
           - the updated addresses a ∈ [b, e), unknown from lmem

       We also require that every addresses in the region have actually been updated,
       although we might not know their value
 *)
Definition is_valid_updated_lmemory
  (glmem llmem : LMem) (la : list Addr) (v : Version) (llmem' : LMem) : Prop :=
  (update_version_region glmem la v llmem) ⊆ llmem' /\
  llmem ⊆ glmem ∧
    (* TODO unclear whether this is useful in the def *)
    (Forall (fun a => llmem !! (a, v+1) = None) la) /\
    (Forall (fun a => is_Some (llmem' !! (a, v+1))) la).


Lemma is_valid_updated_lmemory_notin_preserves_lmem
  (glmem llmem llmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
  a' ∉ la ->
  is_valid_updated_lmemory glmem llmem la v llmem' ->
  llmem !! (a', v') = Some lw ->
  llmem' !! (a', v') = Some lw.
Proof.
  move: glmem llmem llmem' a' v v' lw.
  induction la as [|a la IHla]
  ; intros * Ha'_notin_la (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated) Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto).
  destruct_cons; destruct Hupdated_a as [ lwa Hlwa ].
  rewrite /= -/(update_version_region glmem la v llmem)
    /update_version_addr map_subseteq_spec in Hcompatibility.
  apply Hcompatibility; clear Hcompatibility.
  assert (update_version_region glmem la v llmem !! (a', v') = Some lw)
    as IH by (rewrite update_version_region_notin_preserves_lmem; eauto).
  destruct ( glmem !! (a, v) )
    as [lwa'|] eqn:Hlwa' ; auto.
  by rewrite lookup_insert_ne //=; intro ; simplify_eq.
Qed.

Lemma is_valid_updated_lmemory_preserves_lmem
  (glmem llmem llmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
  NoDup la ->
  is_valid_updated_lmemory glmem llmem la v llmem' ->
  llmem !! (a', v') = Some lw ->
  llmem' !! (a', v') = Some lw.
Proof.
  move: glmem llmem llmem' a' v v' lw.
  induction la as [|a la IHla]
  ; intros * HNoDup (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated) Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto).
  destruct_cons; destruct Hupdated_a as [ lwa Hlwa ].
  assert ((a', v') ≠ (a, v+1)) as Hneq
    by (intro ; simplify_map_eq; by rewrite HmaxMem_a in Hlmem).
  destruct (decide (a' = a)) as [? | Ha'_neq_a] ; simplify_map_eq.
  - assert (v' ≠ (v+1)) as Hneq_v by (intro ; simplify_eq).
    eapply lookup_weaken ; last eapply Hcompatibility.
    eapply update_version_addr_lookup; eauto.
    all: erewrite update_version_region_notin_preserves_lmem; eauto.
  - eapply update_version_addr_updated_incl in Hcompatibility; eauto.
    eapply IHla; eauto.
    split; eauto.
    rewrite update_version_region_notin_preserves_lmem; eauto.
Qed.

Lemma is_valid_updated_lmemory_lmem_incl
  (glmem llmem llmem' : LMem) (la : list Addr) (v : Version) :
  NoDup la ->
  is_valid_updated_lmemory glmem llmem la v llmem' ->
  llmem ⊆ llmem'.
Proof.
  intros.
  eapply map_subseteq_spec; intros.
  eapply is_valid_updated_lmemory_preserves_lmem; eauto.
Qed.

Lemma is_valid_updated_lmemory_preserves_lmem_next
  (glmem llmem llmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
  NoDup la ->
  a' ∈ la ->
  is_valid_updated_lmemory glmem llmem la v llmem' ->
  (* llmem ⊆ glmem -> *)
  Forall (fun a => llmem !! (a, v+1) = None) la ->
  llmem !! (a', v) = Some lw ->
  llmem' !! (a', v+1) = Some lw.
Proof.
  move: glmem llmem llmem' a' v lw.
  induction la as [|a la IHla]
  ; intros * HNoDup Ha'_in_la (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated) Hmax_la Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto; set_solver).
  destruct_cons; destruct Hupdated_a as [ lwa Hlwa ].
  rewrite /= -/(update_version_region glmem la v llmem)
     /update_version_addr map_subseteq_spec in Hcompatibility.
  apply Hcompatibility; clear Hcompatibility.
  destruct ( glmem !! (a, v) ) as [lwa'|] eqn:Hlwa'.
  - destruct Ha'_in_la as [? | Ha'_in_la] ; simplify_map_eq.
    { eapply lookup_weaken in Hlmem; eauto. by rewrite Hlmem in Hlwa'. }
    { pose proof Ha'_in_la as Ha'_in_la'.
    apply elem_of_list_lookup in Ha'_in_la'.
    destruct Ha'_in_la' as [? Ha'_lookup].
    eapply Forall_lookup in Hmax_la ; eauto.
    rewrite lookup_insert_ne //=; last (intro ; simplify_eq; set_solver).
    rewrite update_version_region_preserves_lmem_next; eauto.
    eapply lookup_weaken in Hlmem; eauto. }
  - destruct Ha'_in_la as [Hneq | Ha']; subst.
    { eapply lookup_weaken in Hlmem; eauto. by rewrite Hlmem in Hlwa'. }
    {
      erewrite update_version_region_preserves_lmem_next; eauto.
      eapply lookup_weaken in Hlmem; eauto.
      apply elem_of_list_lookup_1 in Ha' ; destruct Ha' as [? Ha'].
      eapply Forall_lookup in Hmax_la; eauto.
    }
Qed.

Lemma is_valid_updated_lmemory_insert
  (glmem llmem llmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
  NoDup la ->
  a' ∉ la ->
  llmem !! (a', v') = None ->
  Forall (fun a => llmem !! (a, v+1) = None) la ->
  is_valid_updated_lmemory glmem (<[(a', v') := lw]> llmem) la v llmem' ->
  is_valid_updated_lmemory glmem llmem la v llmem'.
Proof.
  move: glmem llmem llmem' a' v v' lw.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None  HmaxMap Hvalid.
  - destruct Hvalid as (Hvalid & Hgl_llmem & _).
    split; cbn in *; try done.
    + eapply insert_subseteq_r_inv; eauto.
    + split; cbn in *; try done.
      eapply insert_subseteq_r_inv; eauto.
  - destruct Hvalid as (Hupd & Hgl_llmem & HmaxMap' & HnextMap).
    split; first (eapply update_version_region_insert; eauto).
    split; auto.
    eapply insert_subseteq_r_inv; eauto.
Qed.

Lemma is_valid_updated_lmemory_insert'
  (glmem llmem llmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
  NoDup la ->
  a' ∈ la ->
  llmem !! (a', v) = None ->
  Forall (fun a => llmem !! (a, v+1) = None) la ->
  is_valid_updated_lmemory glmem (<[(a', v) := lw]> llmem) la v llmem' ->
  is_valid_updated_lmemory glmem llmem la v llmem'.
Proof.
  move: glmem llmem llmem' a' v lw.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la Hlmem_None HmaxMap Hvalid.
  - destruct Hvalid as (Hvalid & Hgl_llmem & _).
    split; cbn in *; try done.
    + eapply insert_subseteq_r_inv; eauto.
    + split; cbn in *; try done.
      eapply insert_subseteq_r_inv; eauto.
  - destruct Hvalid as (Hupd & Hgl_llmem & HmaxMap' & HnextMap).
    split; auto; cycle 1.
    + split; auto.
      eapply insert_subseteq_r_inv; eauto.
    + eapply map_subseteq_trans.
      by eapply update_version_region_insert_inv; eauto.
      eauto.
Qed.

Lemma is_valid_updated_lmemory_lmem_subset
  (glmem llmem llmem' llmem'' : LMem) (la : list Addr) (v : Version) :
  llmem ⊆ llmem' ->
  is_valid_updated_lmemory glmem llmem' la v llmem'' ->
  is_valid_updated_lmemory glmem llmem la v llmem''.
Proof.
  move: glmem llmem llmem' v.
  induction la as [|a la IHla]
  ; intros * Hsubset (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated)
  ; first (cbn in * ; eauto).
  - rewrite /is_valid_updated_lmemory.
    repeat split; eauto; cbn; eapply map_subseteq_trans; eauto.
  - destruct_cons; destruct Hupdated_a as [ lwa Hlwa ].
    rewrite /is_valid_updated_lmemory.
    repeat split; eauto.
    + eapply update_version_region_mono in Hsubset; eauto.
      eapply map_subseteq_trans; eauto.
    + eapply map_subseteq_trans; eauto.
    + rewrite Forall_cons; split; first eapply lookup_weaken_None; eauto.
      rewrite !Forall_forall in HmaxMem |- *.
      intros a' Ha'. apply HmaxMem in Ha'.
      eapply lookup_weaken_None; eauto.
Qed.

(** Logical machine *)

Inductive isCorrectLPC: LWord → Prop :=
| isCorrectLPC_intro:
  forall lpc p (b e a : Addr),
  lword_get_word lpc = (WCap p b e a) ->
  isCorrectPC (WCap p b e a) ->
  isCorrectLPC lpc.

Lemma isCorrectLPC_isCorrectPC :
  forall lw, isCorrectLPC lw -> isCorrectPC (lword_get_word lw).
Proof.
  intros lw Hcorrect.
  destruct_word lw; inv Hcorrect; cbn in *; subst; auto; try congruence.
Qed.

Lemma isCorrectPC_isCorrectLPC :
  forall lw, isCorrectPC (lword_get_word lw) -> isCorrectLPC lw.
Proof.
  intros lw Hcorrect.
  destruct_word lw; inv Hcorrect; cbn in *; subst; auto.
  econstructor; cbn; eauto; constructor; auto.
Qed.

Lemma isCorrectLPC_isCorrectPC_iff :
  forall lw, isCorrectLPC lw <-> isCorrectPC (lword_get_word lw).
Proof.
  intros; split ; [apply isCorrectLPC_isCorrectPC | apply isCorrectPC_isCorrectLPC].
Qed.

Lemma not_isCorrectLPC_perm p b e a v :
  p ≠ RX ∧ p ≠ RWX → ¬ isCorrectLPC (LCap p b e a v).
Proof.
  intros.
  intro contra ; apply isCorrectLPC_isCorrectPC_iff in contra ; simpl in contra.
  apply not_isCorrectPC_perm in contra;auto.
Qed.

Lemma not_isCorrectLPC_bounds p b e a v :
  ¬ (b <= a < e)%a → ¬ isCorrectLPC (LCap p b e a v).
Proof.
  intros.
  intro contra ; apply isCorrectLPC_isCorrectPC_iff in contra ; simpl in contra.
  apply not_isCorrectPC_bounds in contra;auto.
Qed.

Lemma isCorrectLPC_ExecPCPerm_InBounds p b e a v :
  ExecPCPerm p →
  InBounds b e a →
  isCorrectLPC (LCap p b e a v).
Proof.
  unfold ExecPCPerm, InBounds. intros.
  econstructor; eauto. apply isCorrectPC_ExecPCPerm_InBounds; auto.
Qed.

Lemma isCorrectLPC_dec:
  forall lw, { isCorrectLPC lw } + { not (isCorrectLPC lw) }.
Proof.
  destruct lw.
  - right. red; intros H. inversion H. by cbn in *.
  - destruct sb as [p b e a | ].
    -- case_eq (match p with RX | RWX => true | _ => false end); intros.
    + destruct (finz_le_dec b a).
      * destruct (finz_lt_dec a e).
        { left. econstructor; simpl; eauto. econstructor; simpl; eauto.
          by auto.
          destruct p; naive_solver. }
        { right. red; intro HH.
          inversion HH; subst; cbn in *; simplify_eq; inversion H1; subst; solve_addr. }
      * right. red; intros HH; inversion HH; subst.
        inversion HH; subst; cbn in *; simplify_eq; inversion H1; subst; solve_addr.
    + right. red; intros HH; inversion HH; subst.
      inversion HH; subst; cbn in *; simplify_eq; inversion H1; subst; naive_solver.
      -- right. red; intros H. inversion H. by cbn in *.
  - right. red; intros H. inversion H. by cbn in *.
Qed.

Lemma in_range_is_correctLPC p b e a b' e' v :
  isCorrectLPC (LCap p b e a v) →
  (b' <= b)%a ∧ (e <= e')%a →
  (b' <= a)%a ∧ (a < e')%a.
Proof.
  intros Hvpc [Hb He].
  inversion Hvpc; cbn in * ; simplify_eq.
  inversion H0 ; simplify_eq.
  solve_addr.
Qed.

Global Instance dec_lpc lc : Decision (isCorrectLPC lc).
Proof. apply isCorrectLPC_dec. Qed.

Lemma lreg_lookup regs (r : RegName) (lw : LWord) :
  regs !! r = Some lw -> (lreg_strip regs !! r) = Some (lword_get_word lw).
Proof.
  rewrite /lreg_strip lookup_fmap ; intros.
  by rewrite H; cbn.
Qed.

Lemma laddr_neq (la1 la2 : LAddr) :
  (la2.1 =? la1.1)%Z && (la2.2 =? la1.2) = false ->
  la1 <> la2.
Proof.
  intros Hneq.
  apply andb_false_iff in Hneq
  ; destruct Hneq as [Hneq | Hneq]
  ; [ apply Z.eqb_neq in Hneq | apply Nat.eqb_neq in Hneq ]
  ; congruence.
Qed.

Lemma laddr_neq' (a1 : Addr) (v1 : Version) (a2 : Addr) (v2 : Version) :
  (a1 =? a2)%Z && (v1 =? v2) = false ->
  (a1, v1) <> (a2, v2).
Proof.
  intros Hneq.
  apply andb_false_iff in Hneq
  ; destruct Hneq as [Hneq | Hneq]
  ; [ apply Z.eqb_neq in Hneq | apply Nat.eqb_neq in Hneq ]
  ; congruence.
Qed.

Definition updatePcPermL (lw: LWord): LWord :=
  match lw with
  | LCap E b e a v => LCap RX b e a v
  | _ => lw
  end.

Lemma updatePcPermL_spec (lw : LWord):
  lword_get_word (updatePcPermL lw) = updatePcPerm (lword_get_word lw).
Proof.
  destruct_lword lw; auto; destruct p ; auto.
Qed.

Lemma updatePcPermL_cap_non_E p b e a v :
  p ≠ E →
  updatePcPermL (LCap p b e a v) = LCap p b e a v.
Proof.
  intros HnE. cbn. destruct p; done.
Qed.

Lemma is_cur_updatePcPermL (lw : LWord) vmap:
  is_cur_word lw vmap -> is_cur_word (updatePcPermL lw) vmap.
Proof.
  destruct_lword lw ; cbn; auto.
  intros Hbounds.
  destruct p; auto.
Qed.

Definition z_of_argumentL (lregs: LReg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match lregs !! r with
    | Some (LInt z) => Some z
    | _ => None
    end
  end.

Definition lword_get_cap (lword : LWord) : option (Perm * Addr * Addr * Addr * Version) :=
  match lword with
  | LCap p b e a v => Some (p, b, e, a, v)
  | _ => None
  end.


Definition word_of_argumentL (lregs: LReg) (a: Z + RegName): option LWord :=
  match a with
  | inl n => Some (LInt n)
  | inr r => lregs !! r
  end.

Definition addr_of_argumentL (lregs: LReg) (src: Z + RegName): option Addr :=
  n ← z_of_argumentL lregs src ; z_to_addr n.

Definition otype_of_argumentL (lregs: LReg) (src: Z + RegName) : option OType :=
  match z_of_argumentL lregs src with
  | Some n => (z_to_otype n) : option OType
  | None => None : option OType
  end.

Definition is_mutable_rangeL (lw : LWord) : bool:=
  match lw with
  | LCap p _ _ _ _ => match p with | E  => false | _ => true end
  | LSealRange _ _ _ _ => true
  | _ => false end.

Definition nonZeroL (lw: LWord): bool :=
  match lw with
  | LInt n => Zneq_bool n 0
  | _ => true
  end.

Definition is_sealbL (lw : LWord) : bool :=
  match lw with
  | LWSealable sb => true
  |  _ => false
  end.

Definition is_sealrL (lw : LWord) : bool :=
  match lw with
  | LSealRange p b e a => true
  |  _ => false
  end.

Definition is_sealedL (lw : LWord) : bool :=
  match lw with
  | LWSealed a sb => true
  |  _ => false
  end.

Definition is_zL (lw : LWord) : bool :=
  match lw with
  | LInt z => true
  |  _ => false
  end.

Lemma word_to_lword_get_word_int (w : LWord) (v : Version) :
  is_zL w ->
  word_to_lword (lword_get_word w) v = w.
Proof.
  intros Hw.
  destruct w ; cbn in * ; done.
Qed.

Definition is_sealed_with_oL (lw : LWord) (o : OType) : bool :=
  match lw with
  | LWSealed o' sb => (o =? o')%ot
  | _ => false end.

Lemma laddr_ne_reg_ne {lregs : leibnizO LReg} {r1 r2 : RegName}
  {p0 b0 e0 a0 v0 p b e a v}:
  lregs !! r1 = Some (LCap p0 b0 e0 a0 v0)
  → lregs !! r2 = Some (LCap p b e a v)
  → (a0, v0) ≠ (a,v) → r1 ≠ r2.
Proof.
  intros Hr1 Hr2 Hne.
  destruct (decide (r1 = r2)); simplify_eq; auto.
Qed.

Lemma unique_in_registersL_pc_no_overlap
  (pc_p : Perm) (pc_b pc_e pc_a : Addr) (pc_v : Version)
  (p : Perm) (b e a : Addr) (v : Version)
  (src : RegName) (regs : LReg) :
  PC ≠ src ->
  isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) ->
  regs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) ->
  unique_in_registersL regs (Some src) (LCap p b e a v) ->
  pc_a ∉ finz.seq_between b e.
Proof.
  intros Hpc_neq_pc Hvpc Hpc Hunique_regs.
  assert (pc_a ∈ finz.seq_between pc_b pc_e).
  { rewrite isCorrectLPC_isCorrectPC_iff /=  in Hvpc.
    apply isCorrectPC_withinBounds in Hvpc.
    by apply withinBounds_in_seq.
  }
  intro contra.
  rewrite /unique_in_registersL in Hunique_regs.
  eapply map_Forall_lookup_1 in Hunique_regs; eauto.
  destruct (decide (PC = src)); auto.
  apply Hunique_regs.
  rewrite /overlap_wordL /overlap_word //=.
  apply elem_of_finz_seq_between in H,contra.
  destruct H,contra.
  destruct (b <? pc_b)%a eqn:Hb; solve_addr.
Qed.

Lemma update_version_addr_next
  (glmem llmem : LMem) (a : Addr) (v : Version) (lw : LWord) :
  glmem !! (a, v) = Some lw ->
  glmem !! (a, v + 1) = None ->
  update_version_addr glmem a v llmem !! (a, v+1) = Some lw.
Proof.
  intros Hlw Hlw_max.
  by rewrite /update_version_addr Hlw ; simplify_map_eq.
Qed.

Lemma is_valid_updated_lmemory_update_version_region
  (glmem llmem : LMem) (la : list Addr) (v : Version) :
  llmem ⊆ glmem ->
  NoDup la ->
  Forall (λ a : Addr, glmem !! (a, v + 1) = None) la ->
  Forall (λ a' : Addr, is_Some (glmem !! (a', v))) la ->
  is_valid_updated_lmemory glmem llmem la v
    (update_version_region glmem la v llmem).
Proof.
  induction la as [|a la] ; intros Hincl HnoDup Hmax Hsome ; destruct_cons ; cbn
  ; rewrite /is_valid_updated_lmemory //=.
  destruct IHla as (_ & Hgl_llmem & Hla_max & Hla_upd) ; try by destruct_cons.
  split; [|split ; [|split] ] ; cbn.
  - done.
  - done.
  - apply Forall_cons; split; auto. eapply lookup_weaken_None; eauto.
  - rewrite -/(update_version_region glmem la v llmem).
    apply Forall_cons; split; auto.
    + destruct Hsome_a as [lw Hlw].
      exists lw.
      erewrite update_version_addr_next
      ; eauto
      ; rewrite update_version_region_notin_preserves_lmem; eauto.
    + eapply Forall_impl ; try eapply Hla_upd; cbn.
      intros a' [lw' Hlw'].
      destruct (decide (a = a')); subst.
      * rewrite update_version_region_notin_preserves_lmem in Hlw'; eauto.
        exfalso.
        eapply lookup_weaken in Hlw' ; eauto.
        by rewrite Hlw' in Hmax_a.
      * exists lw'; rewrite update_version_addr_lookup_neq; eauto.
Qed.


Definition reg_allows_hash (lregs : LReg) (r : RegName) p b e a v :=
  lregs !! r = Some (LCap p b e a v) ∧ readAllowed p = true.

Definition laddr_leb := pair_fst_leb (A:= Addr) (B:= Version) addr_leb.
Definition lmem_leb := pair_fst_leb (A:= LAddr) (B:= LWord) laddr_leb.

Definition lmemory_get_instrs (lm : LMem) (la : list Addr) (v : Version) : option (list Word) :=
  foldr
    (fun (a : Addr) (opt_instrs_next : option (list Word)) =>
       instrs_next ← opt_instrs_next ;
       w ← lm !! (a,v) ;
       Some ((lword_get_word w)::instrs_next)
    )
    (Some [])
    la.

Definition hash_lmemory_range `{MachineParameters} (lm : LMem) (b e: Addr) (v : Version) : option Z :=
  instructions ← lmemory_get_instrs lm (finz.seq_between b e) v ;
  Some (hash instructions).

Lemma lmeasure_measure_aux `{MP: MachineParameters}
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : list Addr) (v : Version) :
 mem_current_version lm vmap ->
 mem_vmap_root phm lm vmap ->
 (∀ a : Addr, a ∈ la -> vmap !! a = Some v) ->
 lmemory_get_instrs lm la v = memory_get_instrs phm la.
Proof.
  intros Hcur Hroot.
  induction la; intros Hvmap; first done.
  assert ( lmemory_get_instrs lm la v = memory_get_instrs phm la ) as IH.
  { apply IHla.
    intros; apply Hvmap; set_solver.
  }
  rewrite /lmemory_get_instrs /memory_get_instrs !foldr_cons.
  rewrite -/(lmemory_get_instrs lm la v) -/(memory_get_instrs phm la).
  rewrite IH.
  f_equal.
  rewrite /mem_vmap_root in Hroot.
  assert ( vmap !! a = Some v ).
  { apply Hvmap; set_solver. }
  eapply map_Forall_lookup_1 in Hroot ; eauto.
  destruct Hroot as (lw & Hlm_a & Hphm_a & Hcur_lw).
  rewrite Hlm_a Hphm_a.
  by cbn.
Qed.

Lemma lmeasure_measure `{MP: MachineParameters} (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)  :
  forall p b e a v,
  is_cur_word (LCap p b e a v) vmap ->
  state_phys_log_corresponds phr phm lr lm vmap →
  hash_lmemory_range lm b e v = hash_memory_range phm b e.
Proof.
  intros p b e a v Hcur_word [ _ (Hcur & Hroot & _) ].
  unfold hash_lmemory_range, hash_memory_range.
  f_equal.
  rewrite /is_cur_word in Hcur_word.
  eapply lmeasure_measure_aux; eauto.
Qed.

(** Instantiation of the program logic *)

Definition enclaves_agreeUR := authR (gmapUR TIndex (agreeR EIdentity)).
Definition EnclavesAgreePreΣ := #[ GFunctor enclaves_agreeUR].
Class EnclavesAgreePreG Σ := {
    EnclavesAgreePre ::  inG Σ enclaves_agreeUR;
}.
Global Instance subG_EnclavesAgreePreΣ {Σ}:
  subG EnclavesAgreePreΣ Σ →
  EnclavesAgreePreG Σ.
Proof. solve_inG. Qed.

Definition enclaves_exclUR := authUR (gmapUR TIndex (exclR EIdentity)).
Definition EnclavesExclPreΣ := #[ GFunctor enclaves_exclUR].
Class EnclavesExclPreG Σ := {
    EnclavesExclPre ::  inG Σ enclaves_exclUR;
}.
Global Instance subG_EnclavesExclPreΣ {Σ}:
  subG EnclavesExclPreΣ Σ →
  EnclavesExclPreG Σ.
Proof. solve_inG. Qed.

Definition ECUR := excl_authUR ENum.
Definition ECPreΣ := #[ GFunctor ECUR].
Class ECPreG Σ := {
    ECPre ::  inG Σ ECUR;
}.
Global Instance subG_ECPreΣ {Σ}:
  subG ECPreΣ Σ →
  ECPreG Σ.
Proof. solve_inG. Qed.

(* CMRΑ for Cerise *)
Class ceriseG Σ := CeriseG {
  cerise_invG : invGS Σ;
  (* Heap for memory *)
  mem_gen_memG :: gen_heapGS LAddr LWord Σ;
  (* Heap for registers *)
  reg_gen_regG :: gen_heapGS RegName LWord Σ;
  enclaves_agree :: EnclavesAgreePreG Σ;
  enclaves_excl :: EnclavesExclPreG Σ;
  (* The ghost resource of deinitialised enclaves *)
  enclaves_name_prev : gname;
  (* The ghost resource of all enclaves that have ever existed *)
  enclaves_name_all : gname;
  (* ghost names for the resources *)
  enclaves_name_cur : gname;
  (* Heap for EC register *)
  EC_G :: ECPreG Σ;
  EC_name : gname;
}.

 (* Assertions over enclaves *)

Definition enclaves_cur (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesExclPre Σ enclaves_excl)) enclaves_name_cur (● (Excl <$> tbl)).

Definition enclaves_prev (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_prev (● (to_agree <$> tbl)).

Definition enclaves_all (tbl : gmap TIndex EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_all (● (to_agree <$> tbl)).

Definition EC_auth `{ceriseG Σ} (n : ENum) :=
  own (inG0 := @ECPre Σ EC_G) EC_name (●E n).

(* Fragmental resources *)

Definition enclave_cur (eid : TIndex) (identity : EIdentity) `{ceriseG Σ} :=
  own (inG0 := (@EnclavesExclPre Σ enclaves_excl)) enclaves_name_cur (auth_frag {[eid := Excl identity]}).

Definition enclave_prev (eid : TIndex) `{ceriseG Σ} : iProp Σ :=
  ∃ id ,
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_prev (auth_frag {[eid := to_agree id]}).

Definition enclave_all (eid : TIndex) (id : EIdentity) `{ceriseG Σ} : iProp Σ :=
  own (inG0 := (@EnclavesAgreePre Σ enclaves_agree)) enclaves_name_all (auth_frag {[eid := to_agree id]}).

Lemma enclave_all_agree (tidx : TIndex) (id1 id2 : EIdentity) `{ceriseG Σ} :
  enclave_all tidx id1 ∗ enclave_all tidx id2 -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros "[E1 E2]".
  iCombine "E1 E2" as "E".
  rewrite own_valid auth_frag_validI.
  iDestruct "E" as "%E".
  rewrite (singleton_valid tidx) in E.
  by apply to_agree_op_inv in E.
Qed.


#[global] Instance enclave_prev_timeless `{ceriseG Σ} (tidx : TIndex)  : Timeless (enclave_prev tidx).
Proof. apply _. Defined.

#[global] Instance enclave_cur_timeless `{ceriseG Σ} (tidx : TIndex) (eid : EIdentity) : Timeless (enclave_cur tidx eid).
Proof. apply _. Defined.

#[global] Instance enclave_all_timeless `{ceriseG Σ} (tidx : TIndex) (eid : EIdentity) : Timeless (enclave_all tidx eid).
Proof. apply _. Defined.

Definition EC_frag `{ceriseG Σ} (n : ENum) : iProp Σ :=
  own (inG0 := @ECPre Σ EC_G) EC_name (excl_auth_frag n).

#[global] Instance EC_timeless `{ceriseG Σ} (n : ENum) : Timeless (EC_frag n).
Proof. apply _. Defined.

End Logical_mapsto.

Lemma lword_get_word_to_lword (w : Word) (v : Version) :
  lword_get_word (word_to_lword w v) = w.
Proof.
  by destruct w ; auto; destruct sb ; auto.
Qed.

Lemma enclave_cur_compat `{ceriseG Σ} {tidx eid cur_tb} :
  enclave_cur tidx eid -∗ enclaves_cur cur_tb -∗ ⌜ cur_tb !! tidx = Some eid ⌝.
Proof.
  iIntros "Hcur Hcur_tb".
  iDestruct (own_valid_2 with "Hcur_tb Hcur") as "%Hvalid".
  iPureIntro.
  apply auth_both_valid_discrete in Hvalid.
  destruct Hvalid as (Hincl & _).
  apply singleton_included_l in Hincl.
  destruct Hincl as (I' & HeqI' & HII').
  rewrite lookup_fmap in HeqI'.
  destruct I';
    last by (destruct (cur_tb !! tidx); apply leibniz_equiv in HeqI'; inversion HeqI').
  rewrite Excl_included in HII'.
  apply leibniz_equiv in HII'; subst.
  apply leibniz_equiv in HeqI'.
  destruct (cur_tb !! tidx);
    now inversion HeqI'.
Qed.


Lemma enclave_update_deinit `{ceriseG Σ} {cur_tb prev_tb tidx I} :
  cur_tb ##ₘ prev_tb ->
  enclaves_cur cur_tb -∗ enclaves_prev prev_tb -∗ enclave_cur tidx I ==∗ enclave_prev tidx ∗ enclaves_cur (delete tidx cur_tb) ∗ enclaves_prev (insert tidx I prev_tb).
Proof.
  iIntros (Hdisj) "Hcur_tb Hprev_tb Hcur".
  iPoseProof (enclave_cur_compat with "Hcur Hcur_tb") as "%Hcurtbtidx".
  iCombine "Hcur_tb Hcur" as "Hcurm".
  iMod (own_update with "Hcurm") as "Hcurm".
  { eapply (auth_update_dealloc _ _ (excl.Excl <$> (delete tidx cur_tb))).
    rewrite fmap_delete.
    now apply (@delete_singleton_local_update TIndex _ _ (excl EIdentity) (Excl <$> cur_tb)).
  }
  iMod (own_update with "Hprev_tb") as "(Hprev_tb & Hprev)".
  { eapply (auth_update_alloc _ (to_agree <$> (insert tidx I prev_tb)) {[ tidx := to_agree I]} ).
    rewrite fmap_insert -insert_empty.
    eapply alloc_singleton_local_update; last done.
    rewrite lookup_fmap.
    enough (prev_tb !! tidx = None) as Hprev_tbNone by now rewrite Hprev_tbNone.
    now apply (map_disjoint_Some_l _ _ _ _ Hdisj Hcurtbtidx).
  }
  iModIntro.
  iSplitL "Hprev".
  - now iExists I.
  - now iFrame.
Qed.



Definition state_interp_logical (σ : cap_lang.state) `{ReservedAddresses} `{!ceriseG Σ} : iProp Σ :=
  ∃ lr lm vmap (cur_tb prev_tb all_tb : gmap TIndex EIdentity) ,
    gen_heap_interp lr ∗
    gen_heap_interp lm ∗
    ⌜cur_tb = σ.(etable)⌝ ∗
    enclaves_cur cur_tb ∗
    enclaves_prev prev_tb ∗
    enclaves_all all_tb ∗
    EC_auth σ.(enumcur) ∗
    ⌜dom cur_tb ## dom prev_tb⌝ ∗
    ⌜dom (cur_tb ∪ prev_tb) = list_to_set (seq 0 σ.(enumcur))⌝ ∗ (**)
    ⌜cur_tb ##ₘ prev_tb⌝ ∗
    ⌜cur_tb ∪ prev_tb = all_tb⌝ ∗
    ⌜state_phys_log_corresponds σ.(reg) σ.(mem) lr lm vmap⌝.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{ReservedAddresses} `{ceriseg: !ceriseG Σ} : irisGS cap_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := state_interp_logical σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _}.

(* Ltac destruct_cons_upd := *)
(*   match goal with *)
(*      | Hupd : update_cur_version_region ?lmem ?lm ?vmap (?a :: ?la) = (?lmem', ?lm', ?vmap') *)
(*        |- _ => *)
(*          let lmem0 := fresh lmem "0" in *)
(*          let lm0 := fresh lm "0" in *)
(*          let vmap0 := fresh vmap "0" in *)
(*          let Hupd0 := fresh Hupd "0" in *)
(*          apply update_cur_version_region_cons in Hupd *)
(*          ; destruct Hupd as (lmem0 & lm0 & vmap0 & Hupd & Hupd0) *)
(*    end. *)
(* Ltac destruct_cons_hook2 := destruct_cons_upd || destruct_cons_hook1. *)
(* Ltac destruct_cons_hook ::= destruct_cons_hook2. *)

(* Notations for fragmental resources *)
Notation "EC⤇ n" := (EC_frag n)
                      (at level 20, n at level 50, format "EC⤇ n") : bi_scope.

(* Points to predicates for logical registers *)
Notation "r ↦ᵣ{ q } lw" := (mapsto (L:=RegName) (V:=LWord) r q lw)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q } lw") : bi_scope.
Notation "r ↦ᵣ lw" := (mapsto (L:=RegName) (V:=LWord) r (DfracOwn 1) lw) (at level 20) : bi_scope.

(* Points-to predicates for logical memory *)
Notation "la ↦ₐ{ q } lw" := (mapsto (L:=LAddr) (V:=LWord) la q lw)
  (at level 20, q at level 50, format "la  ↦ₐ{ q }  lw") : bi_scope.
Notation "la ↦ₐ lw" := (mapsto (L:=LAddr) (V:=LWord) la (DfracOwn 1) lw) (at level 20) : bi_scope.

Declare Scope LAddr_scope.
Delimit Scope LAddr_scope with la.

Notation eqb_laddr := (λ (a1 a2: LAddr), (a1.1 =? a2.1)%a && (a1.2 =? a2.2)).
Notation "a1 =? a2" := (eqb_laddr a1 a2) : LAddr_scope.

Section machine_param.
  Context `{MachineParameters}.

  Definition decodeInstrWL (lw : LWord) :=
    decodeInstrW (lword_get_word lw).

  Definition encodeInstrWL (i : instr) : LWord := LInt (encodeInstr i).

  Lemma decode_encode_instrLW_inv (i: instr):
    decodeInstrWL (encodeInstrWL i) = i.
  Proof. apply decode_encode_instr_inv. Qed.

  Definition encodeInstrsLW : list instr → list LWord :=
    map encodeInstrWL.

  Definition encodeLWordType (lw : LWord) : Z :=
    encodeWordType (lword_get_word lw).

  (* Definition decodeLWordType (z : Z) : LWord := *)
  (*   (decodeWordType i). *)

  Lemma encodeLWordType_correct (w w' : LWord) :
    match w,w' with
    | LCap _ _ _ _ _, LCap _ _ _ _ _ => encodeLWordType w = encodeLWordType w'
    | LSealRange _ _ _ _, LSealRange _ _ _ _ => encodeLWordType w = encodeLWordType w'
    | LWSealed _ _, LWSealed _ _ => encodeLWordType w = encodeLWordType w'
    | LInt _, LInt _ => encodeLWordType w = encodeLWordType w'
    | _, _ => encodeLWordType w <> encodeLWordType w'
    end.
  Proof.
    pose proof (encodeWordType_correct (lword_get_word w) (lword_get_word w')).
    destruct w, w'; cbn in *; try done
    ; destruct sb; cbn in *; try done
    ; destruct sb0; cbn in *; try done.
  Qed.


  Definition lwt_cap := LCap O 0%a 0%a 0%a 0.
  Definition lwt_sealrange := LSealRange (false, false) 0%ot 0%ot 0%ot.
  Definition lwt_sealed := LWSealed 0%ot (LSCap O 0%a 0%a 0%a 0).
  Definition lwt_int := LInt 0.

End machine_param.

Ltac solve_encodeLWordType :=
  match goal with
  | H: _ |- encodeLWordType ?x = encodeLWordType ?y =>
      try reflexivity
      ; pose proof (encodeLWordType_correct x y) as Heq
      ; unfold wt_cap, wt_int, wt_sealrange, wt_cap ; simpl in Heq ; auto
  end.

Ltac simpl_encodeLWordType :=
  match goal with
  | H: _ |- context G [encodeLWordType (LCap ?p ?b ?e ?a ?v)] =>
      rewrite (_: encodeLWordType (LCap p b e a v) = encodeLWordType lwt_cap) ; last solve_encodeLWordType

  | H: _ |- context G [encodeLWordType (LSealRange ?p ?b ?e ?a)] =>
      rewrite (_: encodeLWordType (LSealRange p b e a) = encodeLWordType lwt_sealrange) ; last solve_encodeLWordType

  | H: _ |- context G [encodeLWordType (LInt ?n)] =>
      rewrite (_: encodeLWordType (LInt n) = encodeLWordType lwt_int) ; last solve_encodeLWordType

  | H: _ |- context G [encodeLWordType (LWSealed ?o ?s)] =>
      rewrite (_: encodeLWordType (LWSealed o s) = encodeLWordType lwt_sealed) ; last solve_encodeLWordType
  end.

Lemma encodeLWordType_correct_cap `{MachineParameters} : forall p b e a v p' b' e' a' v',
  encodeLWordType (LCap p b e a v) = encodeLWordType (LCap p' b' e' a' v').
  intros; solve_encodeLWordType.
Qed.

Lemma encodeLWordType_correct_int `{MachineParameters} : forall z z',
  encodeLWordType (LInt z) = encodeLWordType (LInt z').
  intros; solve_encodeLWordType.
Qed.

Lemma encodeLWordType_correct_sealrange `{MachineParameters} : forall p b e a p' b' e' a',
  encodeLWordType (LSealRange p b e a) = encodeLWordType (LSealRange p' b' e' a').
Proof.
  intros; solve_encodeLWordType.
Qed.

Lemma encodeLWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeLWordType (LWSealed o s) = encodeLWordType (LWSealed o' s').
  intros; solve_encodeLWordType.
Qed.


(** Miscellaneous about logical regions *)
(* TODO move definition to regions.v ? *)
Definition logical_region_map
  (la : list Addr) (lws : list LWord) (v : Version) : gmap LAddr LWord :=
  list_to_map (zip (logical_region la v) lws).

Lemma logical_region_notin
  (la : list Addr) (a : Addr) (v v' : Version) (lws : list LWord) :
  length lws = length la
  -> a ∉ la
  -> (logical_region_map la lws v) !! (a,v') = None.
Proof.
  intros Hlen Hnotin.
  apply not_elem_of_list_to_map_1; cbn.
  intro Hcontra.
  rewrite fst_zip in Hcontra ; eauto; last (rewrite map_length ; lia).
  apply elem_of_list_fmap in Hcontra.
  destruct Hcontra as (? & ? & ?); simplify_eq; set_solver.
Qed.

Lemma logical_region_version_neq
  (la : list Addr) (a : Addr) (v v' : Version) (lws : list LWord) :
  length lws = length la
  -> v ≠ v'
  -> logical_region_map la lws v !! (a, v') = None.
Proof.
  intros Hlen Hneq.
  apply not_elem_of_list_to_map_1; cbn.
  intro Hcontra.
  rewrite fst_zip in Hcontra ; eauto; last (rewrite map_length ; lia).
  apply elem_of_list_fmap in Hcontra.
  destruct Hcontra as (? & ? & ?); simplify_eq; lia.
Qed.

Lemma logical_region_map_cons
  (la : list Addr) (a : Addr) (v : Version) (lws : list LWord) (lw : LWord ):
  logical_region_map (a :: la) (lw :: lws) v =
  <[ (a,v) := lw ]> (logical_region_map la lws v).
Proof.
  by cbn.
Qed.

Lemma logical_region_map_some_inv
  (a : Addr) ( v v' : Version )
  (la : list Addr) (lws : list LWord) :
  NoDup la ->
  length lws = length la ->
  is_Some (logical_region_map la lws v !! (a, v')) ->
  (v' = v) /\ (a ∈ la).
Proof.
  intros HNoDup Hlen [lw Hlw].
  apply elem_of_list_to_map in Hlw.
  { apply elem_of_zip_l in Hlw.
    apply elem_of_list_fmap in Hlw.
    by destruct Hlw as (? & ? & ?); simplify_eq.
  }
  {
    rewrite fst_zip ; eauto; last  (rewrite map_length; lia).
    apply NoDup_fmap; auto.
    by intros x y Heq ; simplify_eq.
  }
Qed.

Lemma logical_region_map_lookup_versions
  (la : list Addr) (a' : Addr) (v v' : Version) (lws : list LWord) :
  NoDup la ->
  a' ∈ la ->
  length lws = length la ->
  (logical_region_map la lws v) !! (a', v)
  = (logical_region_map la lws v') !! (a', v').
Proof.
  move: a' v v' lws.
  induction la as [|a la IHla]; intros * HNoDup Ha'_in_la Hlen.
  - cbn in *; set_solver.
  - cbn in Hlen; destruct lws as [|lw lws] ; simplify_eq.
    injection Hlen ; clear Hlen ; intro Hlen.
    destruct_cons.
    destruct Ha'_in_la; cbn ; simplify_map_eq; first done.
    rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
    rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
    by apply IHla.
Qed.

Lemma logical_region_map_inv
  (lmem : LMem) (la : list Addr) (v : Version) :
  NoDup la ->
  Forall (λ a : Addr, is_Some (lmem !! (a, v))) la ->
  ∃ lws : list LWord,
    length lws = length la ∧ (logical_region_map la lws v) ⊆ lmem.
Proof.
  move: lmem v.
  induction la as [|a la IHla] ; intros * HNoDup HnextMap.
  - cbn in *. exists []. split; auto. apply map_empty_subseteq.
  - destruct_cons; destruct HnextMap_a as [lwa Hlwa].
    eapply IHla in HnextMap; eauto.
    destruct HnextMap as (lws & Hlen & Hincl).
    exists (lwa::lws).
    split ; auto; first (cbn ; lia).
    rewrite logical_region_map_cons.
    eapply insert_subseteq_l; eauto.
Qed.

Lemma logical_region_map_disjoint
  (la1 la2 : list Addr) (lw1 lw2 : list LWord) (v1 v2 : Version) :
  la1 ## la2 ->
  length la1 = length lw1 ->
  logical_region_map la1 lw1 v1 ##ₘ logical_region_map la2 lw2 v2.
Proof.
  intros Hdis Hlen.
  rewrite /logical_region_map.
  eapply map_disjoint_list_to_map_zip_l ; first by rewrite map_length.
  rewrite Forall_forall.
  intros a Ha.
  apply elem_of_list_fmap in Ha.
  destruct Ha as (x & -> & Hx).
  apply not_elem_of_list_to_map_1.
  intro Hcontra.
  rewrite elem_of_list_fmap in Hcontra.
  destruct Hcontra as ( [y vy] & ? & Hy); simplify_eq.
  cbn in *.
  apply elem_of_zip_l in Hy.
  apply elem_of_list_fmap in Hy.
  destruct Hy as (y' & -> & Hy').
  set_solver.
Qed.

Lemma logical_region_NoDup (la : list Addr) (v : Version) :
  NoDup la -> NoDup (logical_region la v).
Proof.
  intros Hla.
  rewrite /logical_region.
  apply NoDup_fmap; auto.
  by intros x1 x2 Hx; simplify_eq.
Qed.

Lemma logical_region_length (la : list Addr) (v : Version) :
  length (logical_region la v) = length la.
Proof. by rewrite map_length. Qed.


Definition logical_range_map
  (b e : Addr) (lws : list LWord) (v : Version) : gmap LAddr LWord :=
  list_to_map (zip (logical_region (finz.seq_between b e) v) lws).

Lemma logical_range_notin
  (b e : Addr) (a : Addr) (v v' : Version) (lws : list LWord) :
  length lws = length (finz.seq_between b e)
  -> a ∉ (finz.seq_between b e)
  -> (logical_range_map b e lws v) !! (a,v') = None.
Proof.
  intros.
  eapply logical_region_notin; eauto.
Qed.

Lemma logical_range_version_neq
  (b e : Addr) (a : Addr) (v v' : Version) (lws : list LWord) :
  length lws = length (finz.seq_between b e)
  -> v ≠ v'
  -> logical_range_map b e lws v !! (a, v') = None.
Proof.
  intros.
  eapply logical_region_version_neq; eauto.
Qed.

Lemma logical_range_map_some_inv
  (a : Addr) ( v v' : Version )
  (b e : Addr) (lws : list LWord) :
  length lws = length (finz.seq_between b e) ->
  is_Some (logical_range_map b e lws v !! (a, v')) ->
  (v' = v) /\ (a ∈ (finz.seq_between b e)).
Proof.
  intros.
  eapply logical_region_map_some_inv; eauto.
  eapply finz_seq_between_NoDup.
Qed.

Lemma logical_range_map_lookup_versions
  (b e : Addr) (a' : Addr) (v v' : Version) (lws : list LWord) :
  a' ∈ finz.seq_between b e ->
  length lws = length (finz.seq_between b e) ->
  (logical_range_map b e lws v) !! (a', v)
  = (logical_range_map b e lws v') !! (a', v').
Proof.
  intros.
  apply logical_region_map_lookup_versions; eauto.
  eapply finz_seq_between_NoDup.
Qed.

Lemma logical_range_map_inv
  (lmem : LMem) (b e : Addr) (v : Version) :
  Forall (λ a : Addr, is_Some (lmem !! (a, v))) (finz.seq_between b e) ->
  ∃ lws : list LWord,
    length lws = length (finz.seq_between b e) ∧ (logical_range_map b e lws v) ⊆ lmem.
Proof.
  intros.
  apply logical_region_map_inv; eauto.
  eapply finz_seq_between_NoDup.
Qed.

Lemma logical_range_map_insert (b e : Addr) (v : Version) (w w': LWord) (lw : list LWord) :
  (b < e)%a ->
  <[ (b,v) := w']> (logical_range_map b e (w::lw) v) = logical_range_map b e (w'::lw) v.
Proof.
  intros Hb.
  rewrite /logical_range_map.
  rewrite finz_seq_between_cons //.
  cbn.
  by rewrite insert_insert.
Qed.

Lemma logical_range_map_disjoint
  (b e : Addr) (lws : list LWord) (v : Version)
  (b' e' : Addr) (lws' : list LWord) (v' : Version) :
  length (finz.seq_between b e) = length lws ->
  finz.seq_between b e ## finz.seq_between b' e' ->
  logical_range_map b e lws v ##ₘ logical_range_map b' e' lws' v'.
Proof.
  intros Hlen Hdis.
  rewrite /logical_range_map.
  apply map_disjoint_list_to_map_zip_l.
  { rewrite logical_region_length; cbn ; f_equal; done. }
  apply Forall_forall.
  intros y Hy.
  apply not_elem_of_list_to_map.
  intro Hcontra.
  rewrite elem_of_list_fmap in Hcontra.
  destruct Hcontra as ([ [y' vy'] wy'] & -> & Hcontra).
  eapply elem_of_zip_l in Hcontra.
  rewrite /logical_region in Hy, Hcontra.
  rewrite !elem_of_list_fmap in Hy,Hcontra.
  destruct Hy as (? & ? & Hy); simplify_eq.
  destruct Hcontra as (? & ? & Hy'); simplify_eq.
  cbn in H; simplify_eq.
  set_solver.
Qed.

Lemma logical_range_map_disjoint_version
  (b e b' e' : Addr) (lws lws' : list LWord) (v v' : Version) :
  length (finz.seq_between b e) = length lws ->
  v ≠ v' ->
  logical_range_map b e lws v ##ₘ logical_range_map b' e' lws' v'.
Proof.
  intros Hlen Hneq.
  rewrite /logical_range_map.
  apply map_disjoint_list_to_map_zip_l.
  { rewrite logical_region_length; cbn ; f_equal; done. }
  apply Forall_forall.
  intros y Hy.
  apply not_elem_of_list_to_map.
  intro Hcontra.
  rewrite elem_of_list_fmap in Hcontra.
  destruct Hcontra as ([ [y' vy'] wy'] & -> & Hcontra).
  eapply elem_of_zip_l in Hcontra.
  rewrite /logical_region in Hy, Hcontra.
  rewrite !elem_of_list_fmap in Hy,Hcontra.
  destruct Hy as (? & ? & _); simplify_eq.
  destruct Hcontra as (? & ? & _); simplify_eq.
  cbn in H; simplify_eq.
Qed.

Lemma hash_lmemory_range_delete_notin
  (lmem : LMem) (l : list Addr) (v : Version) (a : Addr) (lws : list LWord) :
  a ∉ l ->
  NoDup l ->
  length lws = length l ->
  lmemory_get_instrs (delete (a, v) lmem) l v = lmemory_get_instrs lmem l v.
Proof.
  generalize dependent a.
  generalize dependent lws.
  generalize dependent v.
  generalize dependent lmem.
  induction l as [|a' l]; intros lmem v lws a Hnotin Hnodup Hlen; first by cbn.
  destruct lws as [|lw1 lws] ; first (by cbn in Hlen); cbn in Hlen; simplify_eq.
  apply NoDup_cons in Hnodup as [Ha_notin_l Hnodup].
  apply not_elem_of_cons in Hnotin as [Ha_neq_a' Hnotin].
  opose proof (IHl lmem v lws a Hnotin Hnodup Hlen) as IH ; eauto.
  rewrite /= IH.
  apply option_bind_ext_fun.
  intros w.
  rewrite lookup_delete_ne; first done.
  intro ; simplify_eq.
Qed.

Lemma hash_lmemory_range_correct_aux
  (lmem : LMem) (l : list Addr) (v : Version) (lws : list LWord) :
  NoDup l ->
  length lws = length l ->
  list_to_map (zip (logical_region l v) lws) ⊆ lmem ->
  lmemory_get_instrs lmem l v = Some (lword_get_word <$> lws).
Proof.
  generalize dependent lws.
  generalize dependent v.
  generalize dependent lmem.
  induction l; intros lmem v lws Hnodup Hlen Hsubset.
  + apply nil_length_inv in Hlen; simplify_eq.
    by rewrite fmap_nil.
  + destruct lws as [|lw1 lws] ; first (by cbn in Hlen).
    apply NoDup_cons in Hnodup as [Ha_notin_l Hnodup].
    cbn in Hlen ; simplify_eq.
    cbn in Hsubset.
    apply insert_weaken in Hsubset as Ha_lmem.
    rewrite fmap_cons.
    rewrite /lmemory_get_instrs.
    apply insert_delete_subseteq in Hsubset.
    2: { rewrite -not_elem_of_list_to_map.
         intro Hcontra.
         rewrite elem_of_list_fmap in Hcontra.
         destruct Hcontra as ([x vx] & Hx & Hcontra)
         ; cbn in Hx ; simplify_eq.
         apply elem_of_zip_l in Hcontra.
         rewrite elem_of_list_fmap in Hcontra.
         destruct Hcontra as (y & Hy & Hcontra)
         ; cbn in Hy ; simplify_eq.
         set_solver.
    }
    rewrite -/(logical_region l v) in Hsubset.
    opose proof (IHl (delete (a, v) lmem) v lws Hnodup Hlen _) as IH ; eauto.
    erewrite hash_lmemory_range_delete_notin in IH; eauto.
    rewrite /= -/(lmemory_get_instrs lmem l v) IH /= Ha_lmem /=.
    done.
Qed.

Lemma hash_lmemory_range_correct `{MP: MachineParameters} (lmem : LMem) (b e : Addr) (v : Version) (lws : list LWord) (eid : Z) :
  length lws = length (finz.seq_between b e) ->
  logical_range_map b e lws v ⊆ lmem ->
  hash_lmemory_range lmem b e v = Some eid ->
  eid = hash (lword_get_word <$> lws).
Proof.
  intros Hlen Hlmem Hhash.
  rewrite /logical_range_map in Hlmem.
  rewrite /hash_lmemory_range in Hhash.
  rewrite bind_Some in Hhash.
  destruct Hhash as (instrs & Hinstrs & ?); simplify_eq.
  erewrite (hash_lmemory_range_correct_aux) in Hinstrs
  ; eauto; simplify_eq; first done.
  apply finz_seq_between_NoDup.
Qed.

(* Transform Reg into LReg *)
Definition register_to_lregister (reg : Reg) ( v : Version ) : LReg :=
  fmap (fun w => word_to_lword w v) reg.

Lemma register_to_lregister_lookup (reg : Reg) (r : RegName) (w : Word) (v : Version) :
  reg !! r = Some w ->
  register_to_lregister reg v !! r = Some (word_to_lword w v).
Proof.
  intros Hr.
  rewrite /register_to_lregister.
  by rewrite lookup_fmap Hr /=.
Qed.

Lemma register_to_lregister_delete (reg : Reg) (r : RegName) (v : Version) :
  delete r (register_to_lregister reg v) = (register_to_lregister (delete r reg) v).
Proof. by rewrite /register_to_lregister fmap_delete. Qed.

Lemma lreg_strip_register_to_lregister (reg : Reg) (v : Version) :
  lreg_strip (register_to_lregister reg v) = reg.
Proof.
  induction reg using map_ind; cbn in *; first done.
  rewrite /register_to_lregister /lreg_strip !fmap_insert lword_get_word_to_lword.
  rewrite -/(register_to_lregister m v) -/(lreg_strip _).
  by rewrite IHreg.
Qed.

(* Transform Mem into LMem *)
Definition memory_to_lmemory (mem : Mem) ( v : Version ) : LMem :=
  kmap (fun a => (a,v)) (fmap (fun w => word_to_lword w v) mem).

Lemma memory_to_lmemory_insert (m : Mem) (a : Addr) (w : Word) (v : Version):
  memory_to_lmemory (<[a:=w]> m) v = <[(a,v):= word_to_lword w v]> (memory_to_lmemory m v).
Proof.
  rewrite /memory_to_lmemory.
  by rewrite fmap_insert kmap_insert.
Qed.

Lemma memory_to_lmemory_lookup (m : Mem) (a : Addr) (v : Version):
  memory_to_lmemory m v !! (a, v) = (λ w, word_to_lword w v) <$> (m!!a).
Proof.
  rewrite /memory_to_lmemory.
  by rewrite lookup_kmap lookup_fmap.
Qed.

Lemma memory_to_lmemory_union (m1 m2 : Mem) (v : Version) :
  memory_to_lmemory (m1 ∪ m2) v =
  (memory_to_lmemory m1 v) ∪  (memory_to_lmemory m2 v).
Proof.
  by rewrite /memory_to_lmemory map_fmap_union kmap_union.
Qed.

Lemma memory_to_lmemory_subseteq (m1 m2 : Mem) (v : Version) :
  m1 ⊆ m2 -> memory_to_lmemory m1 v ⊆ memory_to_lmemory m2 v.
Proof.
  intros Hm.
  rewrite /memory_to_lmemory.
  apply kmap_subseteq; first by intros x y ?; simplify_eq.
  by apply map_fmap_mono.
Qed.

Lemma memory_to_lmemory_disjoint (m1 m2 : Mem) (v : Version) :
  (m1 ##ₘ m2) ->
  ((memory_to_lmemory m1 v) ##ₘ (memory_to_lmemory m2 v)).
Proof.
  intros Hm.
  rewrite /memory_to_lmemory.
  apply map_disjoint_kmap; first by intros x y ?; simplify_eq.
  by apply map_disjoint_fmap.
Qed.

Lemma memory_to_lmemory_mk_logical_region_map la ws v:
  memory_to_lmemory (list_to_map (zip la ws)) v
  = logical_region_map la ((λ w : Word, word_to_lword w v) <$> ws) v.
Proof.
  revert la ws.
  induction la as [|a la]; intros ws ; cbn in *.
  - rewrite /memory_to_lmemory.
    by rewrite fmap_empty kmap_empty.
  - destruct ws as [|w ws]; cbn.
    + rewrite /memory_to_lmemory.
      by rewrite fmap_empty kmap_empty.
    + rewrite memory_to_lmemory_insert.
      by rewrite IHla.
Qed.

(* When reasoning about initial state, memory must be complete w.r.t. the registers.
   In other words, every reachable addresses must be contained in the memory.
   That's required by `state_phys_log_corresponds`
 *)
Definition is_complete_word (w : Word) (m : Mem) :=
  match w with
  | WCap p b e a
  | WSealed _ (SCap p b e a) => (Forall (fun a => is_Some( m !! a ) ) (finz.seq_between b e))
  | _ => True
  end.

Definition is_complete_registers (reg : Reg) (m : Mem) :=
  map_Forall ( fun r w => is_complete_word w m) reg.
Definition is_complete_memory (m : Mem) :=
  map_Forall ( fun r w => is_complete_word w m) m.

Lemma state_phys_log_corresponds_complete `{ReservedAddresses} (m : Mem) (reg : Reg) (v : Version)  :
  v = init_version ->
  is_complete_memory m ->
  is_complete_registers reg m ->
  state_phys_log_corresponds reg m (register_to_lregister reg v) (memory_to_lmemory m v) (gset_to_gmap v (dom m)).
Proof.
  intros Hv Hm_complete Hreg_complete.
  rewrite /state_phys_log_corresponds.
  split.
  + rewrite /reg_phys_log_corresponds.
    split.
    ++ apply lreg_strip_register_to_lregister.
    ++ rewrite /is_cur_regs.
       apply map_Forall_lookup_2.
       intros r lw Hr.
       rewrite /is_cur_word.
       destruct lw as [ z | sb | ot sb ] ; try done.
       all: destruct sb; auto.
       all: rewrite /register_to_lregister lookup_fmap_Some in Hr.
       all: destruct Hr as (w & Hw & Hwr).
       all: destruct w as [z | sb' | ot' sb']; try destruct sb'; cbn in Hw; simplify_eq.
       all: intros x Hx.
       all: apply lookup_gset_to_gmap_Some.
       all: split; last done.
       all: eapply (map_Forall_lookup_1) in Hreg_complete; eauto.
       all: rewrite elem_of_list_lookup in Hx.
       all: destruct Hx as [kx Hkx].
       all: eapply Forall_lookup in Hreg_complete; eauto.
       all: by rewrite elem_of_dom.
  + rewrite /mem_phys_log_corresponds.
    split;[|split].
    ++ rewrite /mem_current_version.
       apply map_Forall_lookup_2.
       intros la lw Hla.
       rewrite /is_legal_address.
       destruct la as (a', v').
       destruct (decide (v = v')) ; simplify_eq ; cycle 1.
       { rewrite /memory_to_lmemory in Hla.
         apply lookup_kmap_Some in Hla; last (by intros x y ?; simplify_eq).
         destruct Hla as (? & ? & _).
         simplify_eq.
       }
       exists init_version.
       cbn.
       split; [|split].
       +++ rewrite /is_cur_addr //=.
           rewrite lookup_gset_to_gmap_Some; split; auto.
           rewrite /memory_to_lmemory lookup_kmap lookup_fmap_Some in Hla.
           destruct Hla as (w & Hlw & Ha).
           by rewrite elem_of_dom.
       +++ lia.
       +++ by rewrite Hla.
    ++ rewrite /mem_vmap_root.
       apply map_Forall_lookup_2.
       intros a' v' Ha'.
       apply lookup_gset_to_gmap_Some in Ha'; destruct Ha' as [Ha' ->].
       apply elem_of_dom in Ha'. destruct Ha' as [w' Ha'].
       exists (word_to_lword w' v').
       split; [|split].
    * by rewrite lookup_kmap lookup_fmap Ha'; cbn.
    * rewrite Ha' /lword_get_word /word_to_lword /=.
      destruct w'; auto.
      all: destruct sb; auto.
    * rewrite /is_cur_word.
      destruct w' ; cbn; auto.
      all: destruct sb; cbn; auto.
      all: intros x Hx.
      all: apply lookup_gset_to_gmap_Some.
      all: split; last done.
      all: eapply (map_Forall_lookup_1) in Hm_complete; eauto.
      all: rewrite elem_of_list_lookup in Hx.
      all: destruct Hx as [kx Hkx].
      all: eapply Forall_lookup in Hm_complete; eauto.
      all: by rewrite elem_of_dom.
      ++ rewrite /mem_gcroot.
         apply map_Forall_lookup_2.
         intros a' v' Ha' Ha'_reserved.
         rewrite /init_version; cbn.
         apply lookup_gset_to_gmap_Some in Ha';simplify_eq.
         by destruct Ha'.
Qed.

Definition isPermLWord (w : LWord) (p : Perm): bool :=
  match w with
  | LCap p' _ _ _ _  => isPerm p p'
  | _ => false
  end.
