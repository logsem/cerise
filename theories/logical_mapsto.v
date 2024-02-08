From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
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

(* Getters lword and laddr *)
Definition lsealable_get_sealable (lsb : LSealable) : Sealable :=
  match lsb with
  | LSCap p b e a v => SCap p b e a
  | LSSealRange p ob oe oa => SSealRange p ob oe oa
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

Definition is_lcap (w : LWord) :=
  match w with
    | LCap p b e a v | LSealedCap _ p b e a v => true
    | _ => false end.

Definition get_lcap (w : LWord) : option LSealable :=
  match w with
    | LCap p b e a v | LSealedCap _ p b e a v => Some (LSCap p b e a v)
    | _ => None
  end.
Lemma get_is_lcap lw lsb : get_lcap lw = Some lsb → is_lcap lw = true.
Proof. unfold get_lcap, is_lcap. repeat (case_match); auto. all: intro; by exfalso. Qed.

Lemma get_is_lcap_inv (lw : LWord) :
  is_lcap lw = true -> exists p b e a v, get_lcap lw = Some (LSCap p b e a v).
Proof.
  intros.
  destruct_lword lw ; cbn in * ; try (exfalso ; congruence).
  all: eexists _,_,_,_,_; eauto.
Qed.

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

Definition VMap : Type := gmap Addr Version.
Definition LReg := gmap RegName LWord.
Definition LMem := gmap LAddr LWord.
Definition LDFrac := gmap LAddr iris.algebra.dfrac.dfrac.

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

Global Instance is_cur_addr_dec (la : LAddr) (vmap : VMap) :
  Decision (is_cur_addr la vmap).
Proof.
  rewrite /is_cur_addr.
  destruct (vmap !! la.1) eqn:Heq; solve_decision.
Defined.

Lemma is_cur_addr_same (a : Addr) (v v' : Version) (cur_map : VMap) :
  is_cur_addr (a, v) cur_map ->
  is_cur_addr (a, v') cur_map ->
  v = v'.
Proof.
  rewrite /is_cur_addr /=.
  move=> Hcur_a Hcur_a'.
  by rewrite Hcur_a in Hcur_a' ; simplify_eq.
Qed.

Definition is_lword_version (lw : LWord) (p : Perm) (b e a : Addr) (v : Version) : Prop :=
  (get_lcap lw) = Some (LSCap p b e a v).

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

(* TODO I think that there is a duplicate -ish somewhere *)
Lemma is_cur_lword_lea
  (vmap : VMap) (p : Perm) (b e a a' : Addr) (v : Version):
  is_cur_word (LCap p b e a v) vmap ->
  is_cur_word (LCap p b e a' v) vmap.
Proof.
  move=> Hcur a0 Ha0.
  by apply Hcur.
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

Lemma insert_reg_lreg_strip (lregs : LReg) (r : RegName) (lw : LWord) :
  lregs !! r = Some lw ->
  <[ r := lword_get_word lw ]> (lreg_strip lregs) = lreg_strip lregs.
Proof.
  intros Hr.
  rewrite -/lreg_strip -fmap_insert insert_id //.
Qed.

Lemma insert_lcap_lreg_strip
  (lregs : LReg) (r : RegName) (lw : LWord):
  is_lcap lw = true ->
  lregs !! r = Some lw ->
  <[ r := (lword_get_word lw) ]> (lreg_strip lregs) = lreg_strip lregs.
Proof.
  intros Hlw Hr.
  rewrite -fmap_insert insert_id //=.
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

Lemma is_lcap_update_version_lword (lw : LWord):
  is_lcap (next_version_lword lw) = is_lcap lw.
Proof.
  by destruct_lword lw; cbn.
Qed.













(* state_phys_log_corresponds definition *)

(** The `reg_phys_log_corresponds` states that, the physical register file `phr` corresponds
    to the the logical register file `lr`, according to the view map `cur_map` if:
    - the content of the register `phr` is the same as the words in `lr` w/o the version
    - the version of the capabilities in `lr` are the same as the version of its addresses
      in the view map `cur_map`
 *)
Definition reg_phys_log_corresponds (phr : Reg) (lr : LReg) (vmap : VMap) :=
    lreg_strip lr = phr
    ∧ map_Forall (λ _ lw, is_cur_word lw vmap) lr.

(** for each logical addresses in the logical memory,
    - the version is less or equal the current version of the address
    - the current version of the address also exists in the logical memory *)
Definition mem_current_version (lm : LMem) (vmap : VMap) : Prop :=
  map_Forall
    (λ la _ ,
      ∃ cur_v,
        is_cur_addr (laddr_get_addr la, cur_v) vmap
        ∧ laddr_get_version la <= cur_v
        /\ is_Some ( lm !! (laddr_get_addr la, cur_v))
    ) lm.

(** for all entries in the view map,
    - it exists is a logical word `lw` in the logical memory `lm`
      ( i.e. dom(cur_map) ⊆ dom(lm) )
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

Definition mem_phys_log_corresponds (phm : Mem) (lm : LMem) (vmap : VMap) :=
  (mem_current_version lm vmap) ∧ (mem_vmap_root phm lm vmap).

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
  (phr : Reg) (lr : LReg) (cur_map : VMap)
  (src : RegName) (p : Perm)  (b e a a' : Addr) (v : Version) :
  reg_phys_log_corresponds phr lr cur_map  ->
  lr !! src = Some (LCap p b e a v) ->
  a' ∈ finz.seq_between b e ->
  is_cur_addr (a', v) cur_map.
Proof.
  move=> Hreg_inv Hlr_src Ha'.
  eapply lreg_corresponds_read_iscur in Hlr_src; eauto.
  apply is_cur_lword_lea with (a' := a') in Hlr_src.
  eapply cur_lword_cur_addr; eauto.
  rewrite /is_lword_version //=.
  apply elem_of_finz_seq_between in Ha'.
  apply withinBounds_true_iff.
  solve_addr.
Qed.




(* Lemmas about lmem_corresponds *)
Lemma lmem_corresponds_read_iscur
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm vmap →
  is_cur_addr la vmap →
  lm !! la = Some lw →
  is_cur_word lw vmap.
Proof.
  intros [Hdom Hroot] Hla Hlw.
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
  intros [Hdom Hroot] Hla Hlw.
  split.
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

    eapply map_Forall_lookup_1 in Hp'; eauto ; cbn in Hp'.
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
Qed.

Lemma lmem_corresponds_get_word
  (phm : Mem) (lm : LMem) (vmap : VMap)
  (a : Addr) (v : Version) (lw : LWord) :
  mem_phys_log_corresponds phm lm vmap  ->
  is_cur_addr (a,v) vmap ->
  lm !! (a, v) = Some lw ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [Hdom Hroot] Hcur Hlm.
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
  intros [Hdom Hroot] Hlm Hcur.
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
  get_lcap lwsrc = Some (LSCap p b e a v) ->
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
  get_lcap lwsrc = Some (LSCap p b e a v) ->
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
  all: destruct Hmem_inv as [Hroot Hcur].
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
  get_lcap lwsrc = Some (LSCap p b e a v) ->
  lr !! src = Some lwsrc ->
  (Forall (λ a' : Addr, is_Some (lm !! (a', v))) (finz.seq_between b e)).
Proof.
  intros [ [_ ?] [? ?] ] Hget Hlsrc.
  eapply map_Forall_lookup_1 in Hlsrc; eauto; cbn in Hlsrc.
  eapply Forall_forall.
  intros a' Ha'.
  destruct_lword lwsrc ; cbn in * ; simplify_eq.
  all: eapply Hlsrc in Ha'.
  all: eapply map_Forall_lookup_1 in Ha'; eauto; cbn in Ha'.
  all: destruct Ha' as (? & ? & _).
  all: eexists ; eauto.
Qed.




(* TODO where do I put that ? *)
Definition is_last_version_laddr (lmem : LMem) (la : LAddr) : Prop :=
  let v := laddr_get_version la in
  map_Forall
    ( fun (la' : LAddr) (_ : LWord) =>
        (laddr_get_addr la' = laddr_get_addr la) -> laddr_get_version la' <=  v)
    lmem.

Lemma mem_corresponds_cur_addr_last_version_1
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm vmap →
  is_cur_addr la vmap ->
  is_last_version_laddr lm la.
Proof.
  move: la => [a v] [Hdom Hroot] Hcur_la.
  eapply map_Forall_lookup_2.
  move=> [a' v'] lw' Hla' /= ? ; simplify_eq.
  eapply map_Forall_lookup in Hla'; eauto.
  cbn in Hla'.
  destruct Hla' as (v_la' & Hcur_la' & Hcur_v_la' & Hla').
  by eapply is_cur_addr_same in Hcur_la'; [|eapply Hcur_la]; simplify_eq.
Qed.

Lemma mem_corresponds_cur_addr_last_version_2
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm vmap →
  is_Some (lm !! la) ->
  is_last_version_laddr lm la ->
  is_cur_addr la vmap.
Proof.
  move: la => [a v] [Hdom Hroot] [lw Hla] Hlast_la.
  eapply map_Forall_lookup_1 in Hdom ; eauto.
  destruct Hdom as (v_la & Hcur_v_la & Hcur_max & [lw0 Hla0]).
  cbn in *.
  eapply map_Forall_lookup_1 in Hla0 ; eauto.
  cbn in Hla0.
  specialize (Hla0 eq_refl).
  by assert (v = v_la) by lia ; simplify_eq.
Qed.

Lemma mem_corresponds_cur_addr_last_version
  (phm : Mem) (lm : LMem) (vmap : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm vmap →
  is_Some (lm !! la) ->
  (is_last_version_laddr lm la <-> is_cur_addr la vmap).
Proof.
  move=> HLinv Hla.
  by split ; intro
  ; [ eapply mem_corresponds_cur_addr_last_version_2
    | eapply mem_corresponds_cur_addr_last_version_1 ].
Qed.






(* TODO where to put that ? *)
Definition lword_of_argument (lregs: LReg) (a: Z + RegName): option LWord :=
  match a with
  | inl n => Some (LInt n)
  | inr r => lregs !! r
  end.

(* TODO vv -- conventions -- vv *)
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

(* describes whether the region pointed by a lword is not reachable *)
Definition lmem_not_access_wordL (lm : LMem) (vmap : VMap) (lw : LWord) : Prop :=
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      Forall (fun a => lmem_not_access_addrL lm vmap a) (finz.seq_between b e)
  | Some _ | None => True
  end.

(** Sweep in logical memory *)
Definition overlap_wordL (lw1 lw2 : LWord) : Prop :=
  (overlap_word (lword_get_word lw1) (lword_get_word lw2)).

Global Instance overlap_wordL_dec (lw1 lw2 : LWord) : Decision (overlap_wordL lw1 lw2).
Proof. solve_decision. Defined.

Lemma not_overlap_word_leaL
  (p1 p2 : Perm) (b1 b2 e1 e2 a1 a1' a2 a2' : Addr) (v1 v2 : Version)
  (lw1 lw1' lw2 lw2' : LWord) :
  get_lcap lw1 = Some (LSCap p1 b1 e1 a1 v1) ->
  get_lcap lw1' = Some (LSCap p1 b1 e1 a1' v1) ->
  get_lcap lw2 = Some (LSCap p2 b2 e2 a2 v2) ->
  get_lcap lw2' = Some (LSCap p2 b2 e2 a2' v2) ->
  ¬ overlap_wordL lw1 lw2 ->
  ¬ overlap_wordL lw1' lw2'.
Proof.
  move=> Hlw1 Hlw1' Hlw2 Hlw2' Hno_overlap Hoverlap.
  apply Hno_overlap.
  destruct_lword lw1 ; cbn in * ; simplify_eq.
  all: destruct_lword lw1'; cbn in * ; simplify_eq.
  all: destruct_lword lw2; cbn in * ; simplify_eq.
  all: destruct_lword lw2'; cbn in * ; simplify_eq.
  all: done.
Qed.

Lemma not_overlap_wordL_seq_between
  (p p' : Perm) (b b' e e' a a' : Addr) (v v' : Version) (lw lw' : LWord) :
  get_lcap lw = Some (LSCap p b e a v) ->
  get_lcap lw' = Some (LSCap p' b' e' a' v') ->
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


Definition unique_in_registersL (lregs : LReg) (src : RegName) (lwsrc : LWord) : Prop :=
  (map_Forall
     (λ (r : RegName) (lwr : LWord),
       if decide (r = src) then True else ¬ overlap_wordL lwsrc lwr)
     lregs).

Global Instance unique_in_registersL_dec (lregs : LReg) (src : RegName) (lwsrc : LWord)
  : Decision (unique_in_registersL lregs src lwsrc).
Proof.
  apply map_Forall_dec.
  move=> r rw.
  case_decide; solve_decision.
Defined.


(* Returns [true] if [r] is unique. *)
Definition unique_in_memoryL (lmem : LMem) (lwsrc : LWord) : Prop :=
  (map_Forall
     (λ (la : LAddr) (lwa : LWord),
       is_last_version_laddr lmem la -> ¬ overlap_wordL lwsrc lwa)
     lmem).

Global Instance unique_in_memoryL_dec (lmem : LMem) (lwsrc : LWord)
  : Decision (unique_in_memoryL lmem lwsrc).
Proof.
  apply map_Forall_dec.
  move=> la lwa.
  apply impl_dec; solve_decision.
Defined.

Definition unique_in_machineL (lmem : LMem) (lregs : LReg) (src : RegName) (lwsrc : LWord) :=
  lregs !! src = Some lwsrc ->
  unique_in_registersL lregs src lwsrc /\ unique_in_memoryL lmem lwsrc.

(* Alternative definition of unique_in_machineL,
   using the vmap *)
Definition unique_in_memoryL_aux (lmem : LMem) (vmap : VMap) (lwsrc : LWord) : Prop :=
  (map_Forall
     (λ (la : LAddr) (lwa : LWord),
       is_cur_addr la vmap -> ¬ overlap_wordL lwsrc lwa)
     lmem).

Lemma unique_in_memoryL_equiv
  (phm : Mem) (phr : Reg) (lm : LMem) (lr : LReg) (vmap : VMap)
  (src : RegName) (lwsrc : LWord) :
  state_phys_log_corresponds phr phm lr lm vmap →
  lr !! src = Some lwsrc →
  unique_in_memory phm (lword_get_word lwsrc) ->
  unique_in_memoryL lm lwsrc ->
  unique_in_memoryL_aux lm vmap lwsrc.
Proof.
  move=> [_ Hmem_inv] Hsrc Hsweep HsweepL.
  rewrite /unique_in_memoryL_aux.
  rewrite /unique_in_memory in Hsweep.
  rewrite /unique_in_memoryL in HsweepL.
  eapply map_Forall_impl; first eapply HsweepL.
  move=> la lw /= His_last Hcur_la.
  apply: His_last.
  eapply mem_corresponds_cur_addr_last_version_1; eauto.
Qed.

Lemma unique_in_machineL_insert_reg
  (lm : LMem) (lr : LReg) (src r: RegName) (lwsrc lwr : LWord) :
  r <> src ->
  lr !! src = Some lwsrc ->
  ¬ overlap_wordL lwsrc lwr ->
  unique_in_machineL lm lr src lwsrc ->
  unique_in_machineL lm (<[r := lwr ]> lr) src lwsrc.
Proof.
  move=> Hr_neq_src Hlr_src Hlr_r Hunique.
  specialize (Hunique Hlr_src).
  move: Hunique => [Hunique_reg Hunique_src] _.
  split; last done.
  apply map_Forall_insert_2; last done.
  case_decide; auto.
Qed.

Lemma unique_in_machineL_not_overlap_word
  (lm : LMem) (lr : LReg) (src r : RegName) (lwsrc lwr : LWord) :
  r ≠ src ->
  lr !! src = Some lwsrc ->
  lr !! r = Some lwr ->
  unique_in_machineL lm lr src lwsrc ->
  ¬ overlap_wordL lwsrc lwr.
Proof.
  move=> Hr_neq_src Hlr_src Hlr_r Hunique.
  specialize (Hunique Hlr_src).
  move: Hunique => [Hunique_reg _].
  eapply map_Forall_lookup_1 in Hunique_reg; eauto.
  by case_decide; simplify_eq.
Qed.

Lemma phys_log_corresponds_unique_in_registers
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord):
  state_phys_log_corresponds phr phm lr lm vmap ->
  lr !! src = Some lwsrc ->
  unique_in_registers phr src (lword_get_word lwsrc) ->
  unique_in_registersL lr src lwsrc.
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

Lemma phys_log_corresponds_unique_in_memory
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (vmap : VMap)
  (src : RegName) (lwsrc : LWord):
  state_phys_log_corresponds phr phm lr lm vmap ->
  lr !! src = Some lwsrc ->
  unique_in_memory phm (lword_get_word lwsrc) ->
  unique_in_memoryL lm lwsrc.
Proof.
  move=> [Hreg_inv Hmem_inv] Hlr_src Hunique.
  eapply map_Forall_lookup_2.
  move=> [a v] lw_la Hlm_la His_cur_la.
  eapply mem_corresponds_cur_addr_last_version_2 in His_cur_la; eauto.
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
  sweep phm phr src = true →
  unique_in_machineL lm lr src lwsrc.
Proof.
  intros HLinv Hlr_src Hsweep.
  assert (Hphr_src : phr !! src = Some (lword_get_word lwsrc))
    by (by eapply state_corresponds_reg_get_word).
  apply sweep_spec with (wsrc := (lword_get_word lwsrc)) in Hsweep ; auto.
  specialize (Hsweep Hphr_src).
  destruct Hsweep as [Hunique_reg Hunique_mem].
  intros _.
  split ;
    [ eapply phys_log_corresponds_unique_in_registers
    | eapply phys_log_corresponds_unique_in_memory ]
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
  get_lcap lw = Some (LSCap p b e a v) ->
  lr !! src = Some lw ->
  is_cur_word lw vmap ->
  unique_in_machineL lm lr src lw ->
  Forall (λ a' : Addr, lmem_not_access_addrL lm vmap a') (finz.seq_between b e).
Proof.
  move=> Hmem_inv Hlw Hlr_src His_cur Hunique.
  apply Forall_forall; move=> a' Ha'.
  destruct_lword lw ; cbn in Hlw ; simplify_eq.
  all: pose proof (is_cur_lword_lea vmap p b e a a' v His_cur) as His_cur'.
  all: assert (Hcur_a': is_cur_addr (a',v) vmap).
  { eapply cur_lword_cur_addr; [|eauto|].
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










(** Machinery to update the current version in a lmemory *)
(* By convention:
   - `lm` is the global lmemory
   - `vmap_m` is the view map corresponding to the global lmemory `lm`
   - `lmem` is the local lmemory
   - `vmap_mem` is the view map corresponding to the local lmemory `lmem`
 *)


(** Machinery to update locally *)
(* Update the version of the current address,
   both in the the lmemory and in the view map.
   If the address is not in the view map,
   or if the lmemory doesn't contain the current address,
   then the lmemory and view map are not updated. *)
Definition update_cur_version_addr_local
  (lmem : LMem) (vmap : VMap) (a : Addr) : (LMem * VMap) :=
  match vmap !! a with
  | Some v =>
      match lmem !! (a,v) with
      | Some lw => (<[ (a, v+1) := lw ]> lmem, <[ a := v+1 ]> vmap)
      | None => (lmem, vmap)
      end
  | None => (lmem, vmap)
  end.

Definition update_cur_version_region_local
  (lmem : LMem) (vmap : VMap) (la : list Addr) : (LMem * VMap) :=
  foldr
    ( fun a (upd : LMem * VMap) =>
        let (lmem', vmap') := upd in update_cur_version_addr_local lmem' vmap' a)
    (lmem, vmap)
    la.

(* update the version number of the region pointed by a lword *)
Definition update_cur_version_word_region_local
  (lmem : LMem) (vmap : VMap) (lw : LWord) : (LMem * VMap) :=
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      update_cur_version_region_local lmem vmap (finz.seq_between b e)
  | Some _ | None => (lmem, vmap)
  end.


(* TODO vv -- Convention -- vv *)
Lemma update_cur_version_region_local_cons
  (lmem lmem' : LMem) (vmap vmap' : VMap) (a : Addr) (la : list Addr) :
  update_cur_version_region_local lmem vmap (a :: la) = (lmem', vmap') ->
  exists (lmem0 : LMem) (vmap0 : VMap),
    update_cur_version_region_local lmem vmap la = (lmem0, vmap0)
    ∧ update_cur_version_addr_local lmem0 vmap0 a = (lmem', vmap').
Proof.
  intros Hupd.
  cbn in Hupd ; rewrite -/(update_cur_version_region_local lmem vmap la) in Hupd.
  destruct (update_cur_version_region_local lmem vmap la) as [lmem0 vmap0] eqn:Hupd0.
  exists lmem0, vmap0.
  split ; eauto.
Qed.


(* TODO find better lemma name *)
(* If an address `a'` is not reachable from the current view of the lmem,
   then updating the version number of another address `a`
   does not make it reachable *)
Lemma update_cur_version_addr_local_preserves_no_access
  (lmem lmem' : LMem) (vmap vmap' : VMap) (a a' : Addr):
  a ≠ a' →
  update_cur_version_addr_local lmem vmap a' = (lmem', vmap') →
  lmem_not_access_addrL lmem vmap a →
  lmem_not_access_addrL lmem' vmap' a.
Proof.
  intros Hneq Hupd Hno_access.
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a') as [va'|] eqn:Heqn ; cbn in Hupd ; [|by simplify_eq].
  destruct (lmem !! (a', va')) as [lw'|] eqn:Heqn'; simplify_map_eq; last done.
  apply map_Forall_lookup.
  intros la lw Hsome Hcur.
  destruct la as [a0 v0].
  destruct (decide (a0 = a')) ; simplify_eq.
  - assert (v0 = (va' + 1)) by (rewrite /is_cur_addr in Hcur; by simplify_map_eq).
    simplify_map_eq.
    apply (map_Forall_lookup_1 _ _ _ _ Hno_access) in Heqn'; auto.
  - assert ((a', va' + 1) ≠ (a0, v0)) by (intro ; simplify_eq).
    simplify_map_eq.
    apply (map_Forall_lookup_1 _ _ _ _ Hno_access) in Hsome; auto.
    rewrite /is_cur_addr /= in Hcur; simplify_map_eq.
    auto.
Qed.

(* Same as `update_cur_version_addr_preserves_no_access`, but for a list of addresses *)
Lemma update_cur_version_region_local_preserves_no_access
  (lmem lmem': LMem) (vmap vmap' : VMap) (la : list Addr) (a' : Addr):
  a' ∉ la →
  update_cur_version_region_local lmem vmap la = (lmem', vmap') →
  lmem_not_access_addrL lmem vmap a' →
  lmem_not_access_addrL lmem' vmap' a'.
Proof.
  move: lmem lmem' vmap vmap' a'.
  induction la as [| a la IH]; intros * Hnot_in Hupd Hno_access.
  - by cbn in * ; simplify_eq.
  - apply not_elem_of_cons in Hnot_in; destruct Hnot_in as [Hneq Hnot_in].
    apply update_cur_version_region_local_cons in Hupd
    ; destruct Hupd as (lm0 & vmap0 & Hupd & Hupd_rec).
    eapply update_cur_version_addr_local_preserves_no_access ; eauto.
Qed.


(* If the address `a` is not reachable
   from the current view of the lmem,
   then the mem_phys_log invariant still holds
   after updating its version number. *)
Lemma update_cur_version_addr_local_preserves_mem_phyc_cor
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (a : Addr) :
  update_cur_version_addr_local lm vmap a = (lm', vmap') →
  lmem_not_access_addrL lm vmap a →
  mem_phys_log_corresponds phm lm vmap ->
  mem_phys_log_corresponds phm lm' vmap'.
Proof.
  intros Hupd Hnaccess_mem [Hdom Hroot].
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a) as [v |] eqn:Hcur_la; cbn in * ; simplify_eq; last done.
  destruct (lm !! (a,v)) as [lw |] eqn:Hla; cbn in * ; simplify_eq; last done.
  rewrite -/(is_cur_addr (a,v) vmap) in Hcur_la.
  assert (not (word_access_addrL a lw)) as Hnaccess by eauto.
  pose proof (Hla' := Hla).
  eapply map_Forall_lookup_1 in Hla'; eauto; cbn in Hla'.
  destruct Hla' as (va & Hcur_va & Hle_va & [lwa Hlwa]).
  rewrite /is_cur_addr /= in Hcur_la, Hcur_va.
  rewrite Hcur_la in Hcur_va ; simplify_eq.
  split.
  - eapply lmem_corresponds_read_iscur in Hla ; eauto.
    2: split ; eauto.
    eapply update_cur_word with (v := va+1) in Hla;eauto.
    apply map_Forall_insert_2.
    { eexists (va+1).
      split.
      rewrite /is_cur_addr //= ; by simplify_map_eq.
      split; by simplify_map_eq.
    }
    eapply map_Forall_lookup; eauto.
    intros la' lw' Hroot' ; cbn in Hroot'.
    destruct la' as [a' v'] ; cbn in *.
    eapply map_Forall_lookup_1 in Hroot' ; eauto ; cbn in Hroot'.
    destruct Hroot' as (cur_v & Hcur_v & Hcur_max & [cur_lw Hcur_lw]).
    destruct (decide (a = a')); simplify_eq.
    + exists (va+1). split ; [|split] ; try by simplify_map_eq.
      rewrite /is_cur_addr; by simplify_map_eq.
      replace va with cur_v
        by ( by rewrite /is_cur_addr /= Hcur_la in Hcur_v; simplify_eq).
      lia.
    + exists cur_v. split; [|split]; eauto.
      apply is_cur_addr_insert_ne; eauto.
      exists cur_lw. rewrite lookup_insert_ne //=; congruence.
  - apply map_Forall_insert_2.
    { pose proof (Hla' := Hla).
      eapply map_Forall_lookup_1 in Hla; eauto ; cbn in *.
      destruct Hla as (cur_v & Hcur_v & Hcur_max & [cur_lw Hcur_lw]).
      rewrite /is_cur_addr /= Hcur_la in Hcur_v; simplify_map_eq.
      exists lw. split. by simplify_map_eq.
      eapply map_Forall_lookup_1 in Hcur_la ; eauto ; cbn in Hcur_la.
      destruct Hcur_la as (lw' & Hlw' & Hw' & Hcur_lw').
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
      rewrite Hcur_la in Hcur_a' ; simplify_eq.
      rewrite Hlwa in Hla ; simplify_eq.
      by simplify_map_eq.
    + exists lw'.
      assert ((a, va + 1) ≠ (a', v')) by (intro ; simplify_eq).
      split ; [|split] ; try by simplify_map_eq.
      eapply update_cur_word;eauto.
Qed.

(* Same as `update_cur_version_addr_preserves_mem_phyc_cor`,
   but for a list of addresses *)
Lemma update_cur_version_region_local_preserves_mem_phyc_cor
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (la : list Addr):
  NoDup la →
  update_cur_version_region_local lm vmap la = (lm', vmap') →
  Forall (fun a => lmem_not_access_addrL lm vmap a) la →
  mem_phys_log_corresponds phm lm vmap ->
  mem_phys_log_corresponds phm lm' vmap'.
Proof.
  move: phm lm lm' vmap vmap'.
  induction la as [| a la IH]; intros * Hno_dup Hupd Hall_naccess_mem Hmem_corr.
  - by cbn in * ; simplify_eq.
  - apply update_cur_version_region_local_cons in Hupd
    ; destruct Hupd as (lm0 & vmap0 & Hupd & Hupd0).
    apply Forall_cons in Hall_naccess_mem as [Hnacces_mem Hall_naccess_mem].
    apply NoDup_cons in Hno_dup ; destruct Hno_dup as [Hnotin Hno_dup].
    assert (mem_phys_log_corresponds phm lm0 vmap0) as Hinv0.
    by (eapply IH ;eauto).
    eapply update_cur_version_addr_local_preserves_mem_phyc_cor in Hupd0 ; eauto.
    by eapply update_cur_version_region_local_preserves_no_access.
Qed.

(* update the version number of a memory region that is not reacheable,
   preserves the mem_phys_log invariant *)
Lemma update_cur_version_word_region_local_preserves_mem_phyc_cor
  (phm : Mem) (lm lm': LMem) (vmap vmap' : VMap) (lw : LWord) :
  lmem_not_access_wordL lm vmap lw →
  update_cur_version_word_region_local lm vmap lw = (lm', vmap') →
  mem_phys_log_corresponds phm lm vmap ->
  mem_phys_log_corresponds phm lm' vmap'.
Proof.
  intros Hno_access Hupd Hmem_phys_log.
  rewrite /update_cur_version_word_region_local in Hupd.
  rewrite /lmem_not_access_wordL in Hno_access.
  destruct (get_lcap lw) as [[] |] ; simplify_eq ; auto.
  eapply update_cur_version_region_local_preserves_mem_phyc_cor ; eauto.
  apply finz_seq_between_NoDup.
Qed.

Lemma update_cur_version_addr_local_preserves_content_lmem
  (lmem lmem' : LMem) (vmap vmap' : VMap)
  (a a': Addr) (v :Version):
  a ≠ a' ->
  update_cur_version_addr_local lmem vmap a' = (lmem', vmap') ->
  lmem !! (a, v) = lmem' !! (a, v).
Proof.
  intros Ha_notint_la Hupd.
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
  destruct (lmem !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
  simplify_eq.
  by rewrite lookup_insert_ne ; last (intro ; simplify_pair_eq).
Qed.

Lemma update_cur_version_region_local_preserves_content_lmem
  (lmem lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v :Version):
  a ∉ la ->
  update_cur_version_region_local lmem vmap la = (lmem', vmap') ->
  lmem !! (a, v) = lmem' !! (a, v).
Proof.
  move: lmem lmem' vmap vmap' a v.
  induction la as [| a' la Hla]
  ; intros * Ha_notin_la Hupd
  ; first (by cbn in *; simplify_eq).
  apply not_elem_of_cons in Ha_notin_la. destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].
  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lmem0 & vmap0 & Hupd & Hupd0).
  rewrite -(update_cur_version_addr_local_preserves_content_lmem lmem0 lmem' vmap0 vmap' a a' v)
  ; eauto.
Qed.

Lemma update_cur_version_addr_local_notin_preserves_cur
  (lm lm' : LMem) (vmap vmap' : VMap) (a a' : Addr):
  update_cur_version_addr_local lm vmap a' = (lm', vmap')
  → a ≠ a'
  → vmap !! a = vmap' !! a.
Proof.
  move=> Hupd Hneq.
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a') as [va'|]; cbn in *; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; by simplify_eq.
Qed.

Lemma update_cur_version_region_local_notin_preserves_cur
  (lm lm' : LMem) (vmap vmap' : VMap) (la : list Addr) (a' : Addr) :
  update_cur_version_region_local lm vmap la = (lm', vmap')
  → a' ∉ la
  → vmap !! a' = vmap' !! a'.
Proof.
  move: lm lm' vmap vmap' a'.
  induction la as [|a la IH]
  ; intros * ; move=> Hupd Ha_notin_la
  ; first (cbn in *; by simplify_eq).
  apply not_elem_of_cons in Ha_notin_la.
  destruct Ha_notin_la as [Ha0_neq_a Ha_notin_la].
  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
  rewrite -(update_cur_version_addr_local_notin_preserves_cur lm0 lm' vmap_m0 vmap' a' a)
  ; eauto.
Qed.

Lemma update_cur_version_region_local_in_updates_cur_map
  (lm lm' : LMem) (vmap vmap' : VMap)
  (la : list Addr) ( a : Addr) (v : Version):
  NoDup la ->
  update_cur_version_region_local lm vmap la = (lm', vmap') ->
  a ∈ la ->
  is_Some (lm !! (a,v)) ->
  is_cur_addr (a, v) vmap ->
  is_cur_addr (a, v+1) vmap'.
Proof.
  move: lm lm' vmap vmap' a v.
  induction la as [|a' la' IH] ; intros * HNoDup Hupd Ha [lwa Hlwa] Hcur_a.
  - by apply elem_of_nil in Ha.
  - apply NoDup_cons in HNoDup.
    destruct HNoDup as [ Ha'_not_in_la' HNoDup ].
    apply elem_of_cons in Ha.
    apply update_cur_version_region_local_cons in Hupd.
    destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
    destruct Ha as [? | Ha] ; simplify_eq.
    + (* case (a = a' *)
      erewrite update_cur_version_region_local_preserves_content_lmem in Hlwa; eauto.
      eapply update_cur_version_region_local_notin_preserves_cur in Hupd; eauto.
      rewrite /update_cur_version_addr_local -Hupd Hcur_a /= Hlwa in Hupd0.
      by rewrite /is_cur_addr //= ; simplify_map_eq.
    + (* case (a <> a' *)
      assert (a <> a') as Ha_neq_a' by set_solver.
      rewrite /is_cur_addr /=.
      rewrite -(update_cur_version_addr_local_notin_preserves_cur lm0 lm' vmap_m0 vmap' a a')
      ; eauto.
      eapply IH; eauto.
Qed.

Lemma update_cur_version_local_notin_is_cur_word
  (lm lm' : LMem) (vmap vmap' : VMap)
  (p : Perm) (b e a : Addr) (v : Version)
  (lw lwsrc : LWord) :
  get_lcap lwsrc = Some (LSCap p b e a v) ->
  update_cur_version_region_local lm vmap (finz.seq_between b e) = (lm', vmap') ->
  ¬ overlap_wordL lwsrc lw ->
  is_cur_word lw vmap ->
  is_cur_word lw vmap'.
Proof.
  move=> Hget Hupd Hno_overlap His_cur_lw.
  destruct lw ; cbn; first done.
  - destruct sb as [ p' b' e' a' v'|] ; last done.
    move=> a'0 Ha'0.
    cbn in His_cur_lw.
    pose proof (His_cur_lw a'0 Ha'0) as Ha'0_cur.
    erewrite update_cur_version_region_local_notin_preserves_cur
      with (a' := a'0) in Ha'0_cur; eauto.
    eapply not_overlap_wordL_seq_between; [ | | eapply Hno_overlap| eapply Ha'0]; eauto.
  - destruct l as [ p' b' e' a' v'|] ; last done.
    move=> a'0 Ha'0.
    cbn in His_cur_lw.
    pose proof (His_cur_lw a'0 Ha'0) as Ha'0_cur.
    erewrite update_cur_version_region_local_notin_preserves_cur
      with (a' := a'0) in Ha'0_cur; eauto.
    eapply not_overlap_wordL_seq_between; [ | | eapply Hno_overlap| eapply Ha'0]; eauto.
Qed.


Lemma update_cur_version_word_region_local_update_lword
  (lm lm' : LMem) (vmap vmap' : VMap) (lw : LWord) :
  update_cur_version_word_region_local lm vmap lw = (lm', vmap') ->
  (* TODO ugly *)
  ( match lw with
    | LCap _ b e a v
    | LSealedCap _ _ b e a v =>
        Forall (fun a => is_Some (lm !! (a,v)) ) (finz.seq_between b e)
    | _ => True
    end ) ->
  is_cur_word lw vmap ->
  is_cur_word (next_version_lword lw) vmap'.
Proof.
  move=> Hupd Hsome Hcur.
  destruct_lword lw ; try done; cbn in *.
  all: move=> a' Ha'.
  all: specialize (Hcur _ Ha').
  all: eapply update_cur_version_region_local_in_updates_cur_map
  ; eauto; try apply finz_seq_between_NoDup.
  all: rewrite elem_of_list_lookup in Ha'
  ; destruct Ha' as [? Ha']; eapply Forall_lookup in Hsome
  ; eauto.
Qed.

Lemma update_cur_version_region_local_update_lword
  (lm lm' : LMem) (vmap vmap' : VMap)
  (p : Perm) (b e a : Addr) (v : Version) (lw : LWord) :
  get_lcap lw = Some (LSCap p b e a v) ->
  update_cur_version_region_local lm vmap (finz.seq_between b e) = (lm', vmap') ->
  Forall (fun a => is_Some (lm !! (a,v))) (finz.seq_between b e) ->
  is_cur_word lw vmap ->
  is_cur_word (next_version_lword lw) vmap'.
Proof.
  move=> Hget Hupd Hsome Hcur.
  destruct_lword lw ; cbn in Hget ; simplify_eq.
  all: eapply update_cur_version_word_region_local_update_lword; cbn ; eauto.
Qed.

Lemma update_cur_version_reg_phys_log_cor_updates_src
  (phr : Reg) (phm : Mem) (lr : LReg) (lm lm' : LMem) (vmap vmap' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) (lw lwsrc: LWord) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  get_lcap lwsrc = Some (LSCap p b e a v) ->
  is_cur_word lw vmap' ->
  lr !! src = Some lwsrc ->
  unique_in_machineL lm lr src lwsrc ->
  update_cur_version_region_local lm vmap (finz.seq_between b e) = (lm', vmap') ->
  reg_phys_log_corresponds
    (<[src:= (lword_get_word lw)]> phr)
    (<[src:= lw]> lr) vmap'.
Proof.
  move=>  [Hreg_inv Hmem_inv] Hget Hcur_lw Hlr_src Hunique Hupd.
  split.
  - rewrite /lreg_strip fmap_insert /= -/(lreg_strip lr).
    by replace phr with (lreg_strip lr) by (by destruct Hreg_inv as [? _]).
  - rewrite -insert_delete_insert.
    eapply lreg_corresponds_insert_respects with (phr := (delete src phr)).
    2: { by cbn. }
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
      eapply update_cur_version_local_notin_is_cur_word ; eauto.
Qed.

Lemma update_cur_version_reg_phys_log_cor_updates_notin
  (phr : Reg) (phm : Mem) (lr : LReg) (lm lm' : LMem) (vmap vmap' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) :
  state_phys_log_corresponds phr phm lr lm vmap ->
  lr !! src = Some (LCap p b e a v) ->
  update_cur_version_region_local lm vmap (finz.seq_between b e) = (lm', vmap') ->
  unique_in_machineL lm lr src (LCap p b e a v) ->
  src ∉ dom phr ->
  src ∉ dom lr ->
  reg_phys_log_corresponds phr lr vmap'.
Proof.
  move=> HLinv Hlr_src Hupd Hunique Hsrc_notin_phr Hsrc_notin_lr.
  pose proof HLinv as [[Hreg_strip Hreg_current] [Hroot Hdom]].
  split; first done.
  apply map_Forall_lookup ; move=> r lwr Hlr_lwr.
  assert (Hr_neq_src : r ≠ src).
  { apply not_elem_of_dom in Hsrc_notin_lr; congruence. }
  eapply map_Forall_lookup_1 in Hreg_current ; eauto.
  specialize (Hunique Hlr_src).
  destruct Hunique as [Hunique_reg Hunique_mem].
  eapply map_Forall_lookup_1 in Hunique_reg ; eauto.
  case_decide as H; simplify_eq; clear H.
  eapply update_cur_version_local_notin_is_cur_word; eauto.
  by cbn.
Qed.

Lemma update_cur_version_addr_local_notin_preserves_lmem_inv
  (lmem lmem' : LMem) (vmap vmap' : VMap)
  (a a' : Addr) (v : Version) :
  a' ≠ a ->
  update_cur_version_addr_local lmem vmap a' = (lmem', vmap') ->
  lmem' !! (a,v) = lmem !! (a,v).
Proof.
  intros Hneq Hupd.
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a') as [v'|] eqn:Hv' ; cbn in * ; simplify_map_eq ; last done.
  destruct (lmem !! (a', v')) eqn:? ; cbn in * ; simplify_map_eq
  ; last done.
  rewrite lookup_insert_ne /=; eauto; intro ; simplify_eq.
Qed.

Lemma update_cur_version_region_local_notin_preserves_lmem_inv
  (lmem lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v : Version) :
  a ∉ la ->
  update_cur_version_region_local lmem vmap la = (lmem', vmap') ->
  lmem' !! (a,v) = lmem !! (a,v).
Proof.
  move: lmem lmem' vmap vmap' a v.
  induction la as [|a' la IHla]; intros * Ha_notin_la Hupd
  ; first (by cbn in * ; simplify_map_eq).
  apply not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].
  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
  erewrite update_cur_version_addr_local_notin_preserves_lmem_inv
    with (lmem := lmem0) (lmem' := lmem')
  ; eauto.
Qed.





(** Machinery to update globally *)

(* We assume that *lmem* is a local view compatible with the global view *lm*.
   We also assume that *lm* contains the laddress *(a,v)*,
   whereas *lmem* might not contain it.

   This way, the local view *lmem* can be updated,
   even if it does not contain the address (a,v)
 *)
Definition update_cur_version_addr_global (lmem lm : LMem) (vmap : VMap) (a : Addr)
  : LMem * VMap :=
  match vmap !! a with
  | Some v =>
      match lm !! (a,v) with
      | Some lw => (<[ (a, v+1) := lw ]> lmem, <[ a := v+1 ]> vmap)
      | None => (lmem, vmap)
      end
  | None => (lmem, vmap)
  end.

Definition update_cur_version_region_global
  (lmem lm : LMem) (vmap : VMap) (la : list Addr) : LMem * VMap :=
  foldr
    ( fun a (upd : LMem * VMap) =>
        let (lmem', vmap') := upd in
        update_cur_version_addr_global lmem' lm vmap' a)
    (lmem, vmap)
    la.

(* update the version number of the region pointed by a lword *)
Definition update_cur_version_word_region_global
  (lmem lm : LMem) (vmap : VMap) (lw : LWord) : LMem * VMap :=
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      update_cur_version_region_global lmem lm vmap (finz.seq_between b e)
  | Some _ | None => (lm, vmap)
  end.

Lemma update_cur_version_region_global_cons
  (lmem lm lmem' : LMem) (vmap vmap' : VMap) (a : Addr) (la : list Addr) :
  update_cur_version_region_global lmem lm vmap (a :: la) = (lmem', vmap') ->
  exists (lmem0 : LMem) (vmap0 : VMap),
    update_cur_version_region_global lmem lm vmap la = (lmem0, vmap0)
    ∧ update_cur_version_addr_global lmem0 lm vmap0 a = (lmem', vmap').
Proof.
  intros Hupd.
  cbn in Hupd.
  rewrite -/(update_cur_version_region_global lmem lm vmap la) in Hupd.
  destruct (update_cur_version_region_global lmem lm vmap la)
    as [lmem0 vmap0] eqn:Hupd0.
  exists lmem0, vmap0.
  split ; eauto.
Qed.

Lemma update_cur_version_addr_global_notin_preserves_cur_1:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) (opt_v : option Version),
  update_cur_version_addr_global lmem lm cur_map a' = (lmem', cur_map')
  → a ≠ a'
  → cur_map !! a = opt_v
  → cur_map' !! a = opt_v.
Proof.
  move=> lmem lm lmem' cur_map cur_map' a a' opt_v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (cur_map !! a') as [va'|]; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; by simplify_eq.
Qed.

Lemma update_cur_version_addr_global_notin_preserves_cur_2:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) (opt_v : option Version),
  update_cur_version_addr_global lmem lm cur_map a' = (lmem', cur_map')
  → a ≠ a'
  → cur_map' !! a = opt_v
  → cur_map !! a = opt_v.
Proof.
  move=> lmem lm lmem' cur_map cur_map' a a' opt_v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (cur_map !! a') as [va'|]; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; by simplify_eq.
Qed.

Lemma update_cur_version_region_global_notin_preserves_cur_1:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap)
    (la : list Addr) (a : Addr) (opt_v : option Version),
    update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map')
    → a ∉ la
    → cur_map !! a = opt_v
    → cur_map' !! a = opt_v.
Proof.
  move=> lmem lm lmem' cur_map cur_map' la.
  move: lmem lm lmem' cur_map cur_map'.
  induction la as [|a la IH]
  ; intros * ; move=> Hupd Ha_notin_la Hcur
                     ; first (cbn in *; by simplify_eq).

  apply not_elem_of_cons in Ha_notin_la.
  destruct Ha_notin_la as [Ha0_neq_a Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
  assert (vmap_m0 !! a0 = opt_v) as Hcur0 by (eapply IH ; eauto).
  eapply update_cur_version_addr_global_notin_preserves_cur_1 in Hcur0; eauto.
Qed.

Lemma update_cur_version_region_global_notin_preserves_cur_2:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap)
    (la : list Addr) (a : Addr) (opt_v : option Version),
    update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map')
    → a ∉ la
    → cur_map' !! a = opt_v
    → cur_map !! a = opt_v.
Proof.
  move=> lmem lm lmem' cur_map cur_map' la.
  move: lmem lm lmem' cur_map cur_map'.
  induction la as [|a la IH]
  ; intros * ; move=> Hupd Ha_notin_la Hcur
  ; first (cbn in *; by simplify_eq).

  apply not_elem_of_cons in Ha_notin_la.
  destruct Ha_notin_la as [Ha0_neq_a Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
  eapply IH; eauto.
  eapply update_cur_version_addr_global_notin_preserves_cur_2; eauto.
Qed.


Lemma update_cur_version_addr_global_notin_preserves_lmem
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (a a': Addr) (v :Version) (opt_lw : option LWord):
  a ≠ a' ->
  update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  intros Hneq Hupd Hlmem.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
  destruct (lm !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
  simplify_eq.
  rewrite lookup_insert_ne //=; intro ; simplify_eq; lia.
Qed.

(* TODO duplicate of update_cur_version_region_local_preserves_content_lmem *)
Lemma update_cur_version_region_global_notin_preserves_lmem
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v :Version) (opt_lw : option LWord):
  a ∉ la ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  move: lmem lm lmem' vmap vmap' a v opt_lw.
  induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hlmem
  ; first (by cbn in * ; simplify_map_eq).

  rewrite not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).

  eapply update_cur_version_addr_global_notin_preserves_lmem
    in Hupd0; eauto.
Qed.

Lemma update_cur_version_addr_global_preserves_content_lmem
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (a a': Addr) (v :Version) (opt_lw : option LWord):
  update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
  vmap !! a = Some v ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  intros Hupd Hcur Hlmem.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
  destruct (lm !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
  simplify_eq.
  destruct (decide (a = a')) ; simplify_eq
  ; [rewrite Hva' in Hcur; simplify_eq|]
  ; rewrite lookup_insert_ne //=; intro ; simplify_eq; lia.
Qed.

Lemma update_cur_version_region_global_preserves_content_lmem
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v :Version) (opt_lw : option LWord):
  a ∉ la ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
  vmap !! a = Some v ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  move: lmem lm lmem' vmap vmap' a v opt_lw.
  induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hcur Hlmem
  ; first (by cbn in * ; simplify_map_eq).

  rewrite not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).

  eapply update_cur_version_addr_global_preserves_content_lmem
    in Hupd0; eauto.
  eapply update_cur_version_region_global_notin_preserves_cur_1; eauto.
Qed.

Lemma update_cur_version_addr_global_incl_lmem
  (lmem lm lmem': LMem) (vmap vmap' : VMap) (a : Addr) (v : Version) :
  vmap !! a = Some v ->
  lmem !! (a, v+1) = None ->
  update_cur_version_addr_global lmem lm vmap a = (lmem', vmap') ->
  lmem ⊆ lmem'.
Proof.
  intros Hcur Hmaxv Hupd.
  rewrite /update_cur_version_addr_global in Hupd.
  rewrite Hcur in Hupd.
  destruct (lm !! (a,v)) as [lwa|] eqn:Hlwa ; simplify_map_eq; last set_solver.
  eapply insert_subseteq_r; eauto.
Qed.


Lemma update_cur_version_addr_global_notin_preserves_lmem_inv
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (a a' : Addr) (v : Version) (lw : LWord) :
  a' ≠ a ->
  update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
  lmem' !! (a,v) = Some lw ->
  lmem !! (a,v) = Some lw.
Proof.
  intros Hneq Hupd Hlw.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (vmap !! a') as [v'|] eqn:? ; cbn in * ; simplify_map_eq ; last done.
  destruct (lm !! (a', v')) eqn:? ; cbn in * ; simplify_map_eq
  ; last done.
  rewrite lookup_insert_ne /= in Hlw; eauto; intro ; simplify_eq.
Qed.

Lemma update_cur_version_region_global_notin_preserves_lmem_inv
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v : Version) (lw : LWord) :
  a ∉ la ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
  lmem' !! (a,v) = Some lw ->
  lmem !! (a,v) = Some lw.
Proof.
  move: lmem lm lmem' vmap vmap' a v lw.
  induction la as [|a' la IHla]; intros * Ha_notin_la Hupd Hlw
  ; first (by cbn in * ; simplify_map_eq).

  apply not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
  eapply IHla; eauto.
  eapply update_cur_version_addr_global_notin_preserves_lmem_inv; eauto.
Qed.

Lemma update_cur_version_addr_global_notin_preserves_lm_inv
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (a a' : Addr) (v : Version) (lw : LWord) :
  a' ≠ a ->
  lmem ⊆ lm ->
  update_cur_version_addr_global lmem lm vmap a' = (lmem', vmap') ->
  lmem' !! (a,v) = Some lw ->
  lm !! (a,v) = Some lw.
Proof.
  intros Hneq Hlmem_incl Hupd Hlw.
  rewrite /update_cur_version_addr_global in Hupd.
  destruct (vmap !! a') as [v'|] eqn:? ; cbn in * ; simplify_map_eq
  ; last (eapply lookup_weaken ; eauto).
  destruct (lm !! (a', v')) eqn:? ; cbn in * ; simplify_map_eq
  ; last (eapply lookup_weaken ; eauto).
  rewrite lookup_insert_ne /= in Hlw; eauto; [|intro ; simplify_eq].
  eapply lookup_weaken ; eauto.
Qed.

Lemma update_cur_version_region_global_notin_preserves_lm_inv
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (la : list Addr) (a : Addr) (v : Version) (lw : LWord) :
  a ∉ la ->
  lmem ⊆ lm ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
  lmem' !! (a,v) = Some lw ->
  lm !! (a,v) = Some lw.
Proof.
  move: lmem lm lmem' vmap vmap' a v lw.
  induction la as [|a' la IHla]; intros * Ha_notin_la Hlmem_incl Hupd Hlw
  ; first (by cbn in * ; simplify_map_eq; eapply lookup_weaken ; eauto).

  apply not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).
  eapply IHla; eauto.
  eapply update_cur_version_addr_global_notin_preserves_lmem_inv; eauto.
Qed.

(** Machinery to link the local and global update *)

(* TODO find name and refactor proof... *)
Lemma inter_region_aaa
  (lmem lm lmem' lm' : LMem)
  (vmap_mem vmap_m vmap_mem' vmap_m' : VMap)
  (la : list Addr) (a' : Addr) (v va : Version)
  (lw : LWord) :
  NoDup la ->
  a' ∈ la ->
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
  Forall (λ a0 : Addr, vmap_m !! a0 = Some v) la ->
  Forall (λ a0 : Addr, lm !! (a0, v + 1) = None) la ->
  update_cur_version_region_global lmem lm vmap_mem la = (lmem', vmap_mem') ->
  update_cur_version_region_local lm vmap_m la = (lm', vmap_m') ->
  lmem' !! (a', va) = Some lw ->
  lm' !! (a', va) = Some lw.
Proof.
  move: lmem lm lmem' lm' vmap_mem vmap_mem' vmap_m vmap_m' a' v va lw.
  induction la as [|a la IHla]
  ; intros * HNoDup Ha'_in_la Hlmem_incl Hvmap_incl
               HmemMap HcurMap HmaxMap
               Hupd_lmem Hupd_lm Hlw
  ; first (cbn in * ; simplify_map_eq; eapply lookup_weaken ; eauto).

  apply elem_of_cons in Ha'_in_la.
  apply NoDup_cons in HNoDup
  ; destruct HNoDup as [Ha_notin_la HNoDup].

  rewrite Forall_cons in HmemMap
  ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
  rewrite Forall_cons in HcurMap
  ; destruct HcurMap as [ Hcur_v HcurMap].
  rewrite Forall_cons in HmaxMap
  ; destruct HmaxMap as [ Hmax_v HmaxMap].

  apply update_cur_version_region_global_cons in Hupd_lmem
  ; destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

  apply update_cur_version_region_local_cons in Hupd_lm
  ; destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

  destruct Ha'_in_la as [-> | Ha'_in_la].
  - assert (vmap_m0 !! a = Some v) as Hvmap_m0_a
        by (rewrite -(update_cur_version_region_local_notin_preserves_cur
                        lm lm0 vmap_m vmap_m0 la a)
            ; eauto).
    assert (lm0 !! (a, v) = Some lwa) as Hlm0_a
        by (rewrite -(update_cur_version_region_local_preserves_content_lmem
                        lm lm0 vmap_m vmap_m0 la a)
            ; eauto).
    rewrite /update_cur_version_addr_local in Hupd_lm0.
    rewrite Hvmap_m0_a Hlm0_a in Hupd_lm0; simplify_map_eq.
    destruct (decide (va = v+1)); simplify_map_eq.
    { assert (lm !! (a, v) = Some lw) as Hlm_a.
      {

        erewrite <- update_cur_version_region_local_notin_preserves_lmem_inv
        ; eauto.
        assert (lm !! (a, v) = Some lw) as Hlw'.
        {
          rewrite /update_cur_version_addr_global in Hupd_lmem0.
          destruct (vmap_mem0 !! a) as [va|] eqn:Hvmap_mem0_a.
          2: { simplify_map_eq.
               eapply update_cur_version_region_global_notin_preserves_lm_inv
                 in Hlw; eauto.
               by rewrite Hlw in Hmax_v.
          }
          eapply update_cur_version_region_global_notin_preserves_cur_2
            in Hvmap_mem0_a
          ; eauto.
          rewrite /is_cur_addr /= in Hvmap_mem0_a.
          eapply lookup_weaken in Hvmap_mem0_a ; eauto.
          rewrite Hvmap_mem0_a in Hcur_v ; simplify_eq.

          rewrite Hlwa in Hupd_lmem0; simplify_eq.
          by simplify_map_eq.
        }
        by rewrite Hlwa in Hlw' ; simplify_map_eq.

      }
      by rewrite Hlm_a in Hlwa ; simplify_eq.
    }
    {
      rewrite lookup_insert_ne /= ; eauto.
      2: (intro ; simplify_eq).
      clear IHla HmemMap HcurMap HmaxMap.
      - destruct (vmap_mem0 !! a) eqn:Hvmap_mem0_a.
        2: {
          rewrite /update_cur_version_addr_global in Hupd_lmem0.
          rewrite Hvmap_mem0_a in Hupd_lmem0; simplify_eq.
          eapply
            update_cur_version_region_global_notin_preserves_lm_inv
            in Hlw.
          2,3,4: eauto.
          erewrite update_cur_version_region_local_preserves_content_lmem in Hlw; eauto.
        }
        assert (v = v0) as ->.
        {
          eapply update_cur_version_region_global_notin_preserves_cur_2
            in Hvmap_mem0_a
          ; eauto.
          rewrite /is_cur_addr /= in Hvmap_mem0_a.
          eapply lookup_weaken in Hvmap_mem0_a ; eauto.
          by rewrite Hvmap_mem0_a in Hcur_v ; simplify_eq.
        }

        rewrite /update_cur_version_addr_global Hvmap_mem0_a Hlwa in Hupd_lmem0
        ; simplify_map_eq.
        rewrite lookup_insert_ne //= in Hlw; [| intro; simplify_eq ;lia].

        erewrite <- update_cur_version_region_local_preserves_content_lmem with (lmem := lm)
        ; eauto.

        eapply update_cur_version_region_global_notin_preserves_lmem_inv
          in Hlw. 2,3: eauto.
        eapply lookup_weaken; eauto.
    }

  - assert (a ≠ a') as Ha_neq_a' by set_solver.
    assert (lmem0 !! (a', va) = Some lw) as Hlmem0_a'.
    { eapply update_cur_version_addr_global_notin_preserves_lmem_inv
      ; eauto.
    }
    erewrite <- update_cur_version_addr_local_preserves_content_lmem
      with (lmem := lm0)
    ; eauto.
Qed.

Lemma update_cur_version_inter
  (lmem lmem0 lmem' lm lm0 : LMem)
  (vmap_mem vmap_mem0 vmap_mem' vmap_m vmap_m0 : VMap)
  ( a0 : Addr ) (la : list Addr) :
  a0 ∉ la ->
  NoDup la ->
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  update_cur_version_region_global lmem lm vmap_mem la = (lmem0, vmap_mem0) ->
  update_cur_version_region_local lm vmap_m la = (lm0, vmap_m0) ->
  update_cur_version_addr_global lmem0 lm vmap_mem0 a0 = (lmem', vmap_mem') ->
  update_cur_version_addr_global lmem0 lm0 vmap_mem0 a0 = (lmem', vmap_mem').
Proof.
  move: lmem lmem0 lmem' lm lm0 vmap_mem vmap_mem0 vmap_mem' vmap_m vmap_m0 a0.
  induction la as [|a la IHla]
  ; intros * Ha0_notin_la HNoDup_la Hlmem_incl Hvmap_incl Hupd_lmem Hupd_lm Hupd_lmem0
  ; first (by simplify_map_eq).

  apply NoDup_cons in HNoDup_la.
  destruct HNoDup_la as [Ha_notin_la HNoDup_la].

  apply not_elem_of_cons in Ha0_notin_la.
  destruct Ha0_notin_la as [Ha0_neq_a Ha0_notin_la].

  apply update_cur_version_region_global_cons in Hupd_lmem.
  destruct Hupd_lmem as (lmem1 & vmap_mem1 & Hupd_lmem & Hupd_lmem1).

  apply update_cur_version_region_local_cons in Hupd_lm.
  destruct Hupd_lm as (lm1 & vmap_m1 & Hupd_lm & Hupd_lm1).

  rewrite -Hupd_lmem0.
  rewrite /update_cur_version_addr_global.
  destruct (vmap_mem0 !! a0) as [va0|] ; auto.

  eapply update_cur_version_region_local_preserves_content_lmem
    with (a := a0) in Hupd_lm; eauto.
  erewrite update_cur_version_addr_local_preserves_content_lmem
    with (lmem := lm1) (lmem' := lm0) (a := a0) in Hupd_lm; eauto.
  by rewrite Hupd_lm.
  Unshelve. all: eauto.
Qed.


Lemma update_cur_version_addr_inter_incl_vmap
  (lmem lmem' lm lm' : LMem) (vmap_mem vmap_mem' vmap_m vmap_m' : VMap) (a : Addr) :
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  update_cur_version_addr_global lmem lm vmap_mem a = (lmem', vmap_mem') ->
  update_cur_version_addr_local lm vmap_m a = (lm', vmap_m') ->
  vmap_mem' ⊆ vmap_m'.
Proof.
  intros Hlmem_incl Hvmap_incl Hupd_lmem Hupd_lm.
  rewrite /update_cur_version_addr_global in Hupd_lmem.
  rewrite /update_cur_version_addr_local in Hupd_lm.
  destruct (vmap_mem !! a) as [va|] eqn:Hvmap_mem_a ; simplify_map_eq.
  - eapply lookup_weaken in Hvmap_mem_a; eauto ; simplify_map_eq.
    destruct (lm !! (a,va)) as [lw|]; simplify_map_eq; auto.
    by apply insert_mono.
  - destruct (vmap_m !! a) as [va|] eqn:Hvmap_m_a ; simplify_map_eq; auto.
    destruct (lm !! (a,va)) as [lw|]; simplify_map_eq; auto.
    by apply insert_subseteq_r.
Qed.

Lemma update_cur_version_addr_inter_incl_lmem
  (lmem lmem' lm lm' : LMem) (vmap_mem vmap_mem' vmap_m vmap_m' : VMap) (a : Addr) :
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  (∀ v, is_cur_addr (a, v) vmap_m -> lm !! (a, v+1) = None) ->
  update_cur_version_addr_global lmem lm vmap_mem a = (lmem', vmap_mem') ->
  update_cur_version_addr_local lm vmap_m a = (lm', vmap_m') ->
  lmem' ⊆ lm'.
Proof.
  intros Hlmem_incl Hvmap_incl Hmaxv_a Hupd_lmem Hupd_lm.
  rewrite /update_cur_version_addr_global in Hupd_lmem.
  rewrite /update_cur_version_addr_local in Hupd_lm.
  destruct (vmap_mem !! a) as [va|] eqn:Hvmap_mem_a ; simplify_map_eq.
  - eapply lookup_weaken in Hvmap_mem_a; eauto ; simplify_map_eq.
    destruct (lm !! (a,va)) as [lw|]; simplify_map_eq; auto.
    by apply insert_mono.
  - destruct (vmap_m !! a) as [va|] eqn:Hvmap_m_a ; simplify_map_eq; auto.
    destruct (lm !! (a,va)) as [lw|] eqn:Hlm_a; simplify_map_eq; auto.
    apply insert_subseteq_r; auto.
    eapply lookup_weaken_None; eauto.
Qed.

Lemma update_cur_version_addr_inter_incl
  (lmem lmem' lm lm' : LMem) (vmap_mem vmap_mem' vmap_m vmap_m' : VMap) (a : Addr) :
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  (∀ v, is_cur_addr (a, v) vmap_m -> lm !! (a, v+1) = None) ->
  update_cur_version_addr_global lmem lm vmap_mem a = (lmem', vmap_mem') ->
  update_cur_version_addr_local lm vmap_m a = (lm', vmap_m') ->
  lmem' ⊆ lm' ∧ vmap_mem' ⊆ vmap_m'.
Proof.
  intros Hlmem_incl Hvmap_incl Hmaxv_a Hupd_lmem Hupd_lm.
  rewrite /update_cur_version_addr_global in Hupd_lmem.
  rewrite /update_cur_version_addr_local in Hupd_lm.
  destruct (vmap_mem !! a) as [va|] eqn:Hvmap_mem_a ; simplify_map_eq.
  - eapply lookup_weaken in Hvmap_mem_a; eauto ; simplify_map_eq.
    destruct (lm !! (a,va)) as [lw|]; simplify_map_eq; auto.
    split ; by apply insert_mono.
  - destruct (vmap_m !! a) as [va|] eqn:Hvmap_m_a ; simplify_map_eq; auto.
    destruct (lm !! (a,va)) as [lw|] eqn:Hlm_a; simplify_map_eq; auto.
    split; apply insert_subseteq_r; auto.
    eapply lookup_weaken_None; eauto.
Qed.

Lemma update_cur_version_region_inter_incl
  (lmem lmem' lm lm' : LMem) (vmap_mem vmap_mem' vmap_m vmap_m' : VMap) (la : list Addr) :
  NoDup la ->
  lmem ⊆ lm ->
  vmap_mem ⊆ vmap_m ->
  Forall (fun a => (∀ v, is_cur_addr (a, v) vmap_m -> lm !! (a, v+1) = None)) la ->
  update_cur_version_region_global lmem lm vmap_mem la = (lmem', vmap_mem') ->
  update_cur_version_region_local lm vmap_m la = (lm', vmap_m') ->
  lmem' ⊆ lm' /\
    vmap_mem' ⊆ vmap_m'
.
Proof.
  move: lmem lmem' lm lm' vmap_mem vmap_mem' vmap_m vmap_m'.
  induction la as [|a la IHla]
  ; intros * HNoDup Hlmem_incl Hvmap_incl Hmaxv Hupd_lmem Hupd_lm
  ; first (simplify_map_eq ; split ; set_solver).

  apply NoDup_cons in HNoDup.
  destruct HNoDup as [Ha_notin_la HNoDup_la].

  apply Forall_cons in Hmaxv.
  destruct Hmaxv as [Hmaxv Hmaxv_la].

  apply update_cur_version_region_global_cons in Hupd_lmem.
  destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

  apply update_cur_version_region_local_cons in Hupd_lm.
  destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

  (* assert (vmap_mem0 ⊆ vmap_m0) as Hvmap0_incl by (eapply IHla; eauto). *)
  assert (lmem0 ⊆ lm0 /\ vmap_mem0 ⊆ vmap_m0) as
    [Hlmem0_incl Hvmap0_incl]
      by (eapply IHla ; eauto).

  eapply update_cur_version_addr_inter_incl; eauto.
  { intros v Hcur_v'.
    rewrite /is_cur_addr /= in Hcur_v'.
    erewrite <- update_cur_version_region_local_notin_preserves_cur in Hcur_v'
    ; eauto.
    eapply Hmaxv in Hcur_v'.
    erewrite <- update_cur_version_region_local_preserves_content_lmem; eauto.
  }

  clear Hlmem0_incl Hvmap0_incl.
  eapply update_cur_version_inter; eauto.
Qed.

Lemma update_cur_version_region_inter_incl_vmap'
  (lmem lmem' lm lm' : LMem) (vmap vmap_m' vmap_mem' : VMap) (la : list Addr) ( a0 : Addr ):
  NoDup la ->
  a0 ∉ la ->
  update_cur_version_region_local lm vmap la = (lm', vmap_m') ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap_mem') ->
  vmap_mem' !! a0 = vmap_m' !! a0.
Proof.
  move: lmem lmem' lm lm' vmap vmap_m' vmap_mem' a0.
  induction la as [|a la IHla]
  ; intros * HNoDup Ha0_notint_la Hupd_lm Hupd_lmem ; first (by cbn in * ; simplify_eq).

  apply NoDup_cons in HNoDup.
  destruct HNoDup as [Ha_notin_la HNoDup_la].

  apply not_elem_of_cons in Ha0_notint_la.
  destruct Ha0_notint_la as [Ha0_neq_a Ha0_notin_la].

  apply update_cur_version_region_local_cons in Hupd_lm
  ; destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

  apply update_cur_version_region_global_cons in Hupd_lmem
  ; destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

  destruct (vmap_m' !! a0) as [va0|] eqn:Hlva0.
  - erewrite <- update_cur_version_addr_local_notin_preserves_cur in Hlva0
    ; [| eauto |]; eauto.
    erewrite <- update_cur_version_region_local_notin_preserves_cur in Hlva0
    ; [| eauto |]; eauto.

    eapply update_cur_version_region_global_notin_preserves_cur_1 in Hupd_lmem
    ; [| eauto |]; eauto.
    eapply update_cur_version_addr_global_notin_preserves_cur_1 in Hupd_lmem0
    ; [| eauto |]; eauto.

  - destruct (vmap_mem' !! a0) as [va0'|] eqn:Hlva0' ; auto.
    eapply update_cur_version_addr_global_notin_preserves_cur_2 in Hupd_lmem0
    ; [| eauto |]; eauto.
    eapply update_cur_version_region_global_notin_preserves_cur_2 in Hupd_lmem0
    ; [| eauto |]; eauto.

    eapply update_cur_version_region_local_notin_preserves_cur in Hupd_lm; eauto.
    eapply update_cur_version_addr_local_notin_preserves_cur in Hupd_lm0 ; eauto.
    rewrite Hupd_lm in Hupd_lmem0 ; simplify_eq.
    rewrite Hupd_lm0 in Hupd_lmem0 ; simplify_eq.
Qed.





(** Machinery to update the memory for a given version,
    without knowing the view map *)

(* Update the lmemory for the address a.
   Note that lmem might not contain (a,v),
   because lmem is only a *local* view of the actual lmemory. *)
Definition update_version_addr_local
  (lmem : LMem) (a : Addr) (v : Version) : LMem :=
  match lmem !! (a,v) with
  | Some lw => <[ (a, v+1) := lw ]>lmem
  | None => lmem
  end.

(* Update the lmemory region for a given lregion.
   Note that it only updates the *local* view of the lmemory,
   which might not contain some of the addresses in la. *)
Definition update_version_region_local
  (lmem : LMem) (la : list Addr) (v : Version) : LMem :=
  foldr (fun a lmem' => update_version_addr_local lmem' a v) lmem la.



(* TODO move *)
Lemma update_version_addr_local_lookup_neq
  (lmem : LMem) (a a' : Addr) (v v': Version) :
  a ≠ a' ->
  update_version_addr_local lmem a v !! (a', v') = lmem !! (a', v')
.
Proof.
  intros Hneq.
  rewrite /update_version_addr_local.
  destruct (lmem !! (a,v)); auto.
  rewrite lookup_insert_ne //=; by intro ; simplify_eq.
Qed.

Lemma update_cur_version_addr_global_local
  (lmem lm lmem' : LMem) (vmap vmap' : VMap)
  (a : Addr) (v : Version) :
  lmem ⊆ lm ->
  lm !! (a, v + 1) = None ->
  is_Some (lm !! (a, v)) ->
  vmap !! a = Some v ->
  update_cur_version_addr_global lmem lm vmap a = (lmem', vmap') ->
  update_version_addr_local lmem a v ⊆ lmem'.
Proof.
  intros Hlmem_incl Hmaxv [lw Hlw_a] Hcur Hupd.
  rewrite /update_cur_version_addr_global Hcur Hlw_a in Hupd
  ; simplify_eq.
  rewrite /update_version_addr_local.
  destruct (lmem !! (a, v)) eqn:?.
  by eapply lookup_weaken in Heqo ; eauto ; rewrite Heqo in Hlw_a ; simplify_map_eq.
  eapply lookup_weaken_None in Hmaxv; eauto.
  eapply insert_subseteq_r; eauto.
Qed.

Lemma update_version_region_local_notin_preserves_lmem
  (lmem : LMem) (la : list Addr) (a' : Addr) (v v': Version) :
  a' ∉ la ->
  update_version_region_local lmem la v !! (a', v') = lmem !! (a', v').
Proof.
  move: lmem a' v v'.
  induction la as [|a la IHla] ; intros * Ha'_notin_la.
  - by cbn in *.
  - apply not_elem_of_cons in Ha'_notin_la
    ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
        /update_version_addr_local.
    destruct (update_version_region_local lmem la v !! (a, v))
      as [lwa|] eqn:Hlwa.
    + rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
      eapply IHla; eauto.
    + eapply IHla; eauto.
Qed.

Lemma update_version_region_local_preserves_lmem
  (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version) :
  update_version_region_local lmem la v !! (a', v) = lmem !! (a', v).
Proof.
  move: lmem a' v.
  induction la as [|a la IHla] ; intros *.
  - by cbn in *.
  - rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
    rewrite /update_version_addr_local.
    destruct (update_version_region_local lmem la v !! (a, v))
      as [lwa|] eqn:Hlwa.
    + rewrite lookup_insert_ne //=; last (intro ; simplify_eq ; lia).
    + eapply IHla; eauto.
Qed.

Lemma update_version_region_local_inv_1
  (lmem : LMem) (la : list Addr) (a : Addr) (v v': Version):
  a ∉ la -> update_version_region_local lmem la v !! (a, v') = lmem !! (a, v').
Proof.
  move: lmem a v v'.
  induction la as [|a' la IHla] ; intros * Ha_notin_la
  ; first (cbn in *; eauto).

  apply not_elem_of_cons in Ha_notin_la
  ; destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].

  rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
  rewrite update_version_addr_local_lookup_neq; eauto.
Qed.

(* TODO refactor the proof *)
Lemma update_version_region_local_inv_2
  (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version):
  a' ∈ la
  → update_version_region_local lmem la v !! (a', v) = lmem !! (a', v).
Proof.
  move: lmem a' v.
  induction la as [|a la IHla]; intros * Hin.
  set_solver.
  rewrite elem_of_cons in Hin.
  rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
  destruct Hin ; simplify_map_eq.
  - destruct (decide (a ∈ la)) as [ Ha_in_la | Ha_notin_la ].
    + rewrite /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
      ++ rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
         rewrite IHla; eauto.
      ++ rewrite IHla; eauto.
    + rewrite /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
      ++ rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
         erewrite update_version_region_local_notin_preserves_lmem; eauto.
      ++ erewrite update_version_region_local_notin_preserves_lmem; eauto.
  - destruct (decide (a' = a)); simplify_eq.
    + rewrite /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
      ++ rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
         erewrite update_version_region_local_preserves_lmem; eauto.
      ++ erewrite update_version_region_local_preserves_lmem; eauto.
    + rewrite /update_version_addr_local.
      destruct (update_version_region_local lmem la v !! (a, v)) as [lwa|] eqn:Hlwa.
      ++ rewrite lookup_insert_ne; [|intro; simplify_eq; lia].
         rewrite IHla; eauto.
      ++ rewrite IHla; eauto.
Qed.

Lemma update_version_region_local_inv
  (lmem : LMem) (la : list Addr) (a : Addr) (v : Version):
  update_version_region_local lmem la v !! (a, v) = lmem !! (a, v).
Proof.
  intros *.
  destruct (decide (a ∈ la)).
  - eapply update_version_region_local_inv_2 ; eauto.
  - eapply update_version_region_local_inv_1 ; eauto.
Qed.

(* TODO refactor the proof *)
Lemma update_cur_version_region_global_local
  (lmem lm lmem' : LMem)
  (vmap vmap' : VMap)
  (la : list Addr)
  (v : Version) :
  NoDup la ->
  lmem ⊆ lm ->
  Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
  Forall (λ a0 : Addr, vmap !! a0 = Some v) la ->
  Forall (λ a0 : Addr, (lm !! (a0, v +1) = None)) la ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap') ->
  update_version_region_local lmem la v ⊆ lmem'.
Proof.
  move: lmem lm lmem' vmap vmap' v.
  induction la as [|a la IHla]
  ; intros * HNoDup Hlmem_incl HmemMap HcurMap HmaxMap Hupd
  ; first ( cbn in * ; simplify_map_eq ; by set_solver ).

  apply NoDup_cons in HNoDup
  ; destruct HNoDup as [Ha_notin_la HNoDup_la].
  rewrite Forall_cons in HmemMap
  ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
  rewrite Forall_cons in HcurMap
  ; destruct HcurMap as [ Hcur_v HcurMap].
  rewrite Forall_cons in HmaxMap
  ; destruct HmaxMap as [ Hmax_v HmaxMap].

  apply update_cur_version_region_global_cons in Hupd
  ; destruct Hupd as (lmem0 & vmap_mem0 & Hupd & Hupd0).

  cbn.
  rewrite -/(update_version_region_local lmem la v).
  pose proof Hupd0 as Hupd0'.


  destruct (update_cur_version_region_local lm vmap la)
    as [lm' vmap_m'] eqn:Hupd_lm.
  pose proof Hupd_lm as Hupd_lm'.
  eapply update_cur_version_inter in Hupd_lm; eauto.

  (* -------------------- *)
  assert (lm' !! (a, v + 1) = None)
    by (erewrite <- update_cur_version_region_local_preserves_content_lmem; [| |eauto]; eauto).
  assert (lm' !! (a, v) = Some lwa) as Hlwa'
    by (erewrite <- update_cur_version_region_local_preserves_content_lmem; [| |eauto]; eauto).
  eapply update_cur_version_addr_global_local in Hupd_lm; eauto.
  3:{
    eapply update_cur_version_region_global_notin_preserves_cur_1; eauto.
  }
  2:{
    apply map_subseteq_spec.
    intros [a0 va0] lwa0 Hlwa0.
    destruct (decide (a0 ∈ la)).
    {
      eapply inter_region_aaa; eauto.
    }
    { erewrite <- update_cur_version_region_local_preserves_content_lmem; [| |eauto]; eauto.
      eapply update_cur_version_region_global_notin_preserves_lm_inv in Hlwa0; eauto.
    }
  }
  {
    assert ((update_version_region_local lmem la v) ⊆ lmem0).
    { eapply IHla ; eauto. }
    rewrite /update_version_addr_local.
    assert (update_version_region_local lmem la v ⊆ lmem').
    { rewrite /update_version_addr_local in Hupd0.
      destruct (lmem0 !! (a, v)) eqn:?.
      - eapply map_subseteq_spec.
        intros a' lwa' Hlwa'0.
        assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
            (eapply lookup_weaken in Hlwa'0; [|eassumption] ; by eauto).
        assert (<[(a, v + 1):=l]> lmem0 !! (a,v) = Some l).
        { rewrite lookup_insert_ne //=; intro ; simplify_eq; lia. }
        destruct (decide (a' = (a,v))); simplify_map_eq.
        + rewrite update_version_region_local_inv in Hlwa'0 ; eauto.
          eapply lookup_weaken in Hlwa'0; last eapply Hlmem_incl.
          rewrite Hlwa in Hlwa'0; simplify_eq.
          rewrite Hlmem0_a' in Heqo; simplify_eq.
          eapply lookup_weaken; eauto.
          rewrite /update_cur_version_addr_global in Hupd0.
          assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
              by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
          rewrite Hvmap_mem0_a Hlwa in Hupd0; simplify_eq.
          done.
        (* by rewrite /update_lmemory_lword. *)
        + eapply lookup_weaken; eauto.
          assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
              by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
          eapply update_cur_version_addr_global_incl_lmem; eauto.
          eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
          eapply lookup_weaken_None; [eapply Hmax_v|]; eauto.
      - eapply map_subseteq_spec.
        intros a' lwa' Hlwa'0.
        assert (lmem0 !! a' = Some lwa') as Hlmem0_a' by
            (eapply lookup_weaken in Hlwa'0; [|eassumption] ; by eauto).
        eapply lookup_weaken ; eauto.
        rewrite /update_cur_version_addr_global in Hupd0.
        assert (vmap_mem0 !! a = Some v) as Hvmap_mem0_a
            by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
        rewrite Hvmap_mem0_a Hlwa in Hupd0; simplify_eq.
        eapply insert_subseteq_r; eauto.
        eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
        eapply lookup_weaken_None; [eapply Hmax_v|]; eauto.
    }
    destruct (update_version_region_local lmem la v !! (a, v)) eqn:?; auto.
    {eapply insert_subseteq_l; auto.
     rewrite update_version_region_local_inv in Heqo ; eauto.
     eapply lookup_weaken in Hlmem_incl ; eauto.
     rewrite Hlmem_incl in Hlwa; simplify_map_eq.

     eapply update_cur_version_region_global_preserves_content_lmem
       in Heqo; eauto.
     eapply update_cur_version_region_global_notin_preserves_cur_1
       in Hcur_v; eauto.

     rewrite /update_cur_version_addr_global in Hupd0'.
     rewrite Hcur_v /= Hlmem_incl /= in Hupd0'.
     simplify_eq.
     by simplify_map_eq.
    }
  }
Qed.

Lemma update_version_region_local_preserves_lmem_next
  (lmem : LMem) (la : list Addr) (a' : Addr) (v : Version) :
  NoDup la ->
  a' ∈ la ->
  lmem !! (a', v+1) = None ->
  update_version_region_local lmem la v !! (a', v + 1) = lmem !! (a', v).
Proof.
  move: lmem a' v.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la Hlmem_next
  ; first (by set_solver).
  apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup].
  apply elem_of_cons in Ha'_in_la.

  rewrite /update_version_region_local /= -/(update_version_region_local lmem la v).
  rewrite /update_version_addr_local.
  destruct Ha'_in_la as [|Ha'_in_la] ; simplify_map_eq.
  - destruct (update_version_region_local lmem la v !! (a, v))
      as [lwa|] eqn:Hlwa; rewrite update_version_region_local_inv in Hlwa.
    + by simplify_map_eq.
    + rewrite Hlwa update_version_region_local_notin_preserves_lmem; eauto.
  - destruct (update_version_region_local lmem la v !! (a, v))
      as [lwa|] eqn:Hlwa; rewrite update_version_region_local_inv in Hlwa.
    + rewrite lookup_insert_ne //= ; [|intro ; simplify_eq ; set_solver].
      erewrite IHla; eauto.
    + erewrite IHla; eauto.
Qed.

Lemma update_version_region_local_insert
  (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord):
  NoDup la ->
  a' ∉ la ->
  lmem !! (a', v') = None ->
  Forall (fun a => lmem !! (a, v+1) = None) la ->
  update_version_region_local (<[(a', v'):=lw]> lmem) la v ⊆ lmem' ->
  update_version_region_local lmem la v ⊆ lmem'.
Proof.
  move: lmem lmem' a' v v' lw.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None HmaxMap Hupd.
  - cbn in *.
    eapply insert_delete_subseteq in Hupd; eauto.
    apply map_subseteq_spec ; intros [a0 v0] lw0 Hlw0.
    eapply lookup_weaken in Hlw0 ; last eauto.
    assert ((a0, v0) ≠ (a', v')) as Hneq by (intro ; simplify_map_eq).
    rewrite lookup_delete_ne in Hlw0 ; eauto.
  - rewrite NoDup_cons in HNoDup; destruct HNoDup as [Ha_noit_la HNoDup_la].
    rewrite not_elem_of_cons in Ha'_notin_la
    ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].
    rewrite Forall_cons in HmaxMap ; destruct HmaxMap as [ Hmax_v HmaxMap].

    assert (update_version_region_local lmem la v ⊆ lmem').
    { eapply IHla with (a' := a') (v' := v') (lw := lw); eauto.

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
          /update_version_addr_local
        in Hupd.

      destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
        eqn:?
      ; rewrite update_version_region_local_preserves_lmem in Heqo
      ; last done.

      assert (
          (update_version_region_local (<[(a', v'):=lw]> lmem) la v)
            !! (a, v+1) = None).
      { rewrite update_version_region_local_notin_preserves_lmem; eauto.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
      }

      eapply map_subseteq_spec; intros [a0 v0] lw0 Hlw0.
      eapply lookup_weaken; last eauto.
      rewrite lookup_insert_ne //=.
      intro; simplify_eq.
      by rewrite H in Hlw0.
    }

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
        /update_version_addr_local
    .

    destruct (update_version_region_local lmem la v !! (a, v))
      eqn:?; last done.
    eapply insert_subseteq_l; eauto.

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
        /update_version_addr_local
      in Hupd.

    rewrite update_version_region_local_preserves_lmem in Heqo.
    destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
      eqn:?
    ; rewrite update_version_region_local_preserves_lmem in Heqo0
    ; (rewrite lookup_insert_ne in Heqo0 ; [| intro ; simplify_eq ])
    ; rewrite Heqo in Heqo0
    ; simplify_eq.
    eapply map_subseteq_spec in Hupd.
    eapply Hupd.
    by simplify_map_eq.
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
  (lmem : LMem) (la : list Addr) (v : Version) (lmem' : LMem) : Prop :=
  (update_version_region_local lmem la v) ⊆ lmem' /\
    (Forall (fun a => is_Some (lmem' !! (a, v+1))) la).


Lemma update_cur_version_region_global_valid
  (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (v : Version) :
  NoDup la ->
  lmem ⊆ lm ->
  Forall (λ a0 : Addr, cur_map !! a0 = Some v) la ->
  Forall (λ a0 : Addr, is_Some (lm !! (a0, v))) la ->
  Forall (λ a0 : Addr, lm !! (a0, v + 1) = None) la ->
  update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map') ->
  is_valid_updated_lmemory lmem la v lmem'.
Proof.
  move: lmem lm lmem' cur_map cur_map' v.
  induction la as [|a la IHla]
  ; intros * HNoDup Hlmem_incl HcurMap HmemMap HmaxMap Hupd.
  - cbn in *; simplify_map_eq.
    split; cbn.
    set_solver.
    by apply Forall_nil.
  - rewrite NoDup_cons in HNoDup
    ; destruct HNoDup as [Ha_notin_la HNoDup_la].

    rewrite Forall_cons in HmemMap
    ; destruct HmemMap as [ [lwa Hlwa] HmemMap].
    rewrite Forall_cons in HcurMap
    ; destruct HcurMap as [ Hcur_v HcurMap].
    rewrite Forall_cons in HmaxMap
    ; destruct HmaxMap as [ Hmax_v HmaxMap].

    apply update_cur_version_region_global_cons in Hupd
    ; destruct Hupd as (lmem0 & cur_map0 & Hupd & Hupd0).

    assert ( is_valid_updated_lmemory lmem la v lmem0) as Hvalid
        by (eapply IHla ; eauto).
    split.
    + cbn.
      rewrite -/(update_version_region_local lmem la v).
      destruct Hvalid as [Hupd' _].
      assert (cur_map0 !! a = Some v) as Hcur0
          by (eapply update_cur_version_region_global_notin_preserves_cur_1; eauto).
      rewrite /update_version_addr_local.
      assert (update_version_region_local lmem la v ⊆ lmem').
      {
        assert (update_version_region_local lmem la v ⊆ lmem0).
        {
          eapply update_cur_version_region_global_local; eauto.
        }
        assert ( lmem0 ⊆ lmem').
        { rewrite /update_cur_version_addr_global in Hupd0.
          rewrite Hcur0 Hlwa in Hupd0; simplify_eq.
          eapply insert_subseteq_r; last done.
          eapply update_cur_version_region_global_notin_preserves_lmem; eauto.
          eapply lookup_weaken_None ; eauto.
        }
        rewrite map_subseteq_spec.
        intros a' lw' Hlw'.
        eapply lookup_weaken in H ; eauto.
        eapply lookup_weaken in H0 ; eauto.
      }
      destruct (update_version_region_local lmem la v !! (a, v)) eqn:?; auto.
      eapply insert_subseteq_l; auto.
      assert (lmem !! (a,v) = Some l).
      {
        rewrite update_version_region_local_inv in Heqo; eauto.
      }
      assert (lmem0 !! (a,v) = Some l)
        by (eapply update_cur_version_region_global_preserves_content_lmem; eauto).
      eapply lookup_weaken in H0; eauto.
      rewrite H0 in Hlwa ; simplify_map_eq.
      rewrite /update_cur_version_addr_global in Hupd0.
      rewrite Hcur0 in Hupd0.
      rewrite H0 in Hupd0.
      simplify_map_eq.
      by simplify_map_eq.
    + apply Forall_cons.
      split.
      * eapply update_cur_version_region_global_notin_preserves_cur_1 in Hcur_v ; eauto.
        rewrite /update_cur_version_addr_global in Hupd0.
        rewrite Hcur_v /= Hlwa in Hupd0 ; simplify_eq.
        by simplify_map_eq.
      * apply Forall_forall.
        intros a' Ha'_in_la.
        destruct Hvalid as [_ Hsome].
        apply elem_of_list_lookup in Ha'_in_la.
        destruct Ha'_in_la as [? Ha'].
        eapply Forall_lookup in Hsome ; eauto.
        destruct Hsome as [lwa0 Hlwa0].
        exists lwa0.
        destruct ( (decide (a = a'))) as [| Ha'_neq_a]; simplify_map_eq.
        2: { eapply update_cur_version_addr_global_notin_preserves_lmem; eauto. }
        exfalso.
        eapply update_cur_version_region_global_notin_preserves_lmem_inv in Hlwa0; eauto.
        eapply lookup_weaken in Hlwa0 ; eauto.
        by rewrite Hlwa0 in Hmax_v.
Qed.



Lemma is_valid_updated_lmemory_notin_preserves_lmem
  (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
  a' ∉ la ->
  is_valid_updated_lmemory lmem la v lmem' ->
  lmem !! (a', v') = Some lw ->
  lmem' !! (a', v') = Some lw.
Proof.
  move: lmem lmem' a' v v' lw.

  induction la as [|a la IHla] ; intros * Ha'_notin_la [Hcompatibility Hupdated] Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto).

  apply not_elem_of_cons in Ha'_notin_la
  ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].

  apply Forall_cons in Hupdated
  ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

  rewrite
    /update_version_region_local
      /=
      -/(update_version_region_local lmem la v)
    in Hcompatibility.

  rewrite map_subseteq_spec in Hcompatibility.
  apply Hcompatibility.

  rewrite /update_version_addr_local.
  + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
    * rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
      rewrite update_version_region_local_notin_preserves_lmem; eauto.
    * rewrite update_version_region_local_notin_preserves_lmem; eauto.
Qed.

Lemma is_valid_updated_lmemory_preserves_lmem
  (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
  is_valid_updated_lmemory lmem la v lmem' ->
  lmem !! (a', v) = Some lw ->
  lmem' !! (a', v) = Some lw.
Proof.
  move: lmem lmem' a' v lw.

  induction la as [|a la IHla] ; intros * [Hcompatibility Hupdated] Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto).

  apply Forall_cons in Hupdated
  ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

  rewrite
    /update_version_region_local
      /=
      -/(update_version_region_local lmem la v)
    in Hcompatibility.

  rewrite map_subseteq_spec in Hcompatibility.
  apply Hcompatibility.

  rewrite /update_version_addr_local.
  + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
    * rewrite lookup_insert_ne //=; last (intro ; simplify_eq; lia).
      rewrite update_version_region_local_preserves_lmem; eauto.
    * rewrite update_version_region_local_preserves_lmem; eauto.
Qed.

Lemma is_valid_updated_lmemory_preserves_lmem_next
  (lmem lmem' : LMem) (la : list Addr) (a' : Addr) (v : Version) (lw : LWord) :
  NoDup la ->
  a' ∈ la ->
  is_valid_updated_lmemory lmem la v lmem' ->
  Forall (fun a => lmem !! (a, v+1) = None) la ->
  lmem !! (a', v) = Some lw ->
  lmem' !! (a', v+1) = Some lw.
Proof.
  move: lmem lmem' a' v lw.

  induction la as [|a la IHla] ; intros * HNoDup Ha'_in_la [Hcompatibility Hupdated] Hmax_la Hlmem
  ; first (cbn in *; eapply lookup_weaken ; eauto; set_solver).

  apply NoDup_cons in HNoDup
  ; destruct HNoDup as [Ha_notin_la HNoDup].
  apply elem_of_cons in Ha'_in_la.

  apply Forall_cons in Hupdated
  ; destruct Hupdated as [ [ lwa Hlwa ] Hupdated ].

  apply Forall_cons in Hmax_la
  ; destruct Hmax_la as [ Hmax_a Hmax_la ].

  rewrite
    /update_version_region_local
      /=
      -/(update_version_region_local lmem la v)
    in Hcompatibility.

  rewrite map_subseteq_spec in Hcompatibility.
  apply Hcompatibility.
  rewrite -(update_version_region_local_preserves_lmem _ la) in Hlmem; eauto.

  rewrite /update_version_addr_local.
  + destruct ( update_version_region_local lmem la v !! (a, v) ) as [lwa'|] eqn:Hlwa'.
    * destruct Ha'_in_la as [? | Ha'_in_la] ; simplify_map_eq; first done.
      pose proof Ha'_in_la as Ha'_in_la'.
      apply elem_of_list_lookup in Ha'_in_la'.
      destruct Ha'_in_la' as [? Ha'_lookup].
      eapply Forall_lookup in Hmax_la ; eauto.
      rewrite lookup_insert_ne //=; last (intro ; simplify_eq; set_solver).

      rewrite update_version_region_local_preserves_lmem_next; eauto.
      rewrite update_version_region_local_preserves_lmem in Hlmem ; eauto.
    * destruct Ha'_in_la as [? | Ha'_in_la] ; simplify_map_eq.
      rewrite update_version_region_local_preserves_lmem in Hlmem; eauto.
      rewrite update_version_region_local_preserves_lmem_next ; eauto.
      apply elem_of_list_lookup_1 in Ha'_in_la; destruct Ha'_in_la as [? Ha'_in_la].
      eapply Forall_lookup in Hmax_la ; eauto.
Qed.


Lemma is_valid_updated_lmemory_preserves_lmem_incl
  (lmem' : LMem) (la : list Addr) (v : Version) (lws : list LWord) :
  NoDup la ->
  length lws = length la ->
  is_valid_updated_lmemory (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)) la v lmem' ->
  (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)) ⊆ lmem'.
Proof.
  move: lmem' v lws.
  induction la as [|a la IHla] ; intros * HNoDup Hlen Hvalid.
  - cbn in *; apply map_empty_subseteq.
  - cbn in *.
    destruct lws as [|lw lws]; simplify_eq.
    cbn in Hlen; injection Hlen ; clear Hlen ; intros Hlen.
    apply NoDup_cons in HNoDup
    ; destruct HNoDup as [Ha_notin_la HNoDup].
    cbn in *.
    destruct Hvalid as [Hupd_incl Hnext].
    rewrite Forall_cons in Hnext ; destruct Hnext as [Hnext HnextMap].
    rewrite /=
      -/(update_version_region_local
           (<[(a, v):=lw]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws)))
           la
           v)
      /update_version_addr_local
      update_version_region_local_notin_preserves_lmem
      in Hupd_incl; eauto; simplify_map_eq.
    assert (
        (update_version_region_local
           (<[(a, v):=lw]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws))) la v)
          ⊆ lmem').
    {
      assert (
          update_version_region_local (<[(a, v):=lw]> (list_to_map (zip (map (λ a0 : Addr, (a0, v)) la) lws)))
            la v !! (a, v + 1) = None
        ).
      {
        rewrite update_version_region_local_notin_preserves_lmem; eauto.
        rewrite lookup_insert_ne //= ; [| intro ; simplify_eq ; lia].
        apply not_elem_of_list_to_map; cbn.
        rewrite fst_zip; eauto; last (rewrite map_length; lia).
        intro Hcontra.
        apply elem_of_list_fmap in Hcontra.
        destruct Hcontra as (? & ? & Hcontra) ; simplify_eq; lia.
      }
      eapply insert_delete_subseteq in Hupd_incl; eauto.

      apply map_subseteq_spec; intros [a' v'] lwa' Hlwa'.
      eapply lookup_weaken in Hlwa'; last eauto.
      by apply lookup_delete_Some in Hlwa'; destruct Hlwa'.
    }

    eapply insert_subseteq_l; eauto.
    { assert (
          ((update_version_region_local (<[(a, v):=lw
                ]> (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws))) la v)
             !! (a,v)) = Some lw).
      { rewrite update_version_region_local_preserves_lmem; by simplify_map_eq. }
      eapply lookup_weaken; eauto.
    }
    { eapply IHla; eauto.
      split; eauto.
      eapply update_version_region_local_insert; eauto.
      { clear -Hlen Ha_notin_la.
        eapply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; last (rewrite map_length ; lia).
        rewrite elem_of_list_fmap in Hcontra.
        destruct Hcontra as (?&?&?); set_solver.
      }
      { clear -Hlen.
        apply Forall_forall.
        intros a Ha.
        eapply not_elem_of_list_to_map.
        intro Hcontra.
        rewrite fst_zip in Hcontra; last (rewrite map_length ; lia).
        rewrite elem_of_list_fmap in Hcontra.
        destruct Hcontra as (?&?&?) ; simplify_eq; lia.
      }
    }
Qed.

(* TODO refactor the proof *)
Lemma is_valid_updated_lmemory_insert
  (lmem lmem': LMem) (la : list Addr) (a' : Addr) (v v' : Version) (lw : LWord) :
  NoDup la ->
  a' ∉ la ->
  lmem !! (a', v') = None ->
  Forall (fun a => lmem !! (a, v+1) = None) la ->
  is_valid_updated_lmemory (<[(a', v') := lw]> lmem) la v lmem' ->
  is_valid_updated_lmemory lmem la v lmem'.
Proof.
  move: lmem lmem' a' v v' lw.
  induction la as [|a la IHla] ; intros * HNoDup Ha'_notin_la Hlmem_None HmaxMap Hvalid.
  - destruct Hvalid.
    split; cbn in *; last done.
    eapply map_subseteq_spec ; intros [a0 v0] lw0 Hlw0.
    eapply lookup_weaken ; last eapply H.
    rewrite lookup_insert_ne //=; intro ; simplify_eq.
    rewrite Hlmem_None in Hlw0 ; done.
  - rewrite NoDup_cons in HNoDup; destruct HNoDup as [Ha_noit_la HNoDup_la].
    rewrite not_elem_of_cons in Ha'_notin_la
    ; destruct Ha'_notin_la as [Ha'_neq_a Ha'_notin_la].
    rewrite Forall_cons in HmaxMap ; destruct HmaxMap as [ Hmax_v HmaxMap].

    assert (is_valid_updated_lmemory lmem la v lmem') as Hvalid_IH.
    { eapply IHla with (a' := a') (v' := v') (lw := lw); eauto.

      destruct Hvalid as [Hupd HnextMap].
      rewrite Forall_cons in HnextMap
      ; destruct HnextMap as [ [ lw' Hlw' ] HnextMap].

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
        in Hupd.
      split; eauto.

      rewrite
        /update_version_region_local
          /=
          -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
          /update_version_addr_local
        in Hupd.

      destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
        eqn:?
      ; rewrite update_version_region_local_preserves_lmem in Heqo
      ; last done.

      assert (
          (update_version_region_local (<[(a', v'):=lw]> lmem) la v)
            !! (a, v+1) = None).
      { rewrite update_version_region_local_notin_preserves_lmem; eauto.
        rewrite lookup_insert_ne //=; last (intro ; simplify_eq).
      }

      eapply map_subseteq_spec; intros [a0 v0] lw0 Hlw0.
      eapply lookup_weaken; last eauto.
      rewrite lookup_insert_ne //=.
      intro; simplify_eq.
      by rewrite H in Hlw0.
    }

    destruct Hvalid as [Hupd HnextMap].
    destruct Hvalid_IH as [Hupd_IH HnextMap_IH].
    split; last done.

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local lmem la v)
        /update_version_addr_local
    .

    destruct (update_version_region_local (lmem) la v !! (a, v))
      eqn:?; last done.
    eapply insert_subseteq_l; eauto.

    rewrite
      /update_version_region_local
        /=
        -/(update_version_region_local (<[(a', v'):=lw]> lmem) la v)
        /update_version_addr_local
      in Hupd.

    rewrite update_version_region_local_preserves_lmem in Heqo.
    destruct (update_version_region_local (<[(a', v'):=lw]> lmem) la v !! (a, v))
      eqn:?
    ; rewrite update_version_region_local_preserves_lmem in Heqo0
    ; (rewrite lookup_insert_ne in Heqo0 ; [| intro ; simplify_eq ])
    ; rewrite Heqo in Heqo0
    ; simplify_eq.
    eapply map_subseteq_spec in Hupd.
    eapply Hupd.
    by simplify_map_eq.
Qed.















(* Logical machine *)

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

Lemma is_cur_updatePcPermL (lw : LWord) cur_map:
  is_cur_word lw cur_map -> is_cur_word (updatePcPermL lw) cur_map.
Proof.
  destruct_lword lw ; cbn; auto.
  intros Hbounds.
  destruct p; auto.
Qed.

(* TODO duplicate with is_cur_word_lea *)
Lemma is_cur_word_change cur_map p p' b e a a' v lw lw':
  get_lcap lw = Some (LSCap p b e a v) ->
  get_lcap lw' = Some (LSCap p' b e a' v) ->
  is_cur_word lw cur_map ->
  is_cur_word lw' cur_map.
Proof.
  intros Hlw Hlw'.
  destruct_lword lw ; destruct_lword lw' ; cbn in * ; simplify_eq
  ; rewrite /is_cur_word; intros Hcur; auto.
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

Definition word_of_argumentL (lregs: LReg) (a: Z + RegName): option LWord :=
  match a with
  | inl n => Some (LInt n)
  | inr r => lregs !! r
  end.

Definition addr_of_argumentL lregs src :=
  match z_of_argumentL lregs src with
  | Some n => z_to_addr n
  | None => None
  end.

Definition otype_of_argumentL lregs src : option OType :=
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







(** Instantiation of the program logic *)


(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invGS Σ;
  mem_gen_memG :: gen_heapGS LAddr LWord Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invGS Σ;
  reg_gen_regG :: gen_heapGS RegName LWord Σ; }.

Definition state_interp_logical (σ : cap_lang.state) `{!memG Σ, !regG Σ} : iProp Σ :=
  ∃ lr lm cur_map , gen_heap_interp lr ∗ gen_heap_interp lm ∗
                      ⌜state_phys_log_corresponds σ.(reg) σ.(mem) lr lm cur_map⌝.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!memG Σ, !regG Σ} : irisGS cap_lang Σ := {
  iris_invGS := mem_invG;
  state_interp σ _ κs _ := state_interp_logical σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

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

Notation eqb_laddr := (λ (a1 a2: LAddr), (Z.eqb a1.1 a2.1) && (a1.2 =? a2.2)).
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

End machine_param.





(* TODO wtf with this ? where to put it ? *)


Lemma list_to_map_zip_inv
  (a : Addr) ( v v' : Version )
  (la : list Addr) (lws : list LWord) :
  NoDup la ->
  length lws = length la ->
  is_Some ((list_to_map (zip (map (λ a' : Addr, (a', v)) la) lws) : gmap LAddr LWord) !! (a, v')) ->
  (v' = v) /\ (a ∈ la).
Proof.
  intros HNoDup Hlen [lw Hlw].
  apply elem_of_list_to_map in Hlw.
  2:{
    rewrite fst_zip ; eauto; last  (rewrite map_length; lia).
    apply NoDup_fmap; auto.
    by intros x y Heq ; simplify_eq.
  }
  apply elem_of_zip_l in Hlw.
  apply elem_of_list_fmap in Hlw.
  by destruct Hlw as (? & ? & ?); simplify_eq.
Qed.

Lemma list_to_map_zip_version
  (la : list Addr) (a' : Addr) (v v' : Version) (lws : list LWord) :
  NoDup la ->
  a' ∈ la ->
  length lws = length la ->
  (list_to_map (zip (map (λ a : Addr, (a, v)) la) lws): gmap LAddr LWord) !! (a', v)
  = (list_to_map (zip (map (λ a : Addr, (a, v')) la) lws): gmap LAddr LWord) !! (a', v').
Proof.
  move: a' v v' lws.
  induction la as [|a la IHla]; intros * HNoDup Ha'_in_la Hlen.
  - cbn in *; set_solver.
  - cbn in Hlen; destruct lws as [|lw lws] ; simplify_eq.
    injection Hlen ; clear Hlen ; intro Hlen.

    apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup_la].
    apply elem_of_cons in Ha'_in_la.
    destruct Ha'_in_la; simplify_map_eq; first done.
    rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
    rewrite lookup_insert_ne /= ; last (intro ; simplify_eq; set_solver).
    by apply IHla.
Qed.

Lemma Forall_is_Some_list
  (lmem : LMem) (la : list Addr) (v : Version) :
  NoDup la ->
  Forall (λ a : Addr, is_Some (lmem !! (a, v))) la ->
  ∃ lws : list LWord,
    length lws = length la
    ∧ list_to_map (zip (map (λ a : Addr, (a, v)) la) lws) ⊆ lmem.
Proof.
  move: lmem v.
  induction la as [|a la IHla] ; intros * HNoDup HnextMap.
  - cbn in *. exists []. split; auto. apply map_empty_subseteq.
  - apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notint_la HNoDup_la].
    rewrite Forall_cons in HnextMap ; destruct HnextMap as [ [lwa Hlwa] HnextMap].
    eapply IHla in HnextMap; eauto.
    destruct HnextMap as (lws & Hlen & Hincl).
    exists (lwa::lws).
    split ; auto.
    cbn ; lia.
    apply map_subseteq_spec.
    intros [a' v'] lw' Hlw'.
    apply elem_of_list_to_map in Hlw'.
    2: {
      rewrite fst_zip.
      apply NoDup_fmap.
      { by intros x y Heq ; simplify_eq. }
      { by apply NoDup_cons. }
      { rewrite map_length; cbn; lia. }
    }
    cbn in *.
    rewrite elem_of_cons in Hlw'.
    destruct Hlw' as [?|Hlw'] ; simplify_map_eq; first done.
    eapply lookup_weaken; eauto.
    apply elem_of_list_to_map; auto.

    rewrite fst_zip;auto.
    apply NoDup_fmap;auto.
    { by intros x y Heq ; simplify_eq. }
    { rewrite map_length; cbn; lia. }
Qed.
