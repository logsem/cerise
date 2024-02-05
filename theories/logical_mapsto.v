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

Notation LCap p b e a v := (LWSealable (LSCap p b e a v)).
Notation LSealRange p b e a := (LWSealable (LSSealRange p b e a)).
Notation LSealedCap o p b e a v := (LWSealed o (LSCap p b e a v)).
Notation LInt z := (LWInt z).

Global Instance lword_inhabited: Inhabited LWord := populate (LInt 0).

Definition lword_get_version (lw : LWord) : option Version :=
  match lw with
  | LCap _ _ _ _ v | (LSealedCap _ _ _ _ _ v) => Some v
  | _ => None
  end.
Definition laddr_get_addr (la : LAddr) := la.1.
Definition laddr_get_version (la : LAddr) := la.2.

Lemma laddr_inv la : (laddr_get_addr la, laddr_get_version la) = la.
Proof. destruct la ; auto. Qed.

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

Instance version_eq_dec : EqDecision Version.
Proof. solve_decision. Qed.
Instance lsealb_eq_dec : EqDecision LSealable.
Proof. solve_decision. Qed.
Instance lword_eq_dec : EqDecision LWord.
Proof. solve_decision. Qed.

Definition VMap : Type := gmap Addr Version.
Definition LReg := gmap RegName LWord.
Definition LMem := gmap LAddr LWord.
Definition LDFrac := gmap LAddr iris.algebra.dfrac.dfrac.

Definition lreg_strip (lr : LReg) : Reg :=
 (fun lw : LWord => lword_get_word lw) <$> lr.
Definition is_cur_addr (la : LAddr) (cur_map : gmap Addr Version) : Prop :=
  cur_map !! la.1 = Some la.2. (* check whether the version of `la` matches in cur_map *)
Definition is_cur_word (lw : LWord) (cur_map : gmap Addr Version) : Prop :=
  match lw with
  | LCap _ b e _ v | LSealedCap _ _ b e _ v =>
      forall a, a ∈ finz.seq_between b e -> (cur_map !! a = Some v)
  | _ => True
  end.

Definition is_log_cap (lw : LWord) : bool :=
  match lw with
  | LCap _ _ _ _ _ => true
  | _ => false
  end.

Lemma is_log_cap_is_cap_true_iff lw : is_log_cap lw = true <-> is_cap (lword_get_word lw) = true.
Proof.
  split; intros
  ; destruct lw; cbn in *; try congruence
  ; destruct sb; cbn in *; try congruence.
Qed.

Lemma is_log_cap_is_cap_false_iff lw : is_log_cap lw = false <-> is_cap (lword_get_word lw) = false.
Proof.
  split; intros
  ; destruct lw; cbn in *; try congruence
  ; destruct sb; cbn in *; try congruence.
Qed.

Definition logical_region ( region : list Addr ) (v : Version) : list (Addr * Version) :=
  (fun a => (a,v)) <$> region.

(** The `reg_phys_log_corresponds` states that, the physical register file `phr` corresponds
    to the the logical register file `lr`, according to the view map `cur_map` if:
    - the content of the register `phr` is the same as the words in `lr` w/o the version
    - the version of the capabilities in `lr` are the same as the version of its addresses
      in the view map `cur_map`
 *)
Definition reg_phys_log_corresponds (phr : Reg) (lr : LReg) (cur_map : VMap) :=
    lreg_strip lr = phr
    ∧ map_Forall (λ _ lw, is_cur_word lw cur_map) lr.

(** The `mem_phys_log_corresponds` states that,
    - for each logical addresses in the logical memory,
      + the version is less or equal the current version of the address
      + the current version of the address also exists in the logical memory
    - for all entries in the view map,
      + it exists is a logical word `lw` in the logical memory `lm`
        ( i.e. dom(cur_map) ⊆ dom(lm) )
      + the logical word `lw` corresponds to the actual word in the physical memory `phm`
        for the same address
      + the logical word `lw` is the current view of the word
 *)
Definition mem_phys_log_corresponds (phm : Mem) (lm : LMem) (cur_map : VMap) :=
  map_Forall (λ la _ ,
      ∃ cur_v, is_cur_addr (laddr_get_addr la, cur_v) cur_map
               (* logical addr has version less or equal the current version *)
               ∧ laddr_get_version la <= cur_v
               (* current version of the address actually exists in the logical memory ? *)
               (* TODO is this last part is not necessary ? *)
               /\ is_Some ( lm !! (laddr_get_addr la, cur_v))
    ) lm
  ∧ map_Forall (λ a v, ∃ lw, lm !! (a,v) = Some lw
                             ∧ phm !! a = Some (lword_get_word lw)
                             ∧ is_cur_word lw cur_map)
      cur_map (* subset in other direction, and every current address is gc root *).

Definition state_phys_log_corresponds (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem) (cur_map : VMap):=
    reg_phys_log_corresponds phr lr cur_map ∧ mem_phys_log_corresponds phm lm cur_map.


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

Global Instance is_cur_addr_dec (la : LAddr) (cur_map : VMap) :
  Decision (is_cur_addr la cur_map).
Proof.
  rewrite /is_cur_addr.
  destruct (cur_map !! la.1) eqn:Heq ; rewrite Heq; solve_decision.
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

Lemma lreg_insert_respects_corresponds (phr : Reg) (lr : LReg) (cur_map : VMap) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr cur_map →
  is_cur_word lw cur_map →
  reg_phys_log_corresponds (<[r := lword_get_word lw]> phr) (<[r := lw]> lr) cur_map.
Proof.
  intros [Hstrip Hcur_regs] Hlw.
  split.
  - rewrite <- Hstrip.
    unfold lreg_strip.
    by rewrite fmap_insert.
  - apply map_Forall_insert_2; auto.
Qed.

Lemma lmem_insert_respects_corresponds (phm : Mem) (lm : LMem) (cur_map : VMap) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm cur_map →
  is_cur_addr la cur_map →
  is_cur_word lw cur_map →
  mem_phys_log_corresponds (<[laddr_get_addr la := lword_get_word lw]> phm) (<[la := lw]> lm) cur_map.
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
    + exists lw.
      split ; [ by simplify_map_eq|].
      split; auto; cbn ;by simplify_map_eq.
    + exists lw'.
      split; [rewrite lookup_insert_ne; auto ; intro; simplify_pair_eq|].
      split; by simplify_map_eq.
Qed.

Lemma lreg_read_iscur (phr : Reg) (lr : LReg) (cur_map : VMap) (r : RegName) (lw : LWord):
  reg_phys_log_corresponds phr lr cur_map →
  lr !! r = Some lw →
  is_cur_word lw cur_map.
Proof.
  intros [_ Hcur_regs] Hr.
  destruct_lword lw; try done; eapply map_Forall_lookup_1 in Hr; eauto; done.
Qed.

Lemma lmem_read_iscur (phm : Mem) (lm : LMem) (cur_map : VMap) (la : LAddr) (lw : LWord):
  mem_phys_log_corresponds phm lm cur_map →
  is_cur_addr la cur_map →
  lm !! la = Some lw →
  is_cur_word lw cur_map.
Proof.
  intros [Hdom Hroot] Hla Hlw.
  rewrite /is_cur_addr in Hla.
  eapply map_Forall_lookup_1 in Hla; eauto; cbn in Hla.
  destruct Hla as (lw' & Hlw' & Hphm & Hcur_lw').
  destruct la as [a v]; cbn in *.
  by rewrite Hlw in Hlw'; simplify_eq.
Qed.

Definition is_lword_version (lw : LWord) p b e a v : Prop :=
  (get_lcap lw) = Some (LSCap p b e a v).

Lemma is_lword_inv (lw : LWord) p b e a v :
  is_lword_version lw p b e a v ->
  (exists o, lw = LSealedCap o p b e a v)  \/ lw = LCap p b e a v.
Proof.
  intros Hversion.
  destruct_lword lw; cbn in Hversion ; try done
  ; rewrite /is_lword_version /= in Hversion; simplify_eq
  ; [right | left ; eexists]; done.
Qed.

Lemma cur_lword_cur_addr lw p b e a (v : Version) (cur_map : VMap):
  is_lword_version lw p b e a v ->
  is_cur_word lw cur_map →
  withinBounds b e a = true →
  is_cur_addr (a,v) cur_map.
Proof.
  intros Hlword Hcur_lw Hbounds.
  unfold is_cur_addr ; simpl.
  rewrite /is_cur_word /= in Hcur_lw.
  apply is_lword_inv in Hlword.
  destruct Hlword as [[o ?]| ?] ; subst
  ; apply withinBounds_true_iff, elem_of_finz_seq_between in Hbounds
  ; by apply Hcur_lw.
Qed.

Lemma state_phys_corresponds_reg lw (w : Word) r pr pm lr lm cur_map :
  lword_get_word lw = w ->
  state_phys_log_corresponds pr pm lr lm cur_map ->
  lr !! r = Some lw ->
  pr !! r = Some w.
Proof.
  intros * Hlword HLinv Hlr.
  destruct HLinv as [HregInv _]; simpl in *.
  destruct HregInv as [Hstrip _]; simpl in *.
  unfold lreg_strip in Hstrip.
  rewrite <- Hstrip.
  apply lookup_fmap_Some; eexists ; split ; eauto.
Qed.

Lemma state_phys_corresponds_mem
  (lw : LWord) (w : Word) (la : LAddr) (a : Addr)
  (pr : Reg) (pm : Mem) (lr : LReg) (lm : LMem) (cur_map : VMap) :
  lword_get_word lw = w ->
  laddr_get_addr la = a ->
  state_phys_log_corresponds pr pm lr lm cur_map ->
  lm !! la = Some lw ->
  is_cur_addr la cur_map ->
  pm !! a = Some w.
Proof.
  intros * Hlword Hladdr HLinv Hlr Hcur.
  destruct HLinv as [_ HmemInv]; simpl in *.
  destruct HmemInv as [Hdom Hroot]; simpl in *.
  eapply (map_Forall_lookup_1 _) in Hdom; last eapply Hlr.
  destruct Hdom as (cur_v & Hcur_addr & Hle_cur & Hsome).
  destruct la as [a' v']; cbn in * .
  rewrite /is_cur_addr /= in Hcur, Hcur_addr; simplify_eq.
  eapply map_Forall_lookup_1 in Hroot ; last eauto.
  destruct Hroot as (lw' & Hlm & Hpm & Hcurword).
  by rewrite Hlr in Hlm; simplify_map_eq.
Qed.

Lemma reg_corresponds_cap_cur_addr lcap p (b e a : Addr) la r (reg : Reg) lr cur_map :
  reg_phys_log_corresponds reg lr cur_map ->
  lword_get_word lcap = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lcap ->
  lword_get_version lcap = Some (laddr_get_version la) ->
  is_cur_addr la cur_map.
Proof.
  intros[_ Hcur] Hlcap Hla Hbounds Hr Hv; cbn in *.
  destruct lcap; cbn in *; try congruence.
  destruct sb; cbn in *; try congruence.
  simplify_eq.
  eapply map_Forall_lookup_1 in Hcur ; last eauto; clear Hr.
  cbn in *.
  destruct la as [a v]; cbn in *.
  apply Hcur; cbn.
  by apply withinBounds_in_seq.
Qed.

Lemma state_corresponds_cap_cur_addr
  lcap p (b e a : Addr) la r (reg : Reg) pm lr lm cur_map :
  state_phys_log_corresponds reg pm lr lm cur_map ->
  lword_get_word lcap = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some lcap ->
  lword_get_version lcap = Some (laddr_get_version la) ->
  is_cur_addr la cur_map.
Proof.
  intros [HinvReg _] Hlcap Hla Hbounds Hr Hv; cbn in *.
  eapply reg_corresponds_cap_cur_addr; eauto.
Qed.


Lemma reg_corresponds_cap_PC lcap p (b e a : Addr) la r (reg : Reg) lr cur_map :
  reg_phys_log_corresponds reg lr cur_map ->
  lword_get_word lcap = WCap p b e a ->
  laddr_get_addr la = a ->
  isCorrectPC (WCap p b e a) ->
  lr !! r = Some lcap ->
  lword_get_version lcap = Some (laddr_get_version la) ->
  is_cur_addr la cur_map.
Proof.
  intros HinvReg Hlcap Hla Hvpc Hr Hv; cbn in *.
  apply isCorrectPC_withinBounds in Hvpc.
  eapply reg_corresponds_cap_cur_addr ; eauto.
Qed.

Lemma state_phys_corresponds_mem_PC
  (p : Perm) (b e a : Addr) (v : Version) (r : RegName)
  (lw : LWord) (w : Word)
  (pr : Reg) (pm : Mem) (lr : LReg) (lm : LMem) (cur_map : VMap) :
  lword_get_word lw = w ->
  isCorrectPC (WCap p b e a) ->
  state_phys_log_corresponds pr pm lr lm cur_map ->
  lr !! r = Some (LCap p b e a v) ->
  lm !! (a,v) = Some lw ->
  pm !! a = Some w.
Proof.
  intros * Hlw Hvpc HLinv Hlr Hlm.
  eapply state_phys_corresponds_mem; eauto. by cbn.
  destruct HLinv as [ HinvReg _ ].
  eapply reg_corresponds_cap_PC; eauto. by cbn.
Qed.

Lemma reg_phys_log_get_word phr lr cur_map r lw:
  reg_phys_log_corresponds phr lr cur_map  ->
  lr !! r = Some lw ->
  phr !! r = Some (lword_get_word lw).
Proof.
  intros [<- Hcurreg] Hlr.
  unfold lreg_strip.
  apply lookup_fmap_Some. eexists; eauto.
Qed.

Lemma mem_phys_log_get_word phm lm cur_map a v lw:
  mem_phys_log_corresponds phm lm cur_map  ->
  lm !! (a, v) = Some lw ->
  is_cur_addr (a,v) cur_map ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [Hdom Hroot] Hlm Hcur.
  eapply map_Forall_lookup_1 in Hdom; eauto. cbn in Hdom.
  destruct Hdom as (cur_v & Hcur_addr & Hle_cur & Hsome).
  rewrite /is_cur_addr /= in Hcur, Hcur_addr; simplify_eq.
  eapply map_Forall_lookup_1 in Hroot; eauto.
  destruct Hroot as (lw' & Hlm' & Hpm' & Hcurword).
  by rewrite Hlm in Hlm'; simplify_map_eq.
Qed.

Lemma mem_phys_log_current_word phm lm cur_map a v lw:
  mem_phys_log_corresponds phm lm cur_map  ->
  lm !! (a, v) = Some lw ->
  is_cur_addr (a,v) cur_map ->
  is_cur_word lw cur_map.
Proof.
  intros [Hdom Hroot] Hlm Hcur.
  eapply map_Forall_lookup_1 in Hdom; eauto; cbn in Hdom.
  destruct Hdom as (cur_v & Hcur_addr & Hle_cur & Hsome).
  rewrite /is_cur_addr /= in Hcur, Hcur_addr; simplify_eq.
  eapply map_Forall_lookup_1 in Hroot; eauto.
  destruct Hroot as (lw' & Hlm' & Hpm' & Hcurword).
  by rewrite Hlm in Hlm'; simplify_map_eq.
Qed.


Lemma state_phys_log_reg_get_word phr mem lr lm cur_map r lw:
  state_phys_log_corresponds phr mem lr lm cur_map  ->
  lr !! r = Some lw ->
  phr !! r = Some (lword_get_word lw).
Proof.
  intros [Hreg _] ? ; eapply reg_phys_log_get_word ; eauto.
Qed.

Lemma state_phys_log_mem_get_word phr phm lr lm cur_map a v lw:
  state_phys_log_corresponds phr phm lr lm cur_map  ->
  lm !! (a, v) = Some lw ->
  is_cur_addr (a,v) cur_map ->
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [_ Hmem] ? ? ; eapply mem_phys_log_get_word ; eauto.
Qed.

Lemma state_phys_log_cap_all_current
  (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) (v : Version) :
  state_phys_log_corresponds phr phm lr lm cur_map ->
  lr !! src = Some (LCap p b e a v) ->
  Forall (λ a0 : Addr, cur_map !! a0 = Some v) (finz.seq_between b e).
Proof.
  move=> [[_ Hreg_current] Hmem_inv] Hlr_src.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hreg_current Hlr_src) as Hcur_src.
  cbn in *.
  by eapply Forall_forall.
Qed.

Definition lword_of_argument (lregs: LReg) (a: Z + RegName): option LWord :=
  match a with
  | inl n => Some (LInt n)
  | inr r => lregs !! r
  end.

Lemma version_addr_reg reg lr cur_map wr r p b e a la:
  reg_phys_log_corresponds reg lr cur_map ->
  lword_get_word wr = WCap p b e a ->
  laddr_get_addr la = a ->
  withinBounds b e a = true ->
  lr !! r = Some wr →
  is_cur_addr la cur_map ->
  lword_get_version wr = Some (laddr_get_version la).
Proof.
  intros [Hstrip Hcur_reg] Hlr Hla Hinbounds Hr Hcur_la.
  eapply map_Forall_lookup_1 in Hcur_reg; eauto.
  unfold is_cur_word in Hcur_reg.
  destruct_lword wr; simplify_eq ; cbn in Hlr; simplify_eq; cbn in *.
  apply withinBounds_in_seq in Hinbounds.
  apply Hcur_reg in Hinbounds.
  unfold is_cur_addr in Hcur_la.
  destruct la ; cbn in *; congruence.
Qed.

Lemma insert_reg_lreg_strip (lregs : LReg) (r : RegName) (lw : LWord) :
  lregs !! r = Some lw ->
  <[ r := lword_get_word lw ]> (lreg_strip lregs) = lreg_strip lregs.
Proof.
  intros Hr.
  rewrite -/lreg_strip -fmap_insert insert_id //.
Qed.

Lemma insert_cap_lreg_strip (lregs : LReg) (r : RegName)
  (p : Perm) (a b e : Addr) (v : Version) :
  lregs !! r = Some (LCap p b e a v) ->
  <[ r := WCap p b e a ]> (lreg_strip lregs) = lreg_strip lregs.
Proof.
  intros Hr.
  replace (WCap p b e a) with (lword_get_word (LCap p b e a v)) by done.
  rewrite -fmap_insert insert_id //=.
Qed.

Definition word_access_addr (a : Addr) (w : Word) : Prop :=
  match get_scap w with
  | Some (SCap _ b e _) => (b <= a < e)%a
  | _ => False
  end.

Definition word_access_addrL (a : Addr) (lw : LWord) : Prop :=
  word_access_addr a (lword_get_word lw).


Lemma update_cur_word (lw : LWord) (a : Addr) (v : Version)
  (lm : LMem) (cur_map: VMap) :
  ¬ word_access_addrL a lw ->
  is_cur_word lw cur_map ->
  is_cur_word lw ( <[a := v]> cur_map ).
Proof.
  intros Hnaccess Hcur.
  destruct_lword lw ; auto; cbn in *; intros * Ha1.
  all: assert (a1 <> a) by (apply elem_of_finz_seq_between in Ha1; solve_addr).
  all: apply Hcur in Ha1.
  all: by simplify_map_eq.
Qed.

Lemma is_cur_addr_insert_ne
  (a : Addr) (v : Version) (a' : Addr) (v' : Version)
  (cur_map : VMap) :
  is_cur_addr (a,v) cur_map ->
  a ≠ a' ->
  is_cur_addr (a,v) (<[a' := v']> cur_map).
Proof.
  intros Hcur Hneq.
  rewrite /is_cur_addr /=.
  rewrite /is_cur_addr /= in Hcur.
  by simplify_map_eq.
Qed.


(** Update version number of a memory region *)
(* For all the content of a logical memory `lm`,
   no current logical address has a lword that can access the address `a`.

   Put another way, the "current view" of the memory cannot access `a`.
 *)
Definition lmem_not_access_addrL (lm : LMem) (cur_map : VMap) (a : Addr) : Prop :=
  map_Forall
  (λ (la : LAddr) (lw : LWord),
    is_cur_addr la cur_map → (¬ word_access_addrL a lw)
  ) lm.

(* describes whether the region pointed by a lword is not reachable *)
Definition lmem_not_access_wordL (lm : LMem) (cur_map : VMap) (lw : LWord) :=
  (* is_cur_word lw cur_map → *)
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      Forall (fun a => lmem_not_access_addrL lm cur_map a) (finz.seq_between b e)
  | Some _ | None => True
  end.


(* Update the address version in lm, given the word. *)
Definition update_lmemory_lword (lm : LMem) (a : Addr) (v : Version) (lw : LWord)
  : LMem := <[ (a, v+1) := lw ]> lm.

Definition update_cur_version_addr_local (lm : LMem) (cur_map : VMap) (a : Addr)
  : LMem * VMap :=
  match cur_map !! a with
  | Some v =>
      match lm !! (a,v) with
      | Some lw => (update_lmemory_lword lm a v lw, <[ a := v+1 ]> cur_map)
      | None => (lm, cur_map)
      end
  | None => (lm, cur_map)
  end.

Definition update_cur_version_region_local
  (lm : LMem) (cur_map : VMap) (la : list Addr) : LMem * VMap :=
  foldr
    ( fun a (upd : LMem * VMap) =>
        let (lm', cur_map') := upd in
        update_cur_version_addr_local lm' cur_map' a)
    (lm, cur_map)
    la.

(* update the version number of the region pointed by a lword *)
Definition update_cur_version_word_region_local
  (lm : LMem) (cur_map : VMap) (lw : LWord) : LMem * VMap :=
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      update_cur_version_region_local lm cur_map (finz.seq_between b e)
  | Some _ | None => (lm, cur_map)
  end.

(* We assume that *lmem* is a local view compatible with the global view *lm*.
   We also assume that *lm* contains the laddress *(a,v)*,
   whereas *lmem* might not contain it.

   This way, the local view *lmem* can be updated,
   even if it does not contain the address (a,v)
 *)
Definition update_cur_version_addr_global (lmem lm : LMem) (cur_map : VMap) (a : Addr)
  : LMem * VMap :=
  match cur_map !! a with
  | Some v =>
      match lm !! (a,v) with
      | Some lw => (update_lmemory_lword lmem a v lw, <[ a := v+1 ]> cur_map)
      | None => (lmem, cur_map)
      end
  | None => (lmem, cur_map)
  end.

Definition update_cur_version_region_global
  (lmem lm : LMem) (cur_map : VMap) (la : list Addr) : LMem * VMap :=
  foldr
    ( fun a (upd : LMem * VMap) =>
        let (lmem', cur_map') := upd in
        update_cur_version_addr_global lmem' lm cur_map' a)
    (lmem, cur_map)
    la.

(* update the version number of the region pointed by a lword *)
Definition update_cur_version_word_region_global
  (lmem lm : LMem) (cur_map : VMap) (lw : LWord) : LMem * VMap :=
  match get_lcap lw with
  | Some (LSCap p b e a v) =>
      update_cur_version_region_global lmem lm cur_map (finz.seq_between b e)
  | Some _ | None => (lm, cur_map)
  end.

Definition update_cur_version_region_local_cons
  (lm lm' : LMem) (cur_map cur_map' : VMap) (a : Addr) (la : list Addr) :
  update_cur_version_region_local lm cur_map (a :: la) = (lm', cur_map') ->
  exists (lm0 : LMem) (cur_map0 : VMap),
    update_cur_version_region_local lm cur_map la = (lm0, cur_map0)
    ∧ update_cur_version_addr_local lm0 cur_map0 a = (lm', cur_map').
Proof.
  intros Hupd.
  cbn in Hupd.
  rewrite -/(update_cur_version_region_local lm cur_map la) in Hupd.
  destruct (update_cur_version_region_local lm cur_map la) as [lm0 cur_map0] eqn:Hupd0.
  exists lm0, cur_map0.
  split ; eauto.
Qed.

Definition update_cur_version_region_global_cons
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



(* TODO find better lemma name *)
(* If an address `a'` is not reachable from the current view of the lmem,
   then updating the version number of another address `a`
   does not make it reachable *)
Lemma update_cur_version_addr_local_preserves_no_access :
  ∀ (a a' : Addr) (lm lm' : LMem) (cur_map cur_map' : VMap),
    a ≠ a' →
    update_cur_version_addr_local lm cur_map a' = (lm', cur_map') →
    lmem_not_access_addrL lm cur_map a →
    lmem_not_access_addrL lm' cur_map' a.
Proof.
  intros * Hneq Hupd Hno_access.
  rewrite /update_cur_version_addr_local /update_lmemory_lword in Hupd.
  destruct (cur_map !! a') as [va'|] eqn:Heqn ; cbn in Hupd ; [|by simplify_eq].
  destruct (lm !! (a', va')) as [lw'|] eqn:Heqn'; simplify_map_eq; last done.

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
Lemma update_cur_version_region_local_preserves_no_access :
  ∀ (la : list Addr) (a : Addr) (lm lm': LMem) (cur_map cur_map' : VMap),
    a ∉ la →
    update_cur_version_region_local lm cur_map la = (lm', cur_map') →
    lmem_not_access_addrL lm cur_map a →
    lmem_not_access_addrL lm' cur_map' a.
Proof.
  induction la as [| a la IH].
  - by intros; cbn in * ; simplify_eq.
  - intros * Hnot_in Hupd Hno_access.
    apply not_elem_of_cons in Hnot_in; destruct Hnot_in as [Hneq Hnot_in].
    cbn in *.
    rewrite -/(update_cur_version_region_local lm cur_map la) in Hupd.
    destruct (update_cur_version_region_local lm cur_map la)
      as [lm0 cur_map0] eqn:Hupd_rec.
    eapply update_cur_version_addr_local_preserves_no_access ; eauto.
Qed.

(* If the address `a` is not reachable
   from the current view of the lmem,
   then the mem_phys_log invariant still holds
   after updating its version number. *)
Lemma update_cur_version_addr_local_preserves_mem_phyc_cor
  (phm : Mem) (lm lm': LMem) (cur_map cur_map' : VMap) (a : Addr) :
  update_cur_version_addr_local lm cur_map a = (lm', cur_map') →
  lmem_not_access_addrL lm cur_map a →
  mem_phys_log_corresponds phm lm cur_map ->
  mem_phys_log_corresponds phm lm' cur_map'.
Proof.
  intros Hupd Hnaccess_mem [Hdom Hroot].
  rewrite /update_cur_version_addr_local /update_lmemory_lword in Hupd.
  destruct (cur_map !! a) as [v |] eqn:Hcur_la; cbn in * ; simplify_eq; last done.
  destruct (lm !! (a,v)) as [lw |] eqn:Hla; cbn in * ; simplify_eq; last done.
  rewrite -/(is_cur_addr (a,v) cur_map) in Hcur_la.

  assert (not (word_access_addrL a lw)) as Hnaccess by eauto.

  pose proof (Hla' := Hla).
  eapply map_Forall_lookup_1 in Hla'; eauto; cbn in Hla'.
  destruct Hla' as (va & Hcur_va & Hle_va & [lwa Hlwa]).
  rewrite /is_cur_addr /= in Hcur_la, Hcur_va.
  rewrite Hcur_la in Hcur_va ; simplify_eq.

  split.
  - eapply lmem_read_iscur in Hla ; eauto.
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
      by simplify_map_eq.
    + exists lw'.
      assert ((a, va + 1) ≠ (a', v')) by (intro ; simplify_eq).
      split ; [|split] ; try by simplify_map_eq.
      eapply update_cur_word;eauto.
Qed.

(* Same as `update_cur_version_addr_preserves_mem_phyc_cor`,
   but for a list of addresses *)
Lemma update_cur_version_region_local_preserves_mem_phyc_cor:
  ∀ (la : list Addr) (phm : Mem) (lm lm': LMem) (cur_map cur_map' : VMap),
    NoDup la →
    update_cur_version_region_local lm cur_map la = (lm', cur_map') →
    Forall (fun a => lmem_not_access_addrL lm cur_map a) la →
    mem_phys_log_corresponds phm lm cur_map ->
    mem_phys_log_corresponds phm lm' cur_map'.
Proof.
  induction la as [| a la IH].
  - by intros; cbn in * ; simplify_eq.
  - intros * Hno_dup Hupd Hall_naccess_mem Hmem_phys_log_corr.
    rewrite /update_cur_version_region_local in Hupd.
    rewrite foldr_cons in Hupd.
    rewrite -/(update_cur_version_region_local lm cur_map _) in Hupd.
    destruct (update_cur_version_region_local lm cur_map la) as [lm0 cur_map0] eqn:Hupd'.

    apply Forall_cons in Hall_naccess_mem as [Hnacces_mem Hall_naccess_mem].
    apply NoDup_cons in Hno_dup ; destruct Hno_dup as [Hnotin Hno_dup].

    assert (mem_phys_log_corresponds phm lm0 cur_map0) as Hinv0.
      by (eapply IH ;eauto).

    eapply update_cur_version_addr_local_preserves_mem_phyc_cor in Hupd ; eauto.
    by eapply update_cur_version_region_local_preserves_no_access.
Qed.


(* update the version number of a memory region that is not reacheable,
   preserves the mem_phys_log invariant *)
Lemma update_cur_version_word_region_local_preserves_mem_phyc_cor
  (phm : Mem) (lm lm': LMem) (cur_map cur_map' : VMap) (lw : LWord) :
  lmem_not_access_wordL lm cur_map lw →
  update_cur_version_word_region_local lm cur_map lw = (lm', cur_map') →
  mem_phys_log_corresponds phm lm cur_map ->
  mem_phys_log_corresponds phm lm' cur_map'.
Proof.
  intros Hno_access Hupd Hmem_phys_log.
  rewrite /update_cur_version_word_region_local in Hupd.
  rewrite /lmem_not_access_wordL in Hno_access.
  destruct (get_lcap lw) as [[] |] ; simplify_eq ; auto.
  eapply update_cur_version_region_local_preserves_mem_phyc_cor ; eauto.
  apply finz_seq_between_NoDup.
Qed.

(* TODO duplicate *)
(* Lemma update_cur_version_region_local_notin_preserves_cur_map *)
(*   (lmem lmem': LMem) (cur_map cur_map': VMap) (la : list Addr) (a : Addr) (v : Version): *)
(*     a ∉ la -> *)
(*     cur_map !! a = Some v -> *)
(*     update_cur_version_region_local lmem cur_map la = (lmem', cur_map') -> *)
(*     cur_map' !! a = Some v. *)
(* Proof. *)
(*   move: lmem lmem' cur_map cur_map' a v. *)
(*   induction la as [|a la] ; intros * Hnot_in Hcur_a Hupd. *)
(*   - by cbn in Hupd; simplify_eq. *)
(*   - apply not_elem_of_cons in Hnot_in. destruct Hnot_in as [Ha0_neq_a Hnot_in]. *)
(*     cbn in Hupd. *)
(*     rewrite -/(update_cur_version_region_local lmem cur_map la) in Hupd. *)
(*     destruct (update_cur_version_region_local lmem cur_map la) as [lmem0 cur_map0] eqn:Hupd0. *)
(*     rewrite /update_cur_version_addr_local in Hupd. *)
(*     destruct (cur_map0 !! a) as [va|] eqn:Hva. *)
(*     2: { simplify_eq; eapply IHla; eauto. } *)
(*     destruct (lmem0 !! (a,va)) as [lw|] eqn:Hlw. *)
(*     2: { simplify_eq; eapply IHla; eauto. } *)
(*     by simplify_map_eq. *)
(* Qed. *)


Lemma update_cur_version_region_local_preserves_lmem
  (lmem lmem': LMem) (cur_map cur_map' : VMap)
  (la : list Addr) (v : Version):
  NoDup la ->
  Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) la ->
  Forall (λ a : Addr, cur_map !! a = Some v) la ->
  update_cur_version_region_local lmem cur_map la = (lmem', cur_map') ->
  Forall (λ a : Addr, is_Some (lmem' !! (a, v))) la.
Proof.
Abort.

Lemma update_cur_version_region_local_preserves_vmap
  (lmem lmem': LMem) (cur_map cur_map' : VMap)
  (la : list Addr) (v : Version):
  NoDup la ->
  Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) la ->
  Forall (λ a : Addr, cur_map !! a = Some v) la ->
  update_cur_version_region_local lmem cur_map la = (lmem', cur_map') ->
  Forall (λ a : Addr, is_Some (cur_map' !! a)) la.
Proof.
Abort.

Lemma update_cur_version_region_mono
  (lm lmem lmem': LMem) (cur_map cur_map' : VMap)
  (la : list Addr) (v : Version):
  lmem ⊆ lm ->
  NoDup la ->
  Forall (λ a : Addr, ∃ lw, lmem !! (a, v) = Some lw) la ->
  Forall (λ a : Addr, cur_map !! a = Some v) la ->
  update_cur_version_region_local lmem cur_map la = (lmem', cur_map') ->
  exists lm',
    update_cur_version_region_local lm cur_map la = (lm', cur_map')
    /\ lmem' ⊆ lm'.
Proof.
  move: lm lmem lmem' cur_map cur_map' v.
  induction la as [| a la ]
  ; intros * Hsubset_lmem HNoDup HmemMap HcurMap Hupd_lmem.
  - exists lm. by cbn in * ; simplify_eq.
  - apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup].
    apply Forall_cons in HmemMap ; destruct HmemMap as [[lw Ha] HmemMap].
    apply Forall_cons in HcurMap ; destruct HcurMap as [Hcur HcurMap].
    rewrite /update_cur_version_region_local //= in Hupd_lmem.
    rewrite -/(update_cur_version_region_local lmem cur_map la) in Hupd_lmem.
    destruct (update_cur_version_region_local lmem cur_map la) as [lmem0 cur_map0] eqn:Hupd_lm0.

    (* apply bind_Some in Hupd_lmem. *)
    (* destruct Hupd_lmem as ( [lmem0 cur_map0] & Hupd_lmem & Hupd_lmem0 ). *)
    eapply IHla in Hupd_lm0; eauto.
    destruct Hupd_lm0 as [lm' [Hupd_lm' Hsubset_lm']].
    pose proof Hupd_lmem as Hupd_lmem'.
    rewrite /update_cur_version_addr_local in Hupd_lmem'.
    destruct (cur_map0 !! a) as [va|] eqn:Hva.
    2: { simplify_eq.
         (* eapply update_cur_version_region_local_preserves_vmap in Hupd_lm'; eauto. *)
         admit. (* TODO easy, Hupd_lm' + Hva *)
         (* admit. (* TODO by Hsubset_lm, should be easy -> lemma *) *)
    }
    destruct (lmem0 !! (a,va)) as [lw0|] eqn:Hlw.
    2: { simplify_eq.
         (* eapply update_cur_version_region_local_preserves_lmem in Hupd_lm'; eauto. *)
         admit. (* TODO easy, Hupd_lm' + Hlw *)
         (* admit. (* TODO by Hsubset_lm, should be easy -> lemma *) *)
    }
    simplify_eq.

    (* apply bind_Some in Hupd_lmem0. *)
    (* destruct Hupd_lmem0 as (va & Hva & Hupd_lmem0). *)
    (* apply bind_Some in Hupd_lmem0. *)
    (* destruct Hupd_lmem0 as (lmem0' & Hupd_lmem0' & Hlmem0'). *)
    (* apply bind_Some in Hupd_lmem0'. *)
    (* destruct Hupd_lmem0' as (lw0 & Hlw0 & ?). *)
    (* simplify_eq. *)
    pose proof Hupd_lm' as Hupd_lm''.
    eapply IHla in Hupd_lm'; eauto.
    2: admit. (* TODO by Hsubset_lm, should be easy -> lemma *)
    destruct Hupd_lm' as (lm'0 & Hupd_lm'0 & Hsubset_lm'0).
    rewrite Hupd_lm'0 in Hupd_lm''; simplify_eq.
    exists (<[(a, va+1) := lw0 ]> lm').


    (* split. *)
    (* admit. *)
    (* apply insert_mono; auto. *)
    (* { cbn. *)
    (*   (* rewrite -/(update_cur_version_region lm cur_map la). *) *)
    (*   (* rewrite Hupd_lm'. *) *)

    (*   (* auto. *) *)
    (*   (* apply bind_Some. *) *)
    (*   (* exists (lm', cur_map0) ; split ; auto. *) *)

    (*   (* apply bind_Some; exists va ; split ; auto. *) *)
    (*   (* apply bind_Some; exists (<[(a, va + 1):=lw0]> lm') ; split ; auto. *) *)
    (*   (* apply bind_Some; exists lw0 ; split ; auto. *) *)
    (*   eapply map_subseteq_spec; eauto. *)
    (*   intros. *)
    (*   destruct i. destruct (decide (f = a)); simplify_eq. *)
    (*   admit. *)
    (* } *)
    (* apply insert_mono; auto. *)
(* Qed. *)
Abort.

Lemma update_cur_version_addr_local_preserves_content_lmem
  (lmem lmem' : LMem) (vmap vmap' : VMap)
  (a a': Addr) (v :Version) (opt_lw : option LWord):
  a ≠ a' ->
  update_cur_version_addr_local lmem vmap a' = (lmem', vmap') ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  intros Ha_notint_la Hupd Hlmem.
  rewrite /update_cur_version_addr_local in Hupd.
  destruct (vmap !! a') as [va'|] eqn:Hva' ; last (simplify_eq; eauto).
  destruct (lmem !! (a',va')) as [lw'|] eqn:Hlw' ; last (simplify_eq; eauto).
  simplify_eq.
  rewrite /update_lmemory_lword.
  by rewrite lookup_insert_ne ; last (intro ; simplify_pair_eq).
Qed.

Lemma update_cur_version_region_local_preserves_content_lmem
  (lmem lmem' : LMem) (cur_map cur_map' : VMap) (la : list Addr)
  (a : Addr) (v :Version) (opt_lw : option LWord):
  a ∉ la ->
  update_cur_version_region_local lmem cur_map la = (lmem', cur_map') ->
  lmem !! (a, v) = opt_lw ->
  lmem' !! (a, v) = opt_lw.
Proof.
  move: lmem lmem' cur_map cur_map' a v opt_lw.
  induction la as [| a' la Hla]
  ; intros * Ha_notin_la Hupd Hlmem
  ; first (by cbn in *; simplify_eq).

  apply not_elem_of_cons in Ha_notin_la. destruct Ha_notin_la as [Ha_neq_a' Ha_notin_la].
  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lmem0 & vmap0 & Hupd & Hupd0).

  eapply update_cur_version_addr_local_preserves_content_lmem; [eauto | eauto | ].
  eapply Hla; eauto.
Qed.

Lemma update_cur_version_addr_local_notin_preserves_cur_1:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) v,
  update_cur_version_addr_local lm cur_map a' = (lm', cur_map')
  → a ≠ a' → is_cur_addr (a, v) cur_map → is_cur_addr (a, v) cur_map'.
Proof.
  move=> lm lm' cur_map cur_map' a a' v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_local /update_lmemory_lword in Hupd.
  destruct (cur_map !! a') as [va'|]; cbn in *; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; last by simplify_eq.
  rewrite /is_cur_addr /= lookup_insert_ne //=.
Qed.

Lemma update_cur_version_addr_local_notin_preserves_cur_2:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) v,
  update_cur_version_addr_local lm cur_map a' = (lm', cur_map')
  → a ≠ a' → is_cur_addr (a, v) cur_map' → is_cur_addr (a, v) cur_map.
Proof.
  move=> lm lm' cur_map cur_map' a a' v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_local /update_lmemory_lword in Hupd.
  destruct (cur_map !! a') as [va'|]; cbn in *; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; last by simplify_eq.
  rewrite /is_cur_addr /= lookup_insert_ne //= in Hcur.
Qed.

Lemma update_cur_version_addr_local_notin_preserves_cur:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) v,
  update_cur_version_addr_local lm cur_map a' = (lm', cur_map')
  → a ≠ a'
  → (is_cur_addr (a, v) cur_map <-> is_cur_addr (a, v) cur_map').
Proof.
  intros; split ; intros
  ; [ eapply update_cur_version_addr_local_notin_preserves_cur_1
    | eapply update_cur_version_addr_local_notin_preserves_cur_2]
  ; eauto.
Qed.

Lemma update_cur_version_region_local_notin_preserves_cur_1:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (a : Addr) v,
  update_cur_version_region_local lm cur_map la = (lm', cur_map')
  → a ∉ la → is_cur_addr (a, v) cur_map → is_cur_addr (a, v) cur_map'.
Proof.
  move=> lm lm' cur_map cur_map' la.
  move: lm lm' cur_map cur_map'.
  induction la as [|a la IH]
  ; intros * ; move=> Hupd Ha_notin_la Hcur
  ; first (cbn in *; by simplify_eq).

  apply not_elem_of_cons in Ha_notin_la.
  destruct Ha_notin_la as [Ha0_neq_a Ha_notin_la].

  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
  eapply update_cur_version_addr_local_notin_preserves_cur_1; eauto.
Qed.

Lemma update_cur_version_region_local_notin_preserves_cur_2:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (a : Addr) v,
  update_cur_version_region_local lm cur_map la = (lm', cur_map')
  → a ∉ la → is_cur_addr (a, v) cur_map' → is_cur_addr (a, v) cur_map.
Proof.
  move=> lm lm' cur_map cur_map' la.
  move: lm lm' cur_map cur_map'.
  induction la as [|a la IH]
  ; intros * ; move=> Hupd Ha_notin_la Hcur
  ; first (cbn in *; by simplify_eq).

  apply not_elem_of_cons in Ha_notin_la.
  destruct Ha_notin_la as [Ha0_neq_a Ha_notin_la].

  apply update_cur_version_region_local_cons in Hupd
  ; destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).
  eapply IH; eauto.
  eapply update_cur_version_addr_local_notin_preserves_cur_2; eauto.
Qed.

Lemma update_cur_version_region_local_notin_preserves_cur:
  ∀ (lm lm' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (a : Addr) v,
  update_cur_version_region_local lm cur_map la = (lm', cur_map')
  → a ∉ la
  → (is_cur_addr (a, v) cur_map <-> is_cur_addr (a, v) cur_map').
Proof.
  intros; split ; intros
  ; [ eapply update_cur_version_region_local_notin_preserves_cur_1
    | eapply update_cur_version_region_local_notin_preserves_cur_2]
  ; eauto.
Qed.

Lemma update_cur_version_addr_global_notin_preserves_cur_1:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) v,
  update_cur_version_addr_global lmem lm cur_map a' = (lmem', cur_map')
  → a ≠ a' → is_cur_addr (a, v) cur_map → is_cur_addr (a, v) cur_map'.
Proof.
  move=> lmem lm lmem' cur_map cur_map' a a' v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_global /update_lmemory_lword in Hupd.
  destruct (cur_map !! a') as [va'|]; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; last by simplify_eq.
  rewrite /is_cur_addr /= lookup_insert_ne //=.
Qed.

Lemma update_cur_version_addr_global_notin_preserves_cur_2:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (a a' : Addr) v,
  update_cur_version_addr_global lmem lm cur_map a' = (lmem', cur_map')
  → a ≠ a' → is_cur_addr (a, v) cur_map' → is_cur_addr (a, v) cur_map.
Proof.
  move=> lmem lm lmem' cur_map cur_map' a a' v Hupd Hneq Hcur.
  rewrite /update_cur_version_addr_global /update_lmemory_lword in Hupd.
  destruct (cur_map !! a') as [va'|]; last by simplify_eq.
  destruct (lm !! (a', va')) as [lwa' |]eqn:Heq ; simplify_map_eq; last by simplify_eq.
  rewrite /is_cur_addr /= lookup_insert_ne //= in Hcur.
Qed.

Lemma update_cur_version_region_global_notin_preserves_cur_1:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (a : Addr) v,
  update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map')
  → a ∉ la → is_cur_addr (a, v) cur_map → is_cur_addr (a, v) cur_map'.
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
  assert (is_cur_addr (a0, v) vmap_m0) as Hcur0 by (eapply IH ; eauto).
  eapply update_cur_version_addr_global_notin_preserves_cur_1 in Hcur0; eauto.
Qed.

Lemma update_cur_version_region_global_notin_preserves_cur_2:
  ∀ (lmem lm lmem' : LMem) (cur_map cur_map' : VMap) (la : list Addr) (a : Addr) v,
  update_cur_version_region_global lmem lm cur_map la = (lmem', cur_map')
  → a ∉ la → is_cur_addr (a, v) cur_map' → is_cur_addr (a, v) cur_map.
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

(** Sweep in logical memory *)
Definition overlap_wordL (lw1 lw2 : LWord) : Prop :=
  (overlap_word (lword_get_word lw1) (lword_get_word lw2)).

Global Instance overlap_wordL_dec (lw1 lw2 : LWord) : Decision (overlap_wordL lw1 lw2).
Proof. solve_decision. Defined.

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

Definition is_last_version_addr (lmem : LMem) (la : LAddr) : Prop :=
  let v := laddr_get_version la in
  map_Forall
    ( fun (la' : LAddr) (_ : LWord) =>
        (laddr_get_addr la' = laddr_get_addr la) -> laddr_get_version la' <=  v)
    lmem.

Lemma mem_phys_log_cur_addr_last_version_1
  (phm : Mem) (lm : LMem) (cur_map : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm cur_map →
  is_cur_addr la cur_map ->
  is_last_version_addr lm la.
Proof.
  move: la => [a v] [Hdom Hroot] Hcur_la.
  eapply map_Forall_lookup_2.
  move=> [a' v'] lw' Hla' /= ? ; simplify_eq.
  eapply map_Forall_lookup in Hla'; eauto.
  cbn in Hla'.
  destruct Hla' as (v_la' & Hcur_la' & Hcur_v_la' & Hla').
  by eapply is_cur_addr_same in Hcur_la'; [|eapply Hcur_la]; simplify_eq.
Qed.

Lemma mem_phys_log_cur_addr_last_version_2
  (phm : Mem) (lm : LMem) (cur_map : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm cur_map →
  is_Some (lm !! la) ->
  is_last_version_addr lm la ->
  is_cur_addr la cur_map.
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

Lemma mem_phys_log_cur_addr_last_version
  (phm : Mem) (lm : LMem) (cur_map : VMap) (la : LAddr) :
  mem_phys_log_corresponds phm lm cur_map →
  is_Some (lm !! la) ->
  (is_last_version_addr lm la <-> is_cur_addr la cur_map).
Proof.
  move=> HLinv Hla.
  by split ; intro
  ; [ eapply mem_phys_log_cur_addr_last_version_2
    | eapply mem_phys_log_cur_addr_last_version_1 ].
Qed.

Lemma state_phys_log_last_version
  (phr : Reg) (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) (v : Version) :
  state_phys_log_corresponds phr phm lr lm cur_map ->
  lr !! src = Some (LCap p b e a v) ->
  Forall (λ a0 : Addr, lm !! (a0, v+1) = None) (finz.seq_between b e).
Proof.
  move=> [[_ Hreg_current] Hmem_inv] Hlr_src.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hreg_current Hlr_src) as Hcur_src.
  cbn in *.
  apply Forall_forall.
  intros a0 Ha0_inbounds.
  apply Hcur_src in Ha0_inbounds.
  assert (is_cur_addr (a0, v) cur_map) as Hcur_a0 by done.

  destruct (lm !! (a0, v + 1)) eqn:Hv'. 2: done.
  destruct Hmem_inv as [Hroot Hcur].
  eapply map_Forall_lookup_1 in Hroot; eauto.
  destruct Hroot as (cur_v & Hcur_v & cur & Hsome & Hmaxv).
  cbn in *.

  eapply map_Forall_lookup_1 in Hcur; eauto.
  destruct Hcur as (lw & Hlm & _) ; cbn in *.
  eapply is_cur_addr_same in Hcur_a0; eauto; simplify_eq.
  lia.
Qed.

(* Returns [true] if [r] is unique. *)
Definition unique_in_memoryL (lmem : LMem) (lwsrc : LWord) : Prop :=
  (map_Forall
     (λ (la : LAddr) (lwa : LWord),
       is_last_version_addr lmem la -> ¬ overlap_wordL lwsrc lwa)
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

Definition unique_in_memoryL_aux (lmem : LMem) (lwsrc : LWord) (cur_map : VMap) : Prop :=
  (map_Forall
     (λ (la : LAddr) (lwa : LWord),
       is_cur_addr la cur_map -> ¬ overlap_wordL lwsrc lwa)
     lmem).

Lemma unique_in_memoryL_equiv
  (phm : Mem) (phr : Reg) (lm : LMem) (lr : LReg)
  (src : RegName) (lwsrc : LWord) (cur_map : VMap) :

  lr !! src = Some lwsrc →
  state_phys_log_corresponds phr phm lr lm cur_map →
  unique_in_memory phm (lword_get_word lwsrc) ->
  unique_in_memoryL lm lwsrc ->
  unique_in_memoryL_aux lm lwsrc cur_map.
Proof.
  move=> Hsrc [_ Hmem_inv] Hsweep HsweepL.
  rewrite /unique_in_memoryL_aux.
  rewrite /unique_in_memory in Hsweep.
  rewrite /unique_in_memoryL in HsweepL.
  eapply map_Forall_impl; first eapply HsweepL.
  move=> la lw /= His_last Hcur_la.
  apply: His_last.
  eapply mem_phys_log_cur_addr_last_version_1; eauto.
Qed.

Lemma is_cur_word_lea
  (cur_map : VMap)
  (p : Perm) (b e a a' : Addr) (v : Version):
  is_cur_word (LCap p b e a v) cur_map ->
  is_cur_word (LCap p b e a' v) cur_map.
Proof.
  move=> Hcur a0 Ha0.
  by apply Hcur.
Qed.

Lemma update_cur_version_region_local_in_updates_cur_map
  (lm lm' : LMem) (cur_map cur_map' : VMap)
  (la : list Addr) ( a : Addr) (v : Version):
  NoDup la ->
  update_cur_version_region_local lm cur_map la = (lm', cur_map') ->
  a ∈ la ->
  is_Some (lm !! (a,v)) ->
  is_cur_addr (a, v) cur_map ->
  is_cur_addr (a, v+1) cur_map'.
Proof.
  move: lm lm' cur_map cur_map' a v.
  induction la as [|a' la' IH] ; intros * HNoDup Hupd Ha [lwa Hlwa] Hcur_a.
  - by apply elem_of_nil in Ha.
  - apply NoDup_cons in HNoDup.
    destruct HNoDup as [ Ha'_not_in_la' HNoDup ].
    apply elem_of_cons in Ha.

    apply update_cur_version_region_local_cons in Hupd.
    destruct Hupd as (lm0 & vmap_m0 & Hupd & Hupd0).

    destruct Ha as [? | Ha] ; simplify_eq.
    + (* case (a = a' *)
      eapply update_cur_version_region_local_preserves_content_lmem in Hlwa
      ; eauto ; cbn in *.
      eapply update_cur_version_region_local_notin_preserves_cur_1 in Hupd
      ; eauto ; cbn in *.
      rewrite /update_cur_version_addr_local in Hupd0.
      rewrite Hupd /= in Hupd0.
      rewrite /is_cur_addr.
      by rewrite Hlwa in Hupd0 ; simplify_map_eq.
    + (* case (a <> a' *)
      assert (a <> a') as Ha_neq_a' by set_solver.
      eapply update_cur_version_addr_local_notin_preserves_cur_1
      ; eauto ; cbn in *.
Qed.

Lemma reg_phys_log_corresponds_cap_is_cur
  (phr : Reg) (lr : LReg) (cur_map : VMap)
  (src : RegName) (p : Perm)  (b e a a' : Addr) (v : Version) :
  lr !! src = Some (LCap p b e a v) ->
  reg_phys_log_corresponds phr lr cur_map  ->
  a' ∈ finz.seq_between b e ->
  is_cur_addr (a', v) cur_map.
Proof.
  move=> Hlr_src Hreg_inv Ha'.
  eapply lreg_read_iscur in Hlr_src; eauto.
  apply is_cur_word_lea with (a' := a') in Hlr_src.
  eapply cur_lword_cur_addr; eauto.
  rewrite /is_lword_version //=.
  apply elem_of_finz_seq_between in Ha'.
  apply withinBounds_true_iff.
  solve_addr.
Qed.

Lemma not_overlap_wordL_seq_between
  (p p' : Perm) (b b' e e' a a' : Addr) (v v' : Version) :
  ¬ overlap_wordL (LCap p b e a v) (LCap p' b' e' a' v') ->
  a ∈ finz.seq_between b' e' ->
  a ∉ finz.seq_between b e.
Proof.
  move=> Hnot_overlap Ha_in Ha_in'.
  apply Hnot_overlap.
  rewrite /overlap_wordL /= /overlap_word /=.
  apply elem_of_finz_seq_between in Ha_in, Ha_in'.
  destruct (b <? b')%a eqn:Hb; solve_addr.
Qed.

Lemma update_cur_version_local_notin_is_cur_word
  (lm lm' : LMem) (cur_map cur_map' : VMap)
  (p : Perm) (b e a : Addr) (v : Version)
  (lw : LWord)
  :
  update_cur_version_region_local lm cur_map (finz.seq_between b e) = (lm', cur_map') ->
  ¬ overlap_wordL (LCap p b e a v) lw ->
  is_cur_word lw cur_map ->
  is_cur_word lw cur_map'.
Proof.
  move=> Hupd Hno_overlap His_cur_lw.
  destruct lw ; cbn; first done.
  - destruct sb as [ p' b' e' a' v'|] ; last done.
    move=> a'0 Ha'0.
    cbn in His_cur_lw.
    pose proof (His_cur_lw a'0 Ha'0) as Ha'0_cur.
    eapply update_cur_version_region_local_notin_preserves_cur_1 ; eauto.
    eapply not_overlap_wordL_seq_between ; [eapply Hno_overlap| eapply Ha'0].
  - destruct l as [ p' b' e' a' v'|] ; last done.
    move=> a'0 Ha'0.
    cbn in His_cur_lw.
    pose proof (His_cur_lw a'0 Ha'0) as Ha'0_cur.
    eapply update_cur_version_region_local_notin_preserves_cur_1 ; eauto.
    eapply not_overlap_wordL_seq_between ; [eapply Hno_overlap| eapply Ha'0].
  Unshelve. all: auto.
Qed.

Definition update_version_lword (lw : LWord ) : LWord :=
  match lw with
  | LCap p b e a v => LCap p b e a (v+1)
  | LSealedCap ot p b e a v => LSealedCap ot p b e a (v+1)
  | _ => lw
  end.

Lemma update_cur_version_word_region_local_update_lword
  (lm lm' : LMem) (cur_map cur_map' : VMap) (lw : LWord) :
  update_cur_version_word_region_local lm cur_map lw = (lm', cur_map') ->
  (* TODO ugly *)
  (
    match lw with
    | LCap _ b e a v
    | LSealedCap _ _ b e a v =>
        Forall (fun a => is_Some (lm !! (a,v)) ) (finz.seq_between b e)
    | _ => True
    end
  ) ->
  is_cur_word lw cur_map ->
  is_cur_word (update_version_lword lw) cur_map'.
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

Lemma update_cur_version_region_local_update_lcap
  (lm lm' : LMem) (cur_map cur_map' : VMap)
  (p : Perm) (b e a : Addr) (v : Version) :
  update_cur_version_region_local lm cur_map (finz.seq_between b e) = (lm', cur_map') ->
  Forall (fun a => is_Some (lm !! (a,v))) (finz.seq_between b e) ->
  is_cur_word (LCap p b e a v) cur_map ->
  is_cur_word (LCap p b e a (v + 1)) cur_map'.
Proof.
  move=> Hupd Hcur.
  rewrite -/(update_version_lword (LCap p b e a v)).
  eapply update_cur_version_word_region_local_update_lword; cbn ; eauto.
Qed.

Lemma update_cur_version_reg_phys_log_cor_updates_src
  (phr : Reg) (phm : Mem) (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) (lw : LWord) :
  is_cur_word lw cur_map' ->
  state_phys_log_corresponds phr phm lr lm cur_map ->
  lr !! src = Some (LCap p b e a v) ->
  unique_in_machineL lm lr src (LCap p b e a v) ->
  update_cur_version_region_local lm cur_map (finz.seq_between b e)
  = (lm', cur_map') ->
  reg_phys_log_corresponds (<[src:= (lword_get_word lw)]> phr) (<[src:= lw]> lr) cur_map'.
Proof.
  move=> Hcur_lw [Hreg_inv Hmem_inv] Hlr_src Hunique Hupd.
  split.
  - rewrite /lreg_strip fmap_insert /= -/(lreg_strip lr).
    by replace phr with (lreg_strip lr) by (by destruct Hreg_inv as [? _]).
  - rewrite -insert_delete_insert.
    eapply lreg_insert_respects_corresponds with (phr := (delete src phr)).
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

Lemma reg_phys_log_corresponds_delete
  (phr : Reg) (lr : LReg) (cur_map : VMap) (src : RegName) :
  reg_phys_log_corresponds phr lr cur_map ->
  reg_phys_log_corresponds (delete src phr) (delete src lr) cur_map.
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

Lemma update_cur_version_reg_phys_log_cor_updates_notin
  (phr : Reg) (phm : Mem) (lr : LReg) (lm lm' : LMem) (cur_map cur_map' : VMap)
  (src : RegName) (p : Perm) (b e a : Addr) ( v : Version ) :
  state_phys_log_corresponds phr phm lr lm cur_map ->
  lr !! src = Some (LCap p b e a v) ->
  update_cur_version_region_local lm cur_map (finz.seq_between b e) = (lm', cur_map') ->
  unique_in_machineL lm lr src (LCap p b e a v) ->
  src ∉ dom phr ->
  src ∉ dom lr ->
  reg_phys_log_corresponds phr lr cur_map'.
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

Lemma not_overlap_word_leaL
  (p1 p2 : Perm) (b1 b2 e1 e2 a1 a2 a2' : Addr) (v1 v2 : Version) :
  ¬ overlap_wordL (LCap p1 b1 e1 a1 v1) (LCap p2 b2 e2 a2 v2) ->
  ¬ overlap_wordL (LCap p1 b1 e1 a1 v1) (LCap p2 b2 e2 a2' v2).
Proof.
  move=> Hno_overlap Hoverlap.
  apply Hno_overlap.
  rewrite /overlap_wordL ; rewrite /overlap_wordL in Hoverlap
  ; cbn in *; done.
Qed.

Lemma unique_in_machineL_not_overlap_word
  (lm : LMem) (lr : LReg) (src r : RegName)
  (lwsrc lwr : LWord) :
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
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem)
  (cur_map : VMap) (src : RegName) (lwsrc : LWord):
  lr !! src = Some lwsrc ->
  state_phys_log_corresponds phr phm lr lm cur_map ->
  unique_in_registers phr src (lword_get_word lwsrc) ->
  unique_in_registersL lr src lwsrc.
Proof.
  move=> Hlr_src [Hreg_inv Hmem_inv] Hunique.

  eapply map_Forall_lookup_2.
  move=> r lwr Hlr_r.

  assert (Hphr_r : phr !! r = Some (lword_get_word lwr))
    by (by eapply state_phys_log_reg_get_word).
  eapply map_Forall_lookup_1 in Hphr_r; eapply Hunique ; cbn in Hphr_r.

  destruct (decide (r = src)) ; simplify_eq ; auto.
  rewrite Hlr_src in Hlr_r; simplify_eq ; by eapply state_phys_log_reg_get_word.
  by eapply state_phys_log_reg_get_word.
Qed.

Lemma phys_log_corresponds_unique_in_memory
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem)
  (cur_map : VMap) (src : RegName) (lwsrc : LWord):
  lr !! src = Some lwsrc ->
  state_phys_log_corresponds phr phm lr lm cur_map ->
  unique_in_memory phm (lword_get_word lwsrc) ->
  unique_in_memoryL lm lwsrc.
Proof.
  move=> Hlr_src [Hreg_inv Hmem_inv] Hunique.

  eapply map_Forall_lookup_2.
  move=> [a v] lw_la Hlm_la His_cur_la.
  eapply mem_phys_log_cur_addr_last_version_2 in His_cur_la; eauto.

  assert (Hphm_a : phm !! a = Some (lword_get_word lw_la))
    by (by eapply mem_phys_log_get_word).
  pose proof Hphm_a as H'phm_a.
  eapply map_Forall_lookup_1 in Hphm_a; eapply Hunique ; cbn in Hphm_a; eauto.
Qed.

(* link between
   sweep of the physical machine
   and unique_in_machine of logical memory *)
Lemma sweep_true_specL
  (phr : Reg) (phm : Mem) (lr : LReg) (lm : LMem)
  (cur_map : VMap) (src : RegName) (lwsrc : LWord):
  lr !! src = Some lwsrc →
  state_phys_log_corresponds phr phm lr lm cur_map →
  sweep phm phr src = true →
  unique_in_machineL lm lr src lwsrc.
Proof.
  intros Hlr_src HLinv Hsweep.
  assert (Hphr_src : phr !! src = Some (lword_get_word lwsrc))
    by (by eapply state_phys_log_reg_get_word).
  apply sweep_spec with (wsrc := (lword_get_word lwsrc)) in Hsweep
  ; auto.
  specialize (Hsweep Hphr_src).
  destruct Hsweep as [Hunique_reg Hunique_mem].
  intros _.
  split ;
    [ eapply phys_log_corresponds_unique_in_registers
     | eapply phys_log_corresponds_unique_in_memory
    ]
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
  (phm : Mem) (lm : LMem) (lr : LReg) (cur_map : VMap) (src : RegName)
  (p : Perm) (b e a : Addr) ( v : Version ) :
  mem_phys_log_corresponds phm lm cur_map ->
  lr !! src = Some (LCap p b e a v) ->
  is_cur_word (LCap p b e a v) cur_map ->
  unique_in_machineL lm lr src (LCap p b e a v) ->
  Forall
    (λ a' : Addr, lmem_not_access_addrL lm cur_map a')
    (finz.seq_between b e).
Proof.
  move=> Hmem_inv Hlr_src His_cur Hunique.
  apply Forall_forall.
  move=> a' Ha'.
  pose proof (is_cur_word_lea cur_map p b e a a' v His_cur) as His_cur'.
  assert (Hcur_a': is_cur_addr (a',v) cur_map).
  { eapply (cur_lword_cur_addr _ _ b e) ; eauto; cycle 1.
    apply withinBounds_true_iff.
    apply elem_of_finz_seq_between in Ha'.
    solve_addr.
    rewrite /is_lword_version //=.
  }

  rewrite /unique_in_machineL in Hunique.
  specialize (Hunique Hlr_src).
  destruct Hunique as [Hunique_reg Hunique_mem].
  eapply map_Forall_impl ; first eapply Hunique_mem.
  move=> [a0 v0] lw0 Hlast_v Hcur_v0.
  eapply no_overlap_word_no_access_addrL ; eauto.
  eapply Hlast_v.
  eapply mem_phys_log_cur_addr_last_version_1; eauto.
Qed.


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

Lemma is_cur_word_cap_change cur_map p p' b e a a' v :
  is_cur_word (LCap p b e a v) cur_map ->
  is_cur_word (LCap p' b e a' v) cur_map.
Proof.
  rewrite /is_cur_word; intros Hcur; auto.
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




(* Update the lmemory for the address a.
   Note that lmem might not contain (a,v),
   because lmem is only a *local* view of the actual lmemory. *)
Definition update_version_addr_local
  (lmem : LMem) (a : Addr) (v : Version) : LMem :=
  match lmem !! (a,v) with
  | Some lw => update_lmemory_lword lmem a v lw
  | None => lmem
  end.

(* Update the lmemory region for a given lregion.
   Note that it only updates the *local* view of the lmemory,
   which might not contain some of the addresses in la. *)
Definition update_version_region_local
  (lmem : LMem) (la : list Addr) (v : Version) : LMem :=
  foldr (fun a lmem' => update_version_addr_local lmem' a v) lmem la.


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

(* TODO might not be what I actually want *)
Lemma update_cur_version_region_global_mono_valid
  (lmem lmem' lm lm' : LMem) (vmap vmap_mem' vmap_m' : VMap)
  (la : list Addr) (v : Version) :
  NoDup la ->
  Forall (fun a => is_cur_addr (a,v) vmap) la ->
  lmem ⊆ lm ->
  update_cur_version_region_global lm lm vmap la = (lm', vmap_m') ->
  update_cur_version_region_global lmem lm vmap la = (lmem', vmap_mem') ->
  is_valid_updated_lmemory lmem la v lm'.
Proof.
Abort.


(* TODO is this definition convenient enough ?
     The details does not really matter, as soon as the following lemma
     is proven. *)
(* TODO move somewhere ? *)
Definition update_version_word_region (lmem : LMem) (lwsrc : LWord)
  : LMem :=
  match lwsrc with
  | LCap _ b e _ v
  | LSealedCap _ _ b e _ v =>
      foldr
        ( fun a lmem' => update_version_addr_local lmem' a v)
        lmem
        (finz.seq_between b e)
  | _ => lmem
  end.

  (* Lemma update_cur_version_region_implies_next_version_gen *)
  (*   (lm lm' : LMem) (cur_map cur_map': VMap) (la : list Addr) (v : Version) : *)
  (*   NoDup la -> *)
  (*   (∀ a : Addr, a ∈ la → cur_map !! a = Some v) -> *)
  (*   update_cur_version_region lm cur_map la = (lm', cur_map') -> *)
  (*   foldr (λ (a0 : Addr) (lmem' : LMem), update_version_addr lmem' a0 v) lm la = lm'. *)
  (* Proof. *)
  (*   move: lm lm' cur_map cur_map' v. *)
  (*   induction la as [|a la Hla]; intros * HNoDup Hcur_addr Hupd. *)
  (*   - by cbn in *; simplify_eq. *)
  (*   - cbn in *. *)
  (*     apply NoDup_cons in HNoDup ; destruct HNoDup as [Ha_notin_la HNoDup]. *)
  (*     assert (Hcur_a : cur_map !! a = Some v). *)
  (*     { apply Hcur_addr, elem_of_cons; by left. } *)
  (*     assert (Hcur_addr' : ∀ a0 : Addr, a0 ∈ la → cur_map !! a0 = Some v). *)
  (*     { intros a' Hin. apply Hcur_addr, elem_of_cons; by right. } *)
  (*     rewrite -/(update_cur_version_region lm cur_map la) in Hupd. *)

  (*     destruct (update_cur_version_region lm cur_map la) as [lm0 cur_map0] eqn:Hupd0. *)

  (*     (* apply bind_Some in Hupd. *) *)
  (*     (* destruct Hupd as ( [lmem0 cur_map0] & Hupd & Hupd0 ). *) *)
  (*     erewrite Hla ; eauto. *)
  (*     (* cbn. *) *)
  (*     opose proof ( *)
  (*         update_cur_version_region_notin_preserves_cur_map *)
  (*           lm lm0 cur_map cur_map0 la a v _ _ _) *)
  (*       as Hcur0_a; eauto. *)
  (*     rewrite /update_cur_version_addr Hcur0_a in Hupd. *)
  (*     destruct (lm0 !! (a, v)) as [lw0|] eqn:Hlw0; simplify_eq; first done. *)
  (*     (* inversion Hupd *) *)
  (*     (* destruct Hupd0 as (lm0 & Hlm0 & ?) ; simplify_eq. *) *)
  (* Admitted. *)

  (* Lemma update_cur_version_region_implies_next_version *)
  (*   (lm lm' : LMem) (cur_map cur_map': VMap) *)
  (*   (p : Perm) (b e a : Addr) (v : Version) : *)
  (*   is_cur_word (LCap p b e a v) cur_map -> *)
  (*   update_cur_version_region lm cur_map (finz.seq_between b e) = (lm', cur_map') -> *)
  (*   update_version_word_region lm (LCap p b e a v) = lm'. *)
  (* Proof. *)
  (*   intros Hcur_word Hupd. *)
  (*   eapply update_cur_version_region_implies_next_version_gen; eauto. *)
  (*   apply finz_seq_between_NoDup. *)
  (* Qed. *)

  Definition next_version_lword (lw : LWord) :=
    match lw with
    | LCap p b e a v => LCap p b e a (v + 1)
    | LSealedCap o p b e a v => LSealedCap o p b e a (v+1)
    | _ => lw
    end.

    Lemma update_cur_version_region_valid_mono
      (lmem lmem' lm lm' : LMem) (vmap vmap_mem' vmap_m' : VMap)
      (la : list Addr) (v : Version) :
      NoDup la ->
      Forall (fun a => is_cur_addr (a,v) vmap) la ->
      lmem ⊆ lm ->
      update_cur_version_region_global lmem lm vmap la = (lmem', vmap_mem') ->
      update_cur_version_region_local lm vmap la = (lm', vmap_m') ->
      is_valid_updated_lmemory lmem la v lmem'.
    Proof.
    Abort.

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
      eapply update_cur_version_addr_local_preserves_content_lmem
        with (a := a0) in Hupd_lm; eauto.
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
        rewrite /update_lmemory_lword.
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
        rewrite /update_lmemory_lword.
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
        eapply update_cur_version_region_local_notin_preserves_cur_2 in Hcur_v'
        ; eauto.
        eapply Hmaxv in Hcur_v'.
        eapply update_cur_version_region_local_preserves_content_lmem; eauto.
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
      - rewrite -/(is_cur_addr (a0, va0) vmap_m') in Hlva0.
        eapply update_cur_version_addr_local_notin_preserves_cur_2 in Hlva0
        ; [| eauto |]; eauto.
        eapply update_cur_version_region_local_notin_preserves_cur_2 in Hlva0
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

        eapply update_cur_version_region_local_notin_preserves_cur_1 in Hupd_lm
        ; [| eauto |]; eauto.
        eapply update_cur_version_addr_local_notin_preserves_cur_1 in Hupd_lm0
        ; [| eauto |]; eauto.
        rewrite /is_cur_addr /= in Hupd_lm0.
        by rewrite Hlva0 in Hupd_lm0.
    Qed.


    Lemma gen_heap_lmem_version_update `{HmemG : memG Σ, HregG : regG Σ} :
      ∀ (lm lmem lm' lmem': LMem) (vmap vmap_m' vmap_mem': VMap)
        (la : list Addr) ( v : Version ),
        NoDup la ->
        lmem ⊆ lm ->
        update_cur_version_region_local lm vmap la = (lm', vmap_m') ->
        update_cur_version_region_global lmem lm vmap la = (lmem', vmap_mem') ->
        Forall (λ a : Addr, lm !! (a, v+1) = None) la ->
        Forall (λ a : Addr, is_cur_addr (a,v) vmap) la ->
        gen_heap_interp lm
        -∗ ([∗ map] k↦y ∈ lmem, mapsto k (DfracOwn 1) y)
        ==∗ gen_heap_interp lm' ∗ [∗ map] k↦y ∈ lmem', mapsto k (DfracOwn 1) y.
Proof.
  move=> lm lmem lm' lmem' vmap vmap_m' vmap_mem' la.
  move: lm lmem lm' lmem' vmap vmap_m' vmap_mem'.
  induction la as [|a la IH]
  ; iIntros
      (lm lmem lm' lmem' vmap vmap_m' vmap_mem' v
         HNoDup_la Hlmem_incl Hupd_lm Hupd_lmem Hmaxv_lm Hcur_lm)
      "Hgen Hmem".
  - (* no addresses updated *)
    cbn in Hupd_lm, Hupd_lmem ; simplify_eq.
    iModIntro; iFrame.
  - apply NoDup_cons in HNoDup_la.
    destruct HNoDup_la as [Ha_not_la HNoDup_la].

    apply Forall_cons in Hcur_lm.
    destruct Hcur_lm as (Hcur_a_lm & Hcur_lm).

    apply Forall_cons in Hmaxv_lm.
    destruct Hmaxv_lm as (Hmaxv_a & Hmaxv_lm).

    apply update_cur_version_region_local_cons in Hupd_lm
    ; destruct Hupd_lm as (lm0 & vmap_m0 & Hupd_lm & Hupd_lm0).

    apply update_cur_version_region_global_cons in Hupd_lmem
    ; destruct Hupd_lmem as (lmem0 & vmap_mem0 & Hupd_lmem & Hupd_lmem0).

    eapply update_cur_version_inter in Hupd_lmem0 ; eauto.

    assert (lmem0 ⊆ lm0 /\ vmap_mem0 ⊆ vmap_m0) as [Hlmem0_incl Hvmap0_incl].
    eapply update_cur_version_region_inter_incl; eauto.
    { apply Forall_forall. intros a' Ha' v' Hcur_a'.
      apply elem_of_list_lookup_1 in Ha'. destruct Ha' as [lwa' Ha'].
      eapply Forall_lookup in Hcur_lm; eauto.
      eapply is_cur_addr_same in Hcur_a'; eauto; simplify_eq.
      eapply Forall_lookup in Hmaxv_lm; eauto.
    }

    opose proof
      (update_cur_version_addr_inter_incl_vmap _ _ _ _ _ _ _ _ _ _ _ Hupd_lmem0 Hupd_lm0)
      as Hvmap_incl ; eauto.
    rewrite /update_cur_version_addr_global in Hupd_lmem0.
    rewrite /update_cur_version_addr_local in Hupd_lm0.

    destruct (vmap_mem0 !! a) as [va |] eqn:Hvmap_mem0_a.
    2: {
      erewrite update_cur_version_region_inter_incl_vmap' in Hvmap_mem0_a; eauto.
      rewrite Hvmap_mem0_a in Hupd_lm0; simplify_eq.
      iApply (IH with "Hgen"); eauto.
    }
    eapply update_cur_version_region_local_notin_preserves_cur_1
      in Hcur_a_lm; eauto.
    eapply lookup_weaken in Hvmap_mem0_a; eauto.
    rewrite -/(is_cur_addr (a,va) vmap_m0) in Hvmap_mem0_a.
    eapply is_cur_addr_same in Hcur_a_lm; eauto; simplify_map_eq.
    destruct (lm0 !! (a, v)) as [lw|] eqn:Hlm0_a ; simplify_eq.
    2: { iApply (IH with "Hgen"); eauto. }
    specialize (IH lm lmem lm0 lmem0 vmap vmap_m0 vmap_mem0 v
                  HNoDup_la Hlmem_incl Hupd_lm Hupd_lmem).

    iDestruct (IH with "Hgen Hmem") as ">[Hgen Hmem]"; eauto.
    eapply update_cur_version_region_local_preserves_content_lmem in Hmaxv_a
    ; eauto.

    iMod (((gen_heap_alloc lm0 (a, v + 1) lw) with "Hgen"))
      as "(Hgen & Ha & _)"; auto.
    rewrite /update_lmemory_lword.
    iModIntro ; iFrame.
    iApply (big_sepM_insert with "[Hmem Ha]"); last iFrame.
    eapply lookup_weaken_None; eauto.
Qed.
