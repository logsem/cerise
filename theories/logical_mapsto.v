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
    - the logical memory contains only the current version of the logical addresses
      (i.e. dom(lm) ⊆ dom(cur_map))
    - for all entries in the view map,
      + it exists is a logical word `lw` in the logical memory `lm`
      ( i.e. dom(cur_map) ⊆ dom(lm) )
      + the logical word `lw` corresponds to the actual word in the physical memory `phm`
        for the same address
      + the logical word `lw` is the current view of the word
 *)
Definition mem_phys_log_corresponds (phm : Mem) (lm : LMem) (cur_map : gmap VMap) :=
  (* map_Forall (λ la _ , exists v, cur_map !! la.1 = Some v )
     lm (* domain of `lm` is subset of `cur_map`*) *)
  (* TODO bastien : should the logical addresses of lm always be the latest view ??
     shouldn't it be the other way around ? *)
    map_Forall (λ la _ , is_cur_addr la cur_map) lm
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
  - eapply map_Forall_impl; eauto.
    intros a' v' Hp; cbn in *.
    destruct la as [a v].

    destruct Hp as (lw' & Hla' & Hph_lw' & Hcur_lw').
    pose proof (Hla'' := Hla').
    eapply map_Forall_lookup_1 in Hla'; eauto ; cbn in Hla'.
    rewrite /is_cur_addr /= in Hla.
    rewrite /is_cur_addr /= in Hla'; cbn.

    destruct (decide (a' = a)) as [Heq | Hneq]; simplify_eq.
    + exists lw ; split ; [ by simplify_map_eq|].
      split; auto. cbn ;by simplify_map_eq.
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

Lemma state_phys_corresponds_mem lw (w : Word) la (a : Addr) pr pm lr lm cur_map :
  lword_get_word lw = w ->
  laddr_get_addr la = a ->
  state_phys_log_corresponds pr pm lr lm cur_map ->
  lm !! la = Some lw ->
  pm !! a = Some w.
Proof.
  intros * Hlword Hladdr HLinv Hlr.
  destruct HLinv as [_ HmemInv]; simpl in *.
  destruct HmemInv as [Hdom Hroot]; simpl in *.
  eapply (map_Forall_lookup_1 (λ (la : LAddr) (_ : LWord), is_cur_addr la cur_map)) in Hdom;
    last eapply Hlr.
  eapply map_Forall_lookup_1 in Hroot ; last eapply Hdom.
  destruct Hroot as (lw' & Hlm & Hpm & Hcurword).
  unfold is_cur_addr in Hdom; simpl in *.
  inv Hdom.
  rewrite (_ : la = (la.1, la.2)) in Hlr.
  2: { apply injective_projections; auto. }
  rewrite Hlr in Hlm ; clear Hlr; inv Hlm.
  exact Hpm.
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
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [Hdom Hroot] Hlm.
  eapply map_Forall_lookup_1 in Hdom; eauto. cbn in Hdom.
  destruct Hdom as (lw' & Hlw' & Hphm & _).
  rewrite Hlm in Hlw'. rewrite Hphm.
  injection Hlw'; intros -> ; auto.
Qed.

Lemma mem_phys_log_current_word phm lm cur_map a v lw:
  mem_phys_log_corresponds phm lm cur_map  ->
  lm !! (a, v) = Some lw ->
  is_cur_word lw cur_map.
Proof.
  intros [Hdom Hroot] Hlm.
  eapply map_Forall_lookup_1 in Hdom; eauto. cbn in Hdom.
  destruct Hdom as (lw' & Hlw' & _ & Hcur).
  rewrite Hlm in Hlw'.
  injection Hlw'; intros -> ; auto.
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
  phm !! a = Some (lword_get_word lw).
Proof.
  intros [_ Hmem] ? ; eapply mem_phys_log_get_word ; eauto.
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
