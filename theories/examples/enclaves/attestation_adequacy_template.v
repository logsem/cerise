From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
  logical_mapsto
  stdpp_extra iris_extra
  rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample.
(* From cap_machine.proofmode Require Export disjoint_regions_tactics. *)
From cap_machine.proofmode Require Export mkregion_helpers disjoint_regions_tactics.


Definition register_to_lregister (reg : Reg) ( v : Version ) : LReg :=
  fmap (fun w => word_to_lword w v) reg.

Definition memory_to_lmemory (mem : Mem) ( v : Version ) : LMem :=
  kmap (fun a => (a,v)) (fmap (fun w => word_to_lword w v) mem).

Record prog := MkProg {
  prog_start: Addr;
  prog_end: Addr;
  prog_instrs: list Word;

  prog_size:
    (prog_start + length prog_instrs)%a = Some prog_end;
}.

Definition prog_region (P: prog): gmap Addr Word :=
  mkregion (prog_start P) (prog_end P) (prog_instrs P).


Definition adv_condition adv w v :=
  is_z w = true \/ in_region (word_to_lword w v) (prog_start adv) (prog_end adv) v.

Program Definition empty_prog a : prog := MkProg a a [] _.
Next Obligation.
  intros. simpl. solve_addr.
Defined.

Lemma empty_prog_region a :
  prog_region (empty_prog a) = ∅.
Proof.
  rewrite /prog_region /empty_prog /mkregion /=.
  rewrite finz_seq_between_empty;[|solve_addr].
  auto.
Qed.

Lemma prog_region_dom (P: prog):
  dom (prog_region P) =
  list_to_set (finz.seq_between (prog_start P) (prog_end P)).
Proof.
  rewrite /prog_region /mkregion dom_list_to_map_L fst_zip //.
  rewrite finz_seq_between_length /finz.dist.
  pose proof (prog_size P). solve_addr.
Qed.

Record memory_inv := MkMemoryInv {
  minv : gmap Addr Word → Prop;
  minv_dom : gset Addr;

  minv_dom_correct :
    ∀ m m',
      (∀ a, a ∈ minv_dom → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
      minv m ↔ minv m';
}.

Lemma minv_sub_extend (m m': gmap Addr Word) (I: memory_inv) :
  minv_dom I ⊆ dom m →
  m ⊆ m' →
  minv I m →
  minv I m'.
Proof.
  intros Hdom Hsub Hm.
  eapply minv_dom_correct. 2: eassumption.
  intros a Ha.
  assert (is_Some (m !! a)) as [? ?].
  { eapply elem_of_dom.
    rewrite elem_of_subseteq in Hdom.
    eapply Hdom. auto. }
  eexists. split; eauto.
  rewrite map_subseteq_spec in Hsub.
  eapply Hsub. eauto.
Qed.

Lemma minv_sub_restrict (m m': gmap Addr Word) (I: memory_inv) :
  minv_dom I ⊆ dom m →
  m ⊆ m' →
  minv I m' →
  minv I m.
Proof.
  intros Hdom Hsub Hm.
  eapply minv_dom_correct. 2: eassumption.
  intros a Ha.
  assert (is_Some (m !! a)) as [? ?].
  { eapply elem_of_dom.
    rewrite elem_of_subseteq in Hdom.
    eapply Hdom. auto. }
  eexists. split; eauto.
  rewrite map_subseteq_spec in Hsub.
  eapply Hsub; eauto.
Qed.

Lemma filter_dom_is_dom (m: gmap Addr Word) (d: gset Addr):
  d ⊆ dom m →
  dom (filter (λ '(a, _), a ∈ d) m) = d.
Proof.
  intros Hd. eapply set_eq. intros a.
  rewrite (dom_filter_L _ _ d); auto.
  intros. split; intros H.
  { rewrite elem_of_subseteq in Hd. specialize (Hd _ H).
    eapply elem_of_dom in Hd as [? ?]. eexists. split; eauto. }
  { destruct H as [? [? ?] ]; auto. }
Qed.

Definition minv_sep `{ceriseG Σ} (I: memory_inv) ( v : Version ): iProp Σ :=
  ∃ (m: gmap Addr Word),
    ([∗ map] a↦w ∈ (memory_to_lmemory m v), a ↦ₐ w) ∗ ⌜dom m = minv_dom I⌝ ∗
    ⌜minv I m⌝.


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

Lemma memory_to_lmemory_subseteq (m1 m2 : Mem) (v : Version) :
  m1 ⊆ m2 -> memory_to_lmemory m1 v ⊆ memory_to_lmemory m2 v.
Proof.
  intros Hm.
  rewrite /memory_to_lmemory.
  apply kmap_subseteq; first by intros x y ?; simplify_eq.
  by apply map_fmap_mono.
Qed.

Lemma register_to_lregister_lookup (reg : Reg) (r : RegName) (w : Word) (v : Version) :
  reg !! r = Some w ->
  register_to_lregister reg v !! r = Some (word_to_lword w v).
Proof.
  intros Hr.
  rewrite /register_to_lregister.
  by rewrite lookup_fmap Hr /=.
Qed.

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

Lemma memory_to_lmemory_disjoint (m1 m2 : Mem) (v : Version) :
  (m1 ##ₘ m2) ->
  ((memory_to_lmemory m1 v) ##ₘ (memory_to_lmemory m2 v)).
Proof.
  intros Hm.
  rewrite /memory_to_lmemory.
  apply map_disjoint_kmap; first by intros x y ?; simplify_eq.
  by apply map_disjoint_fmap.
Qed.

Lemma register_to_lregister_delete (reg : Reg) (r : RegName) (v : Version) :
  delete r (register_to_lregister reg v) = (register_to_lregister (delete r reg) v).
Proof. by rewrite /register_to_lregister fmap_delete. Qed.

(* TODO move *)
Lemma lword_get_word_to_lword (w : Word) (v : Version) :
  lword_get_word (word_to_lword w v) = w.
Proof.
  by destruct w ; auto; destruct sb ; auto.
Qed.

Lemma lreg_strip_register_to_lregister (reg : Reg) (v : Version) :
  lreg_strip (register_to_lregister reg v) = reg.
Proof.
  induction reg using map_ind; cbn in *; first done.
  rewrite /register_to_lregister /lreg_strip !fmap_insert lword_get_word_to_lword.
  rewrite -/(register_to_lregister m v) -/(lreg_strip _).
  by rewrite IHreg.
Qed.


Section AdequacyInit.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS LAddr LWord Σ}.
  Context {reg_preg: gen_heapGpreS RegName LWord Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {enclave_agree_preg: EnclavesAgreePreG Σ}.
  Context {enclave_excl_preg: EnclavesExclPreG Σ}.
  Context {EC_preg: ECPreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Context (I : memory_inv).

  Lemma state_phys_log_corresponds_memory_to_lmemory {RA: ReservedAddresses}
    (m mi : Mem) (lm : LMem) (vmap : VMap) (v : Version) :
    dom mi = minv_dom I ->
    v = init_version ->
    elements (minv_dom I) = reserved_addresses  ->
    mem_phys_log_corresponds m lm vmap ->
    memory_to_lmemory mi v ⊆ lm ->
    mi ⊆ m.
  Proof.
    intros Hmi_dom -> Hreserved_addrs Hinv Hmi .
    destruct Hinv as (Hdom & Hroot & Hreserved).
    intros a. rewrite /option_relation.
    destruct ( mi !! a ) as [w|] eqn:Ha; rewrite Ha; auto
    ; destruct (m !! a) as [w'|] eqn:Ha'; rewrite Ha'; auto.
    - assert (a ∈ reserved_addresses) as Ha_reserved.
      { rewrite -Hreserved_addrs elem_of_elements -Hmi_dom.
        by apply elem_of_dom.
      }
      assert ( (memory_to_lmemory mi init_version) !! (a, init_version) = Some (word_to_lword w init_version)) as Hmi_a
                                                                                                                    by rewrite lookup_kmap lookup_fmap Ha //=.
      eapply lookup_weaken in Hmi_a; eauto.
      pose proof Hmi_a as Hmi_a'.
      eapply map_Forall_lookup_1 in Hmi_a; eauto; cbn in Hmi_a.
      rewrite /is_legal_address in Hmi_a.
      destruct Hmi_a as (va & Hcur_addr & _ & [w'' Hw''] ).
      rewrite /is_cur_addr /= in Hcur_addr.
      cbn in Hw''.
      clear Hdom.
      eapply map_Forall_lookup_1 in Hreserved; eauto.
      apply Hreserved in Ha_reserved; simplify_eq.
      eapply map_Forall_lookup_1 in Hroot; eauto.
      destruct Hroot as (lw & Hlw & Hm' & Hcur).
      rewrite Hmi_a' in Hlw; simplify_eq.
      by rewrite lword_get_word_to_lword.
    - assert (a ∈ reserved_addresses) as Ha_reserved.
      { rewrite -Hreserved_addrs elem_of_elements -Hmi_dom.
        by apply elem_of_dom.
      }
      assert ( (memory_to_lmemory mi init_version) !! (a, init_version) = Some (word_to_lword w init_version)) as Hmi_a
                                                                                                                    by rewrite lookup_kmap lookup_fmap Ha //=.
      eapply lookup_weaken in Hmi_a; eauto.
      eapply map_Forall_lookup_1 in Hmi_a; eauto; cbn in Hmi_a.
      rewrite /is_legal_address in Hmi_a.
      destruct Hmi_a as (va & Hcur_addr & Hmax_v & [w' Hw'] ).
      rewrite /is_cur_addr /= in Hcur_addr.
      eapply map_Forall_lookup_1 in Hreserved; eauto.
      apply Hreserved in Ha_reserved; simplify_eq.
      cbn in Hw'.
      eapply map_Forall_lookup_1 in Hroot; eauto.
      destruct Hroot as (lw & Hlw & Hm' & Hcur).
      by rewrite Hm' in Ha'.
  Qed.

  Lemma state_phys_log_corresponds_adequacy `{ReservedAddresses} (m : Mem) (reg : Reg) (v : Version)  :
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

End AdequacyInit.



Record lib_entry := MkLibEntry {
  lib_start : Addr;
  lib_end : Addr;
  lib_entrypoint : Addr;
  lib_full_content : gmap Addr Word
}.

Definition entry_points (l: list lib_entry) : list Word :=
  (map (λ entry, WCap E (lib_start entry) (lib_end entry) (lib_entrypoint entry)) l).

Record lib := MkLib {
  pub_libs : list lib_entry;
  priv_libs : list lib_entry
}.

Record tbl {p : prog} {l : list lib_entry} := MkTbl {
  prog_lower_bound : Addr ;
  tbl_start : Addr ;
  tbl_end : Addr ;
  tbl_size : (tbl_start + length l)%a = Some tbl_end ;
  tbl_prog_link : (prog_lower_bound + 1)%a = Some (prog_start p) ;

  tbl_disj : mkregion tbl_start tbl_end (entry_points l) ##ₘ
             mkregion prog_lower_bound (prog_end p) ((WCap RO tbl_start tbl_end tbl_start) :: (prog_instrs p))
}.

Definition tbl_region {p l} (t : @tbl p l) : gmap Addr Word :=
  mkregion (tbl_start t) (tbl_end t) (entry_points l).
Definition prog_lower_bound_region {l} (p : prog) (t : @tbl p l) : gmap Addr Word :=
  mkregion (prog_lower_bound t) (prog_end p) ((WCap RO (tbl_start t) (tbl_end t) (tbl_start t)) :: (prog_instrs p)).
Definition prog_tbl_region {l} (p : prog) (t : @tbl p l) : gmap Addr Word :=
  prog_lower_bound_region p t ∪ tbl_region t.
Definition prog_tbl_data_region {l} (p data: prog) (t : @tbl p l) : gmap Addr Word :=
  prog_lower_bound_region p t ∪ tbl_region t ∪ prog_region data.

Lemma prog_lower_bound_region_cons {l} (p : prog) (t : @tbl p l) :
  prog_lower_bound_region p t = <[(prog_lower_bound t):=WCap RO (tbl_start t) (tbl_end t) (tbl_start t)]> (prog_region p)
  ∧ (prog_region p) !! (prog_lower_bound t) = None.
Proof.
  rewrite /prog_lower_bound_region /mkregion.
  pose proof (tbl_prog_link t) as Ht.
  destruct (decide (prog_start p = prog_end p)).
  - rewrite e in Ht. rewrite /prog_region /mkregion finz_seq_between_singleton// e finz_seq_between_empty /=.
    split;auto. solve_addr.
  - pose proof (prog_size p).
    assert (prog_start p <= prog_end p)%a.
    { solve_addr. }
    rewrite (finz_seq_between_cons (prog_lower_bound t));[|solve_addr].
    simpl. rewrite (addr_incr_eq Ht) /=. split;auto.
    rewrite /prog_region /mkregion.
    apply not_elem_of_list_to_map.
    rewrite fst_zip. apply not_elem_of_finz_seq_between. solve_addr.
    rewrite finz_seq_between_length /finz.dist. solve_addr.
Qed.

Fixpoint lib_region (l : list lib_entry) : gmap Addr Word :=
  match l with
  | [] => ∅
  | e :: l => (lib_full_content e) ∪ (lib_region l)
  end.

Lemma lib_region_app l1 l2 :
  lib_region (l1 ++ l2) = lib_region l1 ∪ lib_region l2.
Proof.
  induction l1. by rewrite app_nil_l map_empty_union.
  by rewrite /= IHl1 map_union_assoc.
Qed.

Definition tbl_pub (p : prog) (l : lib) := @tbl p (pub_libs l).
Definition tbl_priv (p : prog) (l : lib) := @tbl p ((pub_libs l) ++ (priv_libs l)).

Module with_adv_and_link.


Definition is_initial_registers
  (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) (reg: gmap RegName Word) (r_adv: RegName) :=
  reg !! PC = Some (WCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P)) ∧
  reg !! r_adv = Some (WCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv)) ∧
  PC ≠ r_adv ∧
  (∀ (r: RegName), r ∉ ({[ PC ; r_adv ]} : gset RegName) →
     ∃ (w:Word), reg !! r = Some w ∧ is_z w = true).

Lemma initial_registers_full_map (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) reg r_adv :
  is_initial_registers P Adv Lib P_tbl Adv_tbl reg r_adv →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hr0 & Hne & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_adv)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Definition is_initial_memory (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) (m: gmap Addr Word) :=
  prog_tbl_region P P_tbl ⊆ m
  ∧ prog_tbl_region Adv Adv_tbl ⊆ m
  ∧ lib_region ((pub_libs Lib) ++ (priv_libs Lib)) ⊆ m
  ∧ prog_tbl_region P P_tbl ##ₘ prog_tbl_region Adv Adv_tbl
  ∧ prog_tbl_region P P_tbl ##ₘ lib_region ((pub_libs Lib) ++ (priv_libs Lib))
  ∧ prog_tbl_region Adv Adv_tbl ##ₘ lib_region ((pub_libs Lib) ++ (priv_libs Lib))
  ∧ lib_region (pub_libs Lib) ##ₘ lib_region (priv_libs Lib).

Definition initial_memory_domain (P Adv: prog) (Lib : lib) (P_tbl : tbl_priv P Lib) (Adv_tbl : tbl_pub Adv Lib) : gset Addr :=
  dom (prog_tbl_region P P_tbl)
      ∪ dom (prog_tbl_region Adv Adv_tbl)
      ∪ dom (lib_region ((pub_libs Lib) ++ (priv_libs Lib))).

(* NOTE: solely this version of adequacy has been updated to work with seals, by having allocated seals in the precondition *)
Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS LAddr LWord Σ}.
  Context {reg_preg: gen_heapGpreS RegName LWord Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {enclave_agree_preg: EnclavesAgreePreG Σ}.
  Context {enclave_excl_preg: EnclavesExclPreG Σ}.
  Context {EC_preg: ECPreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Context (P Adv: prog).
  Context (Lib : lib).
  Context (P_tbl : @tbl_priv P Lib).
  Context (Adv_tbl : @tbl_pub Adv Lib).
  Context (I : memory_inv).
  Context (r_adv : RegName).
  Context (vinit : Version).

  Definition invN : namespace := nroot .@ "templateadequacy" .@ "inv".

  Lemma template_adequacy' (m m': Mem) (reg reg': Reg)
    (etbl' : ETable) (ecur' : ENum)
    (es: list cap_lang.expr)
    :
    is_initial_memory P Adv Lib P_tbl Adv_tbl m →
    is_complete_memory m →
    is_initial_registers P Adv Lib P_tbl Adv_tbl reg r_adv →
    is_complete_registers reg m →

    Forall (fun w => adv_condition Adv w vinit) (prog_instrs Adv) →
    minv I m →
    minv_dom I ⊆ dom (lib_region (priv_libs Lib)) →

    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom I) m in
    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, ReservedAddresses} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
     (* ∗ custom_enclave_inv *)
       ∗ @na_own _ (@logrel_na_invG _ NA) logrel_nais ⊤ (*XXX*)

       (* Registers *)
       ∗ PC ↦ᵣ LCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P) vinit
       ∗ r_adv ↦ᵣ LCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv) vinit
       ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

       (* Memory *)
       (* P program and table *)
       ∗ (prog_lower_bound P_tbl, vinit) ↦ₐ (LCap RO (tbl_start P_tbl) (tbl_end P_tbl) (tbl_start P_tbl) vinit)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (tbl_region P_tbl) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
       (* Adv program and table *)
       ∗ (prog_lower_bound Adv_tbl, vinit) ↦ₐ (LCap RO (tbl_start Adv_tbl) (tbl_end Adv_tbl) (tbl_start Adv_tbl) vinit)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (tbl_region Adv_tbl) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
       (* filtered entries *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (lib_region (pub_libs Lib)) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (filtered_map (lib_region (priv_libs Lib))) vinit), a ↦ₐ w)

       ∗ EC⤇ 0
       ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step
      ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := ∅ ; enumcur := 0 |})
      (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
    minv I m'.
  Proof.
    intros Hm Hm_complete Hreg Hreg_complete Hadv HI HIdom prog_map Hspec Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c:ExecConf) => minv I c.(mem)) as state_is_good.
    specialize (WPI
                  (Seq (Instr Executable))
                  {| reg := reg ; mem := m ; etable := ∅ ; enumcur := 0 |}
                  es
                  {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}
                  (state_is_good {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |})).
    eapply WPI; eauto. intros Hinv κs. clear WPI.

    unfold is_initial_memory in Hm.

    iMod (gen_heap_init ((memory_to_lmemory m vinit):LMem))
      as (lmem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init ((register_to_lregister reg vinit):LReg))
      as (lreg_heapg) "(Hreg_ctx & Hreg & _)" .
    iMod (own_alloc (A := enclaves_agreeUR) (● ∅)) as (γhist) "Henclave_hist"
    ; first by apply auth_auth_valid.
    iMod (own_alloc (A := enclaves_agreeUR) (● ∅)) as (γprev) "Henclave_prev"
    ; first by apply auth_auth_valid.
    iMod (own_alloc (A := enclaves_exclUR) (● ∅)) as (γlive) "Henclave_live"
    ; first by apply auth_auth_valid.
    iMod (own_alloc (A := ECUR) (● 0 ⋅ ◯ 0)) as (γEC) "[HEC_full HEC]"
    ; first by eapply auth_both_valid_2.
    (* TRICK: for some reason, if the set is not opaque,
       Rocq takes forever to apply iMod *)
    iMod (seal_store_init gset_all_otypes) as (seal_storeg) "Hseal_store".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".


    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose ceriseg := CeriseG Σ Hinv lmem_heapg lreg_heapg
                      enclave_agree_preg enclave_excl_preg γhist γprev γlive
                      EC_preg γEC.
    set ( addr_inv := (elements (minv_dom I))).
    pose reservedaddresses := ReservedAddressesG addr_inv vinit.
    specialize (Hspec ceriseg seal_storeg logrel_na_invs reservedaddresses).
    destruct Hm as (HM & HA & HL & (Hdisj1 & Hdisj2 & Hdisj3 & Hdisj4)).

    iDestruct (big_sepM_subseteq with "Hmem") as "Hprogadv".
    { transitivity (
          (memory_to_lmemory (
          prog_tbl_region P P_tbl ∪
                    prog_tbl_region Adv Adv_tbl ∪
                    lib_region ((pub_libs Lib) ++ (priv_libs Lib))) vinit)
        ); eauto.
      apply memory_to_lmemory_subseteq.
      rewrite map_subseteq_spec. intros * HH.
      apply lookup_union_Some in HH; auto. destruct HH as [HH|HH].
      apply lookup_union_Some in HH; auto. destruct HH as [HH|HH].
      eapply map_subseteq_spec in HM; eauto.
      eapply map_subseteq_spec in HA; eauto.
      eapply map_subseteq_spec in HL; eauto.
      apply map_disjoint_union_l;auto.
    }
    iEval (rewrite 2!memory_to_lmemory_union) in "Hprogadv".
    iDestruct (big_sepM_union with "Hprogadv") as "[Hprog Hlib]";
      [apply map_disjoint_union_l;auto;split;apply memory_to_lmemory_disjoint; auto|].
    iDestruct (big_sepM_union with "Hprog") as "[Hp Hadv]";
      [apply memory_to_lmemory_disjoint; auto|].

    pose proof (tbl_disj P_tbl) as Hdisjtbl1.
    pose proof (tbl_disj Adv_tbl) as Hdisjtbl2.
    pose proof (tbl_prog_link P_tbl) as Hlink1.
    pose proof (tbl_prog_link Adv_tbl) as Hlink2.

    iEval (rewrite memory_to_lmemory_union) in "Hp".
    iDestruct (big_sepM_union with "Hp") as "[Hp Hp_tbl]";
      [apply memory_to_lmemory_disjoint; auto|].
    iEval (rewrite memory_to_lmemory_union) in "Hadv".
    iDestruct (big_sepM_union with "Hadv") as "[Hadv Hadv_tbl]";
      [apply memory_to_lmemory_disjoint; auto|].

    iEval (rewrite lib_region_app memory_to_lmemory_union) in "Hlib".
    iDestruct (big_sepM_union with "Hlib") as "[Hlib_pub Hlib_priv]";
      [apply memory_to_lmemory_disjoint; auto|].


    set prog_in_inv :=
      filter (fun '(a, _) => a ∈ minv_dom I) (lib_region (priv_libs Lib)).
    set prog_nin_inv :=
      filter (fun '(a, _) => a ∉ minv_dom I) (lib_region (priv_libs Lib)).
    rewrite (_: lib_region (priv_libs Lib) = prog_in_inv ∪ prog_nin_inv).
    2: { symmetry. apply map_filter_union_complement. }
    iEval (rewrite memory_to_lmemory_union) in "Hlib_priv".
    iDestruct (big_sepM_union with "Hlib_priv") as "[Hlib_inv Hlib_priv]".
    { by apply memory_to_lmemory_disjoint, map_disjoint_filter_complement. }

    iMod (inv_alloc invN ⊤ (minv_sep I vinit) with "[Hlib_inv]") as "#Hinv".
    { iNext. unfold minv_sep. iExists prog_in_inv. iFrame. iPureIntro.
      assert (minv_dom I ⊆ dom (lib_region (priv_libs Lib))).
      { etransitivity. eapply HIdom. auto. }
      rewrite filter_dom_is_dom; auto. split; auto.
      eapply minv_sub_restrict; [ | | eapply HI]. rewrite filter_dom_is_dom//.
      transitivity (lib_region (priv_libs Lib)); auto. rewrite /prog_in_inv.
      eapply map_filter_subseteq; typeclasses eauto.
      transitivity (lib_region (pub_libs Lib ++ priv_libs Lib)); auto.
      rewrite lib_region_app. apply map_union_subseteq_r. auto.
    }

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hr0 & Hne & Hrothers).
    iDestruct (big_sepM_delete _ _ PC
                with "Hreg") as "[HPC Hreg]"; eauto.
    { erewrite register_to_lregister_lookup; eauto. }
    iEval (cbn) in "HPC".
    iDestruct (big_sepM_delete _ _ r_adv with "Hreg") as "[Hr0 Hreg]".
    { rewrite lookup_delete_ne //.
      erewrite register_to_lregister_lookup; eauto.
    }

    set lreg := (register_to_lregister reg vinit).
    set lrmap := delete r_adv (delete PC lreg).


    iAssert ([∗ map] r↦w ∈ lrmap, r ↦ᵣ w ∗ ⌜is_zL w = true⌝)%I
               with "[Hreg]" as "Hreg".
    { iApply (big_sepM_mono with "Hreg"). intros r w Hr. cbn.
      subst lrmap. apply lookup_delete_Some in Hr as [? Hr].
      apply lookup_delete_Some in Hr as [? Hr].
      opose proof (Hrothers r _) as HH; first set_solver.
      destruct HH as [? (Hr' & Hrz')]. simplify_map_eq. iIntros. iFrame.
      subst lreg.
      apply (register_to_lregister_lookup _ _ _ vinit) in Hr'; eauto.
      rewrite Hr in Hr'.
      simplify_eq.
      destruct x ; cbn in Hrz' ; try congruence.
      by cbn.
    }

    assert (∀ r, is_Some (reg !! r)) as Hreg_full.
    { intros r.
      destruct (decide (r = PC)); subst; [by eauto|].
      destruct (decide (r = r_adv)); subst; [by eauto|].
      destruct (Hrothers r) as [? [? ?] ]; eauto. set_solver. }
    subst lrmap lreg.
    rewrite !register_to_lregister_delete.
    set rmap := (delete _ _) : Reg.

    pose proof (prog_lower_bound_region_cons P P_tbl) as [HeqP HNoneP].
    pose proof (prog_lower_bound_region_cons Adv Adv_tbl) as [HeqAdv HNoneAdv].
    rewrite HeqP HeqAdv.
    Set Nested Proofs Allowed.

    iEval (rewrite memory_to_lmemory_insert) in "Hp".
    iDestruct (big_sepM_insert with "Hp") as "[Hlinkp Hp]"
    ;[rewrite memory_to_lmemory_lookup;apply fmap_None; auto|].
    iEval (rewrite memory_to_lmemory_insert) in "Hadv".
    iDestruct (big_sepM_insert with "Hadv") as "[Hlinkadv Hadv]"
    ;[rewrite memory_to_lmemory_lookup;apply fmap_None; auto|].

    iPoseProof (Hspec rmap with
                 "[$HPC $Hr0 $Hreg $HEC $Hseal_store
                  $Hlinkp $Hp $Hlinkadv $Hadv $Hp_tbl
                  $Hadv_tbl $Hlib_pub $Hlib_priv
                  $Hinv $Hna]") as "Spec".
    { subst rmap. rewrite !dom_delete_L regmap_full_dom. set_solver+. apply Hreg_full. }

    iModIntro.
    iExists (fun σ κs _ => state_interp_logical σ).
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL.
    {
      iExists (register_to_lregister reg vinit),
                (memory_to_lmemory m vinit),
                  (gset_to_gmap vinit (dom m)), ∅, ∅, ∅.
      iFrame; cbn.
      repeat (iSplit ; first done).
      iPureIntro.
      apply state_phys_log_corresponds_adequacy; eauto.
    }

    iIntros "Hinterp'".
    rewrite /state_interp_logical.
    iDestruct "Hinterp'"
      as (lr' lm' vmap' cur_tb' prev_tb' all_tb')
           "(Hreg' & Hmem'
           & %Hcur_tb' & Henclaves_cur & Henclaves_prev & Henclaves_all
           & HEC & %Hdis_tb & %Hdom_all_tb & %Hdis_tb' & %Hall_tb
           & %Hstate_inv)".
    cbn in Hstate_inv.
    iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    unfold minv_sep. iDestruct "Hx" as (mi) "(Hmi & Hmi_dom & %)".
    iDestruct "Hmi_dom" as %Hmi_dom.
    iDestruct (gen_heap_valid_inclSepM with "Hmem' Hmi") as %Hmi_incl.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
    eapply minv_sub_extend; [| |eassumption].
    rewrite Hmi_dom //.
    destruct Hstate_inv.
    eapply state_phys_log_corresponds_memory_to_lmemory; eauto.
  Qed.

End Adequacy.

  Lemma template_adequacy
    `{MP: MachineParameters}
    (P Adv: prog) (Lib : lib)
    (P_tbl : @tbl_priv P Lib)
    (Adv_tbl : @tbl_pub Adv Lib) (I: memory_inv) (r_adv : RegName)
    (m m': Mem) (reg reg': Reg) (etbl' : ETable) (ecur' : ENum)
    (es: list cap_lang.expr):
    let vinit := 0 in

    is_initial_memory P Adv Lib P_tbl Adv_tbl m →
    is_complete_memory m →
    is_initial_registers P Adv Lib P_tbl Adv_tbl reg r_adv →
    is_complete_registers reg m →

    Forall (fun w => adv_condition Adv w vinit) (prog_instrs Adv) →
    minv I m →
    minv_dom I ⊆ dom (lib_region (priv_libs Lib)) →

    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom I) m in
    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, ReservedAddresses} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
     (* ∗ custom_enclave_inv *)
       ∗ @na_own _ (@logrel_na_invG _ NA) logrel_nais ⊤ (*XXX*)

       (* Registers *)
       ∗ PC ↦ᵣ LCap RWX (prog_lower_bound P_tbl) (prog_end P) (prog_start P) vinit
       ∗ r_adv ↦ᵣ LCap RWX (prog_lower_bound Adv_tbl) (prog_end Adv) (prog_start Adv) vinit
       ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

       (* Memory *)
       (* P program and table *)
       ∗ (prog_lower_bound P_tbl, vinit) ↦ₐ (LCap RO (tbl_start P_tbl) (tbl_end P_tbl) (tbl_start P_tbl) vinit)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (tbl_region P_tbl) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
       (* Adv program and table *)
       ∗ (prog_lower_bound Adv_tbl, vinit) ↦ₐ (LCap RO (tbl_start Adv_tbl) (tbl_end Adv_tbl) (tbl_start Adv_tbl) vinit)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (tbl_region Adv_tbl) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
       (* filtered entries *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (lib_region (pub_libs Lib)) vinit), a ↦ₐ w)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (filtered_map (lib_region (priv_libs Lib))) vinit), a ↦ₐ w)

       ∗ EC⤇ 0
       ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step
      ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := ∅ ; enumcur := 0 |})
      (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
    minv I m'.
  Proof.
    set (Σ := #[invΣ; gen_heapΣ LAddr LWord; gen_heapΣ RegName LWord;
                na_invΣ; sealStorePreΣ; EnclavesAgreePreΣ; EnclavesExclPreΣ; ECPreΣ]).
    intros.
    eapply (@template_adequacy' Σ); eauto ; try typeclasses eauto.
  Qed.

End with_adv_and_link.
