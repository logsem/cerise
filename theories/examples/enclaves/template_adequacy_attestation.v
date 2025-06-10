From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
  logical_mapsto
  stdpp_extra iris_extra
  rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample.
From cap_machine.proofmode Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine Require Import assert.

Record prog := MkProg {
  prog_start: Addr;
  prog_end: Addr;
  prog_instrs: list Word;

  prog_size:
    (prog_start + length prog_instrs)%a = Some prog_end;
}.

Definition prog_region (P: prog): gmap Addr Word :=
  mkregion (prog_start P) (prog_end P) (prog_instrs P).

Definition in_region (w : Word) (b e : Addr) :=
  match w with
  | WCap p b' e' a => PermFlows RO p /\ (b <= b')%a /\ (e' <= e)%a
  | _ => False
  end.

Definition adv_condition adv w :=
  is_z w = true \/ in_region w (prog_start adv) (prog_end adv).

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

  Lemma state_phys_log_corresponds_preserves_inv {RA: ReservedAddresses}
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
      assert ( (memory_to_lmemory mi init_version) !! (a, init_version) = Some (word_to_lword w init_version))
        as Hmi_a by rewrite lookup_kmap lookup_fmap Ha //=.
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
      assert ( (memory_to_lmemory mi init_version) !! (a, init_version) = Some (word_to_lword w init_version))
        as Hmi_a by rewrite lookup_kmap lookup_fmap Ha //=.
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

End AdequacyInit.



Record assert_library `{MachineParameters} := MkAssertLibrary {
  (* assert library *)
  assert_start : Addr;
  assert_cap : Addr;
  assert_flag : Addr;
  assert_end : Addr;

  assert_code_size :
    (assert_start + length assert_subroutine_instrs)%a = Some assert_cap;
  assert_cap_size :
    (assert_cap + 1)%a = Some assert_flag;
  assert_flag_size :
    (assert_flag + 1)%a = Some assert_end;
}.

Definition assert_library_content `{MachineParameters} (assert_layout : assert_library) : gmap Addr Word :=
  (* code for the assert subroutine, followed by a capability to the assert flag
     and the flag itself, initialized to 0. *)
  mkregion (assert_start assert_layout) (assert_cap assert_layout) (lword_get_word <$> assert_subroutine_instrs)
  ∪ list_to_map [(assert_cap assert_layout, WCap RW (assert_flag assert_layout) (assert_end assert_layout) (assert_flag assert_layout))]
  ∪ list_to_map [(assert_flag assert_layout, WInt 0)] (* assert flag *).

Definition assert_entry_point `{MachineParameters} (assert_layout : assert_library) :=
  WCap E (assert_start assert_layout) (assert_end assert_layout) (assert_start assert_layout).

Definition OK_invariant `{MachineParameters} (assert_layout : assert_library) (m : gmap Addr Word) : Prop :=
  ∀ w, m !! (assert_flag assert_layout) = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} (assert_layout : assert_library) : gset Addr := {[ assert_flag assert_layout ]}.

Program Definition OK_dom_correct `{MachineParameters} (assert_layout : assert_library) :
  ∀ m m',
    (∀ a, a ∈ OK_dom assert_layout → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant assert_layout m ↔ OK_invariant assert_layout m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with (assert_flag assert_layout) as [w [Hw1 Hw2] ]. rewrite /OK_dom. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition adequacy_flag_inv `{MachineParameters} (assert_layout : assert_library) : memory_inv :=
  {| minv := OK_invariant assert_layout;
     minv_dom := {[ assert_flag assert_layout ]} ;
     minv_dom_correct := OK_dom_correct assert_layout |}.

Record assert_tbl := MkTbl {
  tbl_start : Addr ;
  tbl_end : Addr ;
  tbl_size : (tbl_start + 1)%a = Some tbl_end ;
}.

Definition assert_tbl_region `{MachineParameters} (tbl : assert_tbl) (assert_layout : assert_library) : gmap Addr Word :=
  mkregion (tbl_start tbl) (tbl_end tbl) [assert_entry_point assert_layout].

Definition is_initial_registers `{MachineParameters}
  (P Adv: prog) (AssertLib : assert_library) (tbl : assert_tbl) (regs: Reg) (r_adv: RegName):=
  regs !! PC = Some (WCap RWX (prog_start P) (prog_end P) (prog_start P)) ∧
  regs !! r_adv = Some (WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv)) ∧
  PC ≠ r_adv ∧
  (∀ (r: RegName), r ∉ ({[ PC ; r_adv ]} : gset RegName) →
     ∃ (w:Word), regs !! r = Some w ∧ is_z w = true).

Lemma initial_registers_full_map `{MachineParameters}
  (P Adv: prog) (AssertLib : assert_library) (tbl : assert_tbl) (regs: Reg) (r_adv : RegName) :
  is_initial_registers P Adv AssertLib tbl regs r_adv →
  (∀ r, is_Some (regs !! r)).
Proof.
  intros (HPC & Hr0 & Hne & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_adv)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Definition is_initial_memory `{MachineParameters}
  (P Adv: prog) (AssertLib : assert_library) (tbl : assert_tbl) (m: Mem) :=
  prog_region P ⊆ m
  ∧ prog_region Adv ⊆ m
  ∧ assert_tbl_region tbl AssertLib ⊆ m
  ∧ (assert_library_content AssertLib) ⊆ m
  ∧ prog_region P ##ₘ prog_region Adv
  ∧ prog_region P ##ₘ assert_tbl_region tbl AssertLib
  ∧ prog_region P ##ₘ (assert_library_content AssertLib)
  ∧ prog_region Adv ##ₘ assert_tbl_region tbl AssertLib
  ∧ prog_region Adv ##ₘ (assert_library_content AssertLib)
  ∧ assert_tbl_region tbl AssertLib ##ₘ (assert_library_content AssertLib).

Lemma adequacy_flag_inv_is_initial_memory `{MachineParameters}
  (P Adv: prog) (AssertLib : assert_library) (tbl : assert_tbl) (m : Mem) :
  is_initial_memory P Adv AssertLib tbl m →
  minv (adequacy_flag_inv AssertLib) m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs.
  pose proof (assert_code_size AssertLib). pose proof (assert_cap_size AssertLib).
  pose proof (assert_flag_size AssertLib).
  assert (list_to_map [(assert_flag AssertLib, WInt 0)] ⊆ m) as Hassert_flag.
  { etrans;[|eauto]. eapply map_union_subseteq_r'. 2: done.
    disjoint_map_to_list.
    apply elem_of_disjoint. intro. rewrite elem_of_app !elem_of_finz_seq_between !elem_of_list_singleton.
    intros [ [? ?]|?] ->; solve_addr. }
  eapply (lookup_weaken _ _ (assert_flag AssertLib) (WInt 0)) in Hassert_flag.
    by simplify_eq. by simplify_map_eq.
Qed.

Local Instance reserved_addresses_assert `{MachineParameters} (layout : assert_library) (vinit : Version) : ReservedAddresses.
Proof. apply (ReservedAddressesG [assert_flag layout] vinit). Defined.

Definition assertInv `{ceriseG Σ, logrel_na_invs Σ, MachineParameters} (layout : assert_library) :=
  assert.assert_inv (assert_start layout) (assert_flag layout) (assert_end layout).

Definition assertN : namespace := nroot .@ "assert".

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
  Context (AssertLib : assert_library).
  Context (tbl_assert_tbl : assert_tbl).
  Context (r_adv : RegName).
  Context (vinit : Version).

  Definition invN : namespace := nroot .@ "templateadequacy" .@ "inv".

  Set Nested Proofs Allowed.

  Lemma template_adequacy' `{subG Σ' Σ}
    (m m': Mem) (reg reg': Reg)
    (etbl etbl' : ETable) (ecur ecur' : ENum)
    (es: list cap_lang.expr)
    :
    let I := (adequacy_flag_inv AssertLib) in
    let RA := reserved_addresses_assert AssertLib vinit in

    let dom_etbl_all := seq 0 ecur : list TIndex in
    let dom_etbl_dead := filter (fun tidx => tidx ∉ dom etbl ) dom_etbl_all : list TIndex in
    let dummy_I := 0 : EIdentity in
    let etbl_dead := create_gmap_default dom_etbl_dead dummy_I : ETable in
    let etbl_all := etbl ∪ etbl_dead in

    is_initial_memory P Adv AssertLib tbl_assert_tbl m →
    is_complete_memory m →
    is_initial_registers P Adv AssertLib tbl_assert_tbl reg r_adv →
    is_complete_registers reg m →
    is_initial_etable etbl ecur ->

    Forall (fun w => adv_condition Adv w) (prog_instrs Adv) →
    minv I m →

    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom I) m in
    (∀ `{ceriseG Σ, sealStoreG Σ, NA: logrel_na_invs Σ, subG Σ' Σ} rmap,
        dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
       ∗ @na_own _ (@logrel_na_invG _ NA) logrel_nais ⊤ (*XXX*)
       ∗ @na_inv _ _ _ (@logrel_na_invG _ NA) logrel_nais assertN (assertInv AssertLib vinit)

       (* Registers *)
       ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
       ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
       ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

       (* Memory *)
       (* P program *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
       (* Adv program  *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
       (* Linking Table *)
       ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region tbl_assert_tbl AssertLib) vinit), a ↦ₐ w)

       ∗ EC⤇ ecur
       ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
       ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step
      ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := etbl ; enumcur := ecur |})
      (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
    minv I m'.
  Proof.
    intros * Hm Hm_complete Hreg Hreg_complete Hetbl Hadv HI prog_map Hspec Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c:ExecConf) => minv I c.(mem)) as state_is_good.
    specialize (WPI
                  (Seq (Instr Executable))
                  {| reg := reg ; mem := m ; etable := etbl ; enumcur := ecur |}
                  es
                  {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}
                  (state_is_good {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |})).
    eapply WPI; eauto. intros Hinv κs. clear WPI.

    unfold is_initial_memory in Hm.

    iMod (gen_heap_init ((memory_to_lmemory m vinit):LMem))
      as (lmem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init ((register_to_lregister reg vinit):LReg))
      as (lreg_heapg) "(Hreg_ctx & Hreg & _)" .
    iMod (own_alloc (A := ECUR) (●E ecur ⋅ ◯E ecur)) as (γEC) "[HEC_full HEC]"
    ; first by apply excl_auth_valid.

    iMod (own_alloc (A := enclaves_exclUR) (● ( Excl <$> etbl))) as (γlive) "Henclave_live".
    { apply auth_auth_valid.
      clear.
      induction etbl using map_ind.
      + done.
      + rewrite fmap_insert.
        apply insert_valid; done.
    }

    iMod (own_alloc (A := enclaves_agreeUR) (● (to_agree <$> etbl_dead))) as (γprev) "Henclave_prev".
    { apply auth_auth_valid.
      clear.
      induction etbl_dead using map_ind.
      + done.
      + rewrite fmap_insert.
        apply insert_valid; done.
    }

    iMod (own_alloc (A := enclaves_agreeUR) (● (to_agree <$> etbl_all) ⋅ ◯ (to_agree <$> etbl_all)))
      as (γhist) "[Henclave_hist_full Henclave_hist_frag]".
    { apply auth_both_valid_2; last done.
      clear.
      induction etbl_all using map_ind.
      + done.
      + rewrite fmap_insert.
        apply insert_valid; done.
    }
    (* TRICK: for some reason, if the set is not opaque,
       Rocq takes forever to apply iMod *)
    iMod (seal_store_init gset_all_otypes) as (seal_storeg) "Hseal_store".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose ceriseg := CeriseG Σ Hinv lmem_heapg lreg_heapg
                      enclave_agree_preg enclave_excl_preg γprev γhist γlive
                      EC_preg γEC.
    set ( addr_inv := (elements (minv_dom I))).
    specialize (Hspec ceriseg seal_storeg logrel_na_invs).
    destruct Hm as (HProg & HAdv & HLink & HAssert & (Hdisj1 & Hdisj2 & Hdisj3 & Hdisj4 & Hdisj5 & Hdisj6)).

    iAssert ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)%I with "[Henclave_hist_frag]" as
      "Hall_enclaves".
    { clear.
      iInduction (etbl_all) as [|] "IH" using map_ind ; first done.
      rewrite fmap_insert.
      rewrite insert_singleton_op; last by rewrite lookup_fmap H.
      rewrite auth_frag_op own_op.
      rewrite big_opM_insert; last done.
      rewrite /enclave_all.
      cbn.
      iDestruct "Henclave_hist_frag" as  "[Hi?]"; iFrame.
      by iApply "IH".
    }

    iDestruct (big_sepM_subseteq with "Hmem") as "Hprogadv".
    { transitivity (
          (memory_to_lmemory (
               prog_region P ∪
                 prog_region Adv ∪
                 ( assert_tbl_region tbl_assert_tbl AssertLib ) ∪
                 assert_library_content AssertLib)
             vinit)
        ); eauto.
      apply memory_to_lmemory_subseteq.
      rewrite map_subseteq_spec. intros * HH.
      apply lookup_union_Some in HH; auto.
      2:{
        apply map_disjoint_union_l;auto.
        split; auto.
        apply map_disjoint_union_l;auto.
      }
      destruct HH as [HH|HH].
      - apply lookup_union_Some in HH; auto.
        2:{ apply map_disjoint_union_l;auto. }
        destruct HH as [HH|HH].
        + apply lookup_union_Some in HH; auto.
          destruct HH as [HH|HH].
          * eapply map_subseteq_spec in HProg; eauto.
          * eapply map_subseteq_spec in HAdv; eauto.
        + eapply map_subseteq_spec in HLink; eauto.
      - eapply map_subseteq_spec in HAssert; eauto.
    }
    iEval (rewrite 3!memory_to_lmemory_union) in "Hprogadv".
    iDestruct (big_sepM_union with "Hprogadv") as "[Hprog HAssertLib]".
    { apply map_disjoint_union_l;auto;split; last (apply memory_to_lmemory_disjoint; auto).
      apply map_disjoint_union_l;auto;split; apply memory_to_lmemory_disjoint; auto.
    }
    iDestruct (big_sepM_union with "Hprog") as "[Hprog HLink]".
    { apply map_disjoint_union_l;auto;split;apply memory_to_lmemory_disjoint; auto.
    }
    iDestruct (big_sepM_union with "Hprog") as "[Hp Hadv]";
      [apply memory_to_lmemory_disjoint; auto|].

    set prog_in_inv :=
      filter (fun '(a, _) => a ∈ minv_dom I) (assert_library_content AssertLib).
    set prog_nin_inv :=
      filter (fun '(a, _) => a ∉ minv_dom I) (assert_library_content AssertLib).
    rewrite (_: (assert_library_content AssertLib) = prog_in_inv ∪ prog_nin_inv).
    2: { symmetry. apply map_filter_union_complement. }
    iEval (rewrite memory_to_lmemory_union) in "HAssertLib".
    iDestruct (big_sepM_union with "HAssertLib") as "[Hassert_inv Hassert]".
    { by apply memory_to_lmemory_disjoint, map_disjoint_filter_complement. }

    iMod (inv_alloc invN ⊤ (minv_sep I vinit) with "[Hassert_inv]") as "#Hinv".
    { iNext. unfold minv_sep. iExists prog_in_inv. iFrame. iPureIntro.
      assert (minv_dom I ⊆ dom (assert_library_content AssertLib)).
      { subst I.
        rewrite /assert_library_content.
        setoid_rewrite dom_union.
        cbn.
        rewrite dom_insert_L dom_empty_L union_empty_r_L.
        apply union_subseteq_r.
      }
      rewrite filter_dom_is_dom; auto. split; auto.
      eapply minv_sub_restrict; [ | | eapply HI]. rewrite filter_dom_is_dom//.
      transitivity (assert_library_content AssertLib); auto. rewrite /prog_in_inv.
      eapply map_filter_subseteq;typeclasses eauto.
    }

  iMod (@na_inv_alloc _ _ _ (@logrel_na_invG _ logrel_na_invs) logrel.logrel_nais ⊤ assertN (assertInv AssertLib vinit)
          with "[Hassert]") as "#Hinv_assert".
  { iNext. rewrite /assertInv /assert_inv /assert_library_content.
    iExists (assert_cap AssertLib).
    pose proof (assert_code_size AssertLib). pose proof (assert_cap_size AssertLib).
    pose proof (assert_flag_size AssertLib).
    rewrite /prog_nin_inv.
    rewrite map_filter_union.
    2: { disjoint_map_to_list. apply elem_of_disjoint. intro.
         rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
         intros [ [? ?]|?]; solve_addr. }
    rewrite memory_to_lmemory_union.
    iDestruct (big_sepM_union with "Hassert") as "[Hassert _]".
    { apply memory_to_lmemory_disjoint.
      eapply map_disjoint_filter. disjoint_map_to_list.
      apply elem_of_disjoint. intro.
      rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
      intros [ [? ?]|?]; solve_addr. }
    rewrite map_filter_id.
    2: { intros ? ? HH%elem_of_dom_2. rewrite !dom_union_L dom_mkregion_eq in HH.
         2: solve_addr. apply elem_of_union in HH.
         rewrite elem_of_singleton. destruct HH as [HH|HH].
         rewrite -> elem_of_list_to_set, elem_of_finz_seq_between in HH; solve_addr.
         rewrite -> dom_list_to_map_singleton, elem_of_list_to_set, elem_of_list_singleton in HH; solve_addr. }
    rewrite memory_to_lmemory_union.
    iDestruct (big_sepM_union with "Hassert") as "[Hassert Hcap]".
    { apply memory_to_lmemory_disjoint.
      disjoint_map_to_list. apply elem_of_disjoint. intro.
      rewrite elem_of_finz_seq_between !elem_of_list_singleton. solve_addr. }
    rewrite memory_to_lmemory_insert.
    iEval (cbn) in "Hcap".
    iDestruct (big_sepM_insert with "Hcap") as "[Hcap _]"; first done.
    iFrame "Hcap".
    iSplitL "Hassert"; cycle 1.
    + iPureIntro. repeat split; solve_addr.
    + iApply (mkregion_sepM_to_sepL2 with "[Hassert]"); auto.
      { apply Forall_forall.
        intros.
        cbn in *.
        repeat (rewrite elem_of_cons in H12; destruct H12 as [-> | H12]; first done).
        set_solver+H3.
      }
      { solve_addr. }
      rewrite (_: assert_cap AssertLib = assert_start AssertLib ^+ length assert_subroutine_instrs)%a. 2: solve_addr.
    iFrame "Hassert".
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

    iPoseProof (Hspec _ rmap with
                 "[$HPC $Hr0 $Hreg $HEC $Hseal_store
                  $Hp $Hadv $HLink $Hinv_assert
                  $Hinv $Hna $Hall_enclaves]") as "Spec".
    { subst rmap. rewrite !dom_delete_L regmap_full_dom. set_solver+. apply Hreg_full. }
    iModIntro.
    iExists (fun σ κs _ => state_interp_logical σ).
    iExists (fun _ => True)%I. iFrame.
    iSplitL.
    {
      iExists (register_to_lregister reg vinit),
                (memory_to_lmemory m vinit),
                  (gset_to_gmap vinit (dom m)), etbl, etbl_dead, etbl_all.
      iFrame; cbn.
      iSplit; first done.
      iSplit.
      { iPureIntro.
        subst etbl_dead dom_etbl_dead dom_etbl_all.
        rewrite create_gmap_default_dom.
        intros tidx Htidx Htidx'.
        apply elem_of_list_to_set in Htidx'.
        apply elem_of_list_filter in Htidx' as [Htidx' _].
        set_solver + Htidx Htidx'.
      }
      iSplit.
      { iPureIntro.
        subst etbl_dead dom_etbl_dead dom_etbl_all.
        rewrite dom_union_L create_gmap_default_dom.
        replace (dom etbl) with
          ((list_to_set (filter (λ tidx : TIndex, tidx ∈ dom etbl) (seq 0 ecur))) : gset nat).
        2:{
          rewrite list_to_set_filter.
          clear -Hetbl.
          match goal with
          | _ : _ |- ?s1 = ?s2 =>
              assert (s1 ⊆ s2) as H12 ; [| assert (s2 ⊆ s1) as H21]
          end; last set_solver.
          + intros x Hx.
            rewrite elem_of_filter in Hx.
            by destruct Hx as [? ?].
          + intros x Hx.
            rewrite elem_of_filter.
            split; first done.
            rewrite elem_of_list_to_set.
            rewrite elem_of_seq.
            split; first lia.
            cbn.
            destruct Hetbl as [Hinit_tbl _].
            by apply Hinit_tbl in Hx.
        }
        rewrite !list_to_set_filter.
        rewrite filter_union_complement_L; eauto.
        exact ∅.
      }
      iSplit.
      { iPureIntro.
        subst etbl_dead dom_etbl_dead dom_etbl_all.
        apply map_disjoint_dom.
        rewrite create_gmap_default_dom.
        intros tidx Htidx Htidx'.
        apply elem_of_list_to_set in Htidx'.
        apply elem_of_list_filter in Htidx' as [Htidx' _].
        set_solver + Htidx Htidx'.
      }
      iSplit; first done.
      iPureIntro.
      apply state_phys_log_corresponds_complete; eauto.
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
    iModIntro. iPureIntro.
    rewrite /state_is_good.
    eapply minv_sub_extend; [| |eassumption].
    rewrite Hmi_dom //.
    destruct Hstate_inv.
    eapply state_phys_log_corresponds_preserves_inv; eauto.
    subst I.
    subst RA.
    rewrite /reserved_addresses /=.
    apply elements_singleton.
  Qed.

End Adequacy.

Lemma template_adequacy
  `{MP: MachineParameters}
  (Σ : gFunctors)
  (P Adv: prog) (AssertLib : assert_library) (tbl_assert_tbl : assert_tbl)
  (r_adv : RegName)
  (m m': Mem) (reg reg': Reg)
  (etbl etbl' : ETable) (ecur ecur' : ENum)
  (es: list cap_lang.expr)
  :
  let I := (adequacy_flag_inv AssertLib) in
  let vinit := 0%nat in
  let RA := reserved_addresses_assert AssertLib vinit in

  let dom_etbl_all := seq 0 ecur : list TIndex in
  let dom_etbl_dead := filter (fun tidx => tidx ∉ dom etbl ) dom_etbl_all : list TIndex in
  let dummy_I := 0 : EIdentity in
  let etbl_dead := create_gmap_default dom_etbl_dead dummy_I : ETable in
  let etbl_all := etbl ∪ etbl_dead in

  is_initial_memory P Adv AssertLib tbl_assert_tbl m →
  is_complete_memory m →
  is_initial_registers P Adv AssertLib tbl_assert_tbl reg r_adv →
  is_complete_registers reg m →
  is_initial_etable etbl ecur ->

  Forall (fun w => adv_condition Adv w) (prog_instrs Adv) →
  minv I m →

  let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom I) m in
  (∀ `{ceriseG Σ', sealStoreG Σ', NA: logrel_na_invs Σ', subG Σ Σ'} rmap,
     dom rmap = all_registers_s ∖ {[ PC; r_adv ]} →
     ⊢ inv invN (minv_sep I vinit)
     ∗ na_own logrel_nais ⊤ (*XXX*)
     ∗ na_inv logrel_nais assertN (assertInv AssertLib vinit)

     (* Registers *)
     ∗ PC ↦ᵣ LCap RWX (prog_start P) (prog_end P) (prog_start P) vinit
     ∗ r_adv ↦ᵣ LCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv) vinit
     ∗ ([∗ map] r↦w ∈ (register_to_lregister rmap vinit), r ↦ᵣ w ∗ ⌜is_zL w = true⌝)

     (* Memory *)
     (* P program *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region P) vinit), a ↦ₐ w)
     (* Adv program  *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (prog_region Adv) vinit), a ↦ₐ w)
     (* Linking Table *)
     ∗ ([∗ map] a↦w ∈ (memory_to_lmemory (assert_tbl_region tbl_assert_tbl AssertLib) vinit), a ↦ₐ w)

     ∗ EC⤇ ecur
     ∗ ([∗ set] o ∈ gset_all_otypes, can_alloc_pred o)
     ∗ ( [∗ map] tidx ↦ eid ∈ etbl_all, enclave_all tidx eid)

       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

  rtc erased_step
    ([Seq (Instr Executable)] , {| reg := reg ; mem := m ; etable := etbl ; enumcur := ecur |})
    (es, {| reg := reg' ; mem := m' ; etable := etbl' ; enumcur := ecur' |}) →
  minv I m'.
Proof.
  set (Σ' := #[invΣ; gen_heapΣ LAddr LWord; gen_heapΣ RegName LWord;
               na_invΣ; sealStorePreΣ; EnclavesAgreePreΣ; EnclavesExclPreΣ; ECPreΣ; Σ]).
  intros.
  eapply (@template_adequacy' Σ'); eauto; try typeclasses eauto.
Qed.
