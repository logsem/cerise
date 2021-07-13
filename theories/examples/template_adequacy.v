From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample mkregion_helpers.

Record prog := MkProg {
  prog_start: Addr;
  prog_end: Addr;
  prog_instrs: list Word;

  prog_size:
    (prog_start + length prog_instrs)%a = Some prog_end;
}.

Definition prog_region (P: prog): gmap Addr Word :=
  mkregion (prog_start P) (prog_end P) (prog_instrs P).

Lemma prog_region_dom (P: prog):
  dom (gset Addr) (prog_region P) =
  list_to_set (region_addrs (prog_start P) (prog_end P)).
Proof.
  rewrite /prog_region /mkregion dom_list_to_map_L fst_zip //.
  rewrite region_addrs_length /region_size.
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
  minv_dom I ⊆ dom (gset Addr) m →
  m ⊆ m' →
  minv I m →
  minv I m'.
Proof.
  intros Hdom Hsub Hm.
  eapply minv_dom_correct. 2: eassumption.
  intros a Ha.
  assert (is_Some (m !! a)) as [? ?].
  { eapply elem_of_gmap_dom.
    rewrite elem_of_subseteq in Hdom |- * => Hdom.
    eapply Hdom. auto. }
  eexists. split; eauto.
  rewrite map_subseteq_spec in Hsub |- * => Hsub.
  eapply Hsub. eauto.
Qed.

Lemma minv_sub_restrict (m m': gmap Addr Word) (I: memory_inv) :
  minv_dom I ⊆ dom (gset Addr) m →
  m ⊆ m' →
  minv I m' →
  minv I m.
Proof.
  intros Hdom Hsub Hm.
  eapply minv_dom_correct. 2: eassumption.
  intros a Ha.
  assert (is_Some (m !! a)) as [? ?].
  { eapply elem_of_gmap_dom.
    rewrite elem_of_subseteq in Hdom |- * => Hdom.
    eapply Hdom. auto. }
  eexists. split; eauto.
  rewrite map_subseteq_spec in Hsub |- * => Hsub.
  eapply Hsub; eauto.
Qed.

Lemma filter_dom_is_dom (m: gmap Addr Word) (d: gset Addr):
  d ⊆ dom (gset Addr) m →
  dom (gset Addr) (filter (λ '(a, _), a ∈ d) m) = d.
Proof.
  intros Hd. eapply set_eq. intros a.
  rewrite (dom_filter_L _ _ d); auto.
  intros. split; intros H.
  { rewrite elem_of_subseteq in Hd |- * => Hd. specialize (Hd _ H).
    eapply elem_of_gmap_dom in Hd as [? ?]. eexists. split; eauto. }
  { destruct H as [? [? ?] ]; auto. }
Qed.

Definition minv_sep `{memG Σ} (I: memory_inv): iProp Σ :=
  ∃ (m: gmap Addr Word),
    ([∗ map] a↦w ∈ m, a ↦ₐ w) ∗ ⌜dom (gset Addr) m = minv_dom I⌝ ∗
    ⌜minv I m⌝.


Module basic.

Definition is_initial_registers (P: prog) (reg: gmap RegName Word) :=
  reg !! PC = Some (WCap RWX (prog_start P) (prog_end P) (prog_start P)) ∧
  (∀ (r: RegName), r ∉ ({[ PC ]} : gset RegName) →
     ∃ (w:Word), reg !! r = Some w ∧ is_cap w = false).

Lemma initial_registers_full_map (P: prog) reg :
  is_initial_registers P reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Definition is_initial_memory (P: prog) (m: gmap Addr Word) :=
  prog_region P ⊆ m.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Context (P: prog).
  Context (I : memory_inv).

  Definition invN : namespace := nroot .@ "templateadequacy" .@ "inv".

  Lemma template_adequacy' (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
    is_initial_memory P m →
    is_initial_registers P reg →
    minv I m →
    minv_dom I ⊆ list_to_set (region_addrs (prog_start P) (prog_end P)) →

    let prog_map := filter (fun '(a, _) => a ∉ minv_dom I) (prog_region P) in
    (∀ `{memG Σ, regG Σ, logrel_na_invs Σ} rmap,
     dom (gset RegName) rmap = all_registers_s ∖ {[ PC ]} →
     ⊢ inv invN (minv_sep I)
       ∗ PC ↦ᵣ WCap RWX (prog_start P) (prog_end P) (prog_start P)
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
       ∗ ([∗ map] a↦w ∈ prog_map, a ↦ₐ w)
       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
    minv I m'.
  Proof.
    intros Hm Hreg HI HIdom prog_map Hspec Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c:ExecConf) => minv I c.2) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, m) es (reg', m') (state_is_good (reg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    unfold is_initial_memory in Hm.

    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

    specialize (Hspec memg regg logrel_na_invs).
    iDestruct (big_sepM_subseteq with "Hmem") as "Hprog". by eapply Hm.

    set prog_in_inv :=
      filter (λ '(a, _), a ∈ minv_dom I) (prog_region P).
    rewrite (_: prog_region P = prog_in_inv ∪ prog_map).
    2: { symmetry. apply map_union_filter. }
    iDestruct (big_sepM_union with "Hprog") as "[Hprog_inv Hprog]".
    by apply map_disjoint_filter.

    iMod (inv_alloc invN ⊤ (minv_sep I) with "[Hprog_inv]") as "#Hinv".
    { iNext. unfold minv_sep. iExists prog_in_inv. iFrame. iPureIntro.
      assert (minv_dom I ⊆ dom (gset Addr) (prog_region P)).
      { etransitivity. eapply HIdom. rewrite prog_region_dom//. }
      rewrite filter_dom_is_dom; auto. split; auto.
      eapply minv_sub_restrict; [ | | eapply HI]. rewrite filter_dom_is_dom//.
      transitivity (prog_region P); auto. rewrite /prog_in_inv.
      eapply map_filter_sub; typeclasses eauto. }

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hrothers).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; eauto.

    set rmap := delete PC reg.
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
               with "[Hreg]" as "Hreg".
    { iApply (big_sepM_mono with "Hreg"). intros r w Hr. cbn.
      subst rmap. apply lookup_delete_Some in Hr as [? Hr].
      feed pose proof (Hrothers r) as HH. set_solver.
      destruct HH as [? (? & ?)]. simplify_map_eq. iIntros. iFrame. eauto. }

    assert (∀ r, is_Some (reg !! r)) as Hreg_full.
    { intros r.
      destruct (decide (r = PC)); subst; [by eauto|].
      destruct (Hrothers r) as [? [? ?] ]; eauto. set_solver. }

    iPoseProof (Hspec rmap with "[$HPC $Hreg $Hprog $Hinv]") as "Spec".
    { subst rmap. rewrite !dom_delete_L regmap_full_dom. set_solver+. apply Hreg_full. }

    iModIntro.
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    unfold minv_sep. iDestruct "Hx" as (mi) "(Hmi & Hmi_dom & %)".
    iDestruct "Hmi_dom" as %Hmi_dom.
    iDestruct (gen_heap_valid_inclSepM with "Hmem' Hmi") as %Hmi_incl.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
    eapply minv_sub_extend; [| |eassumption].
    rewrite Hmi_dom //. auto.
  Qed.

End Adequacy.

Theorem template_adequacy `{MachineParameters}
    (P: prog) (I: memory_inv)
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory P m →
  is_initial_registers P reg →
  minv I m →
  minv_dom I ⊆ list_to_set (region_addrs (prog_start P) (prog_end P)) →

  let prog_map := filter (fun '(a, _) => a ∉ minv_dom I) (prog_region P) in
  (∀ `{memG Σ, regG Σ, logrel_na_invs Σ} rmap,
   dom (gset RegName) rmap = all_registers_s ∖ {[ PC ]} →
   ⊢ inv invN (minv_sep I)
     ∗ PC ↦ᵣ WCap RWX (prog_start P) (prog_end P) (prog_start P)
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
     ∗ ([∗ map] a↦w ∈ prog_map, a ↦ₐ w)
     -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  minv I m'.
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              na_invΣ]).
  intros. eapply (@template_adequacy' Σ); eauto; typeclasses eauto.
Qed.

End basic.

Module with_adv.

Definition is_initial_registers (P Adv: prog) (reg: gmap RegName Word) :=
  reg !! PC = Some (WCap RWX (prog_start P) (prog_end P) (prog_start P)) ∧
  reg !! r_t0 = Some (WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv)) ∧
  (∀ (r: RegName), r ∉ ({[ PC ]} : gset RegName) →
     ∃ (w:Word), reg !! r = Some w ∧ is_cap w = false).

Lemma initial_registers_full_map (P Adv: prog) reg :
  is_initial_registers P Adv reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hr0 & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_t0)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Definition is_initial_memory (P Adv: prog) (m: gmap Addr Word) :=
  prog_region P ⊆ m
  ∧ prog_region Adv ⊆ m
  ∧ prog_region P ##ₘ prog_region Adv.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Context (P Adv: prog).
  Context (I : memory_inv).

  Definition invN : namespace := nroot .@ "templateadequacy" .@ "inv".

  Lemma template_adequacy' (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
    is_initial_memory P Adv m →
    is_initial_registers P Adv reg →
    Forall (λ w, is_cap w = false) (prog_instrs Adv) →
    minv I m →
    minv_dom I ⊆ list_to_set (region_addrs (prog_start P) (prog_end P)) →

    let prog_map := filter (fun '(a, _) => a ∉ minv_dom I) (prog_region P) in
    (∀ `{memG Σ, regG Σ, logrel_na_invs Σ} rmap,
     dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
     ⊢ inv invN (minv_sep I)
       ∗ PC ↦ᵣ WCap RWX (prog_start P) (prog_end P) (prog_start P)
       ∗ r_t0 ↦ᵣ WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv)
       ∗ interp (WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv))
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
       ∗ ([∗ map] a↦w ∈ prog_map, a ↦ₐ w)
       -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

    rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
    minv I m'.
  Proof.
    intros Hm Hreg Hadv HI HIdom prog_map Hspec Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c:ExecConf) => minv I c.2) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, m) es (reg', m') (state_is_good (reg', m'))).
    eapply WPI. intros Hinv κs. clear WPI.

    unfold is_initial_memory in Hm.

    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

    specialize (Hspec memg regg logrel_na_invs).
    destruct Hm as (HM & HA & Hdisj).

    iDestruct (big_sepM_subseteq with "Hmem") as "Hprogadv".
    { transitivity (prog_region P ∪ prog_region Adv); eauto.
      rewrite map_subseteq_spec. intros * HH.
      apply lookup_union_Some in HH; auto. destruct HH as [HH|HH].
      eapply map_subseteq_spec in HM; eauto.
      eapply map_subseteq_spec in HA; eauto. }
    iDestruct (big_sepM_union with "Hprogadv") as "[Hprog Hadv]";
      [assumption|].

    set prog_in_inv :=
      filter (λ '(a, _), a ∈ minv_dom I) (prog_region P).
    rewrite (_: prog_region P = prog_in_inv ∪ prog_map).
    2: { symmetry. apply map_union_filter. }
    iDestruct (big_sepM_union with "Hprog") as "[Hprog_inv Hprog]".
    by apply map_disjoint_filter.

    iMod (inv_alloc invN ⊤ (minv_sep I) with "[Hprog_inv]") as "#Hinv".
    { iNext. unfold minv_sep. iExists prog_in_inv. iFrame. iPureIntro.
      assert (minv_dom I ⊆ dom (gset Addr) (prog_region P)).
      { etransitivity. eapply HIdom. rewrite prog_region_dom//. }
      rewrite filter_dom_is_dom; auto. split; auto.
      eapply minv_sub_restrict; [ | | eapply HI]. rewrite filter_dom_is_dom//.
      transitivity (prog_region P); auto. rewrite /prog_in_inv.
      eapply map_filter_sub; typeclasses eauto. }

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hr0 & Hrothers).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; eauto.
    iDestruct (big_sepM_delete _ _ r_t0 with "Hreg") as "[Hr0 Hreg]".
      by rewrite lookup_delete_ne //.

    set rmap := delete r_t0 (delete PC reg).
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
               with "[Hreg]" as "Hreg".
    { iApply (big_sepM_mono with "Hreg"). intros r w Hr. cbn.
      subst rmap. apply lookup_delete_Some in Hr as [? Hr].
      apply lookup_delete_Some in Hr as [? Hr].
      feed pose proof (Hrothers r) as HH. set_solver.
      destruct HH as [? (? & ?)]. simplify_map_eq. iIntros. iFrame. eauto. }

    assert (∀ r, is_Some (reg !! r)) as Hreg_full.
    { intros r.
      destruct (decide (r = PC)); subst; [by eauto|].
      destruct (decide (r = r_t0)); subst; [by eauto|].
      destruct (Hrothers r) as [? [? ?] ]; eauto. set_solver. }

    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". apply prog_size.
    iDestruct (@region_integers_alloc _ memg with "Hadv") as ">Hadv".
      by eapply Hadv. by assert (PermFlowsTo RO RWX); eauto.

    iPoseProof (Hspec rmap with "[$HPC $Hr0 $Hreg $Hprog $Hadv $Hinv]") as "Spec".
    { subst rmap. rewrite !dom_delete_L regmap_full_dom. set_solver+. apply Hreg_full. }

    iModIntro.
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    unfold minv_sep. iDestruct "Hx" as (mi) "(Hmi & Hmi_dom & %)".
    iDestruct "Hmi_dom" as %Hmi_dom.
    iDestruct (gen_heap_valid_inclSepM with "Hmem' Hmi") as %Hmi_incl.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
    eapply minv_sub_extend; [| |eassumption].
    rewrite Hmi_dom //. auto. auto.
  Qed.

End Adequacy.

Theorem template_adequacy `{MachineParameters}
    (P Adv: prog) (I: memory_inv)
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory P Adv m →
  is_initial_registers P Adv reg →
  Forall (λ w, is_cap w = false) (prog_instrs Adv) →
  minv I m →
  minv_dom I ⊆ list_to_set (region_addrs (prog_start P) (prog_end P)) →

  let prog_map := filter (fun '(a, _) => a ∉ minv_dom I) (prog_region P) in
  (∀ `{memG Σ, regG Σ, logrel_na_invs Σ} rmap,
   dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
   ⊢ inv invN (minv_sep I)
     ∗ PC ↦ᵣ WCap RWX (prog_start P) (prog_end P) (prog_start P)
     ∗ r_t0 ↦ᵣ WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv)
     ∗ interp (WCap RWX (prog_start Adv) (prog_end Adv) (prog_start Adv))
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
     ∗ ([∗ map] a↦w ∈ prog_map, a ↦ₐ w)
     -∗ WP Seq (Instr Executable) {{ λ _, True }}) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  minv I m'.
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              na_invΣ]).
  intros. eapply (@template_adequacy' Σ); eauto; typeclasses eauto.
Qed.

End with_adv.
