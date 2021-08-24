From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental proofmode.
From cap_machine.examples Require Import addr_reg_sample malloc macros_new
     interval_client_closure interval_client interval_closure dynamic_sealing.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy.
From cap_machine Require Import monotone.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Import with_adv_and_link.

Definition offset_to_checki : Z := (interval_client_closure_instrs_length - interval_client_closure_move_offset).
Definition offset_to_interval : Z := (interval_closure_instrs_length - interval_closure_move_offset).

Class memory_layout `{MachineParameters} := {
  (* Code of interval client *)
  interval_client_region_start : Addr;
  interval_client_closure_start : Addr;
  interval_client_body_start : Addr;
  interval_client_region_end : Addr;

  interval_client_closure_size: (interval_client_closure_start +
                          (length (interval_client_closure 2 0 offset_to_checki))
                                 = Some interval_client_body_start)%a;
  interval_client_body_size : (interval_client_body_start +
                               (length (check_interval 1))
                               = Some interval_client_region_end)%a ;
  interval_client_region_start_offset: (interval_client_region_start + 1)%a
                                       = Some interval_client_closure_start;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 3)%a = Some link_table_end;

  (* adversary code *)
  adv_region_start : Addr;
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;
  adv_region_start_offset: (adv_region_start + 1)%a = Some adv_start;

  (* adversary link table *)
  adv_link_table_start : Addr;
  adv_link_table_end : Addr;
  adv_link_table_size :
    (adv_link_table_start + 1)%a = Some adv_link_table_end;

  (* interval library *)
  interval_region_start : Addr;
  interval_closure_start : Addr;
  interval_body_start : Addr;
  interval_region_end : Addr;

  interval_closure_size : (interval_closure_start +
                           length (interval_closure 0 1 offset_to_interval)
                           = Some interval_body_start)%a;
  interval_body_size : (interval_body_start +
                        length (interval 0) = Some interval_region_end)%a;
  interval_region_start_offset: (interval_region_start + 1 = Some interval_closure_start)%a;

  (* interval table *)
  int_table_start : Addr;
  int_table_end : Addr;
  int_table_size : (int_table_start + 2)%a = Some int_table_end;

  (* seal library (nested within interval library) *)
  seal_region_start : Addr;
  seal_body_start : Addr;
  seal_region_end : Addr;
  seal_size : (seal_body_start +
               length (unseal_instrs ++ (seal_instrs 0) ++ (make_seal_preamble_instrs 0))
               = Some seal_region_end)%a;
  seal_makeseal_entrypoint : Addr;
  seal_makeseal_entrypoint_correct :
    (seal_body_start + ((length unseal_instrs) + (length (seal_instrs 0))) = Some seal_makeseal_entrypoint)%a;
  seal_region_start_offset: (seal_region_start + 1 = Some seal_body_start)%a;

  (* seal table *)
  seal_table_start : Addr;
  seal_table_end : Addr;
  seal_table_size : (seal_table_start + 1 = Some seal_table_end)%a;

  (* malloc routine *)
  malloc_start : Addr;
  malloc_memptr : Addr;
  malloc_mem_start : Addr;
  malloc_end : Addr;

  malloc_code_size :
    (malloc_start + length malloc_subroutine_instrs)%a
    = Some malloc_memptr;

  malloc_memptr_size :
    (malloc_memptr + 1)%a = Some malloc_mem_start;

  malloc_mem_size :
    (malloc_mem_start <= malloc_end)%a;

  (* fail routine *)
  fail_start : Addr;
  fail_end : Addr;

  fail_size :
    (fail_start
     + (length assert_fail_instrs (* code of the subroutine *)
        + 1 (* pointer to the flag *))
    )%a
    = Some fail_end;
  (* failure flag *)
  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
      (* components *)
      region_addrs adv_region_start adv_end;
      [interval_client_region_start];
      region_addrs interval_client_closure_start interval_client_body_start;
      region_addrs interval_client_body_start interval_client_region_end;
      (* tables *)
      region_addrs link_table_start link_table_end;
      region_addrs adv_link_table_start adv_link_table_end;
      (* libraries *)
      [interval_region_start];
      region_addrs interval_closure_start interval_body_start;
      region_addrs interval_body_start interval_region_end;
      region_addrs int_table_start int_table_end;
      [seal_region_start];
      region_addrs seal_body_start seal_region_end;
      region_addrs seal_table_start seal_table_end;
      [fail_flag];
      region_addrs fail_start fail_end;
      region_addrs malloc_mem_start malloc_end;
      [malloc_memptr];
      region_addrs malloc_start malloc_memptr
      ]
}.

Program Definition int_client_prog `{memory_layout} : prog :=
  {| prog_start := interval_client_closure_start ;
     prog_end := interval_client_region_end ;
     prog_instrs := (interval_client_closure 2 0 offset_to_checki) ++ (check_interval 1);
     prog_size := _ |}.
Next Obligation.
  intros. pose proof (interval_client_closure_size) as HH.
  pose proof (interval_client_body_size) as HHH.
  rewrite app_length. solve_addr+HH HHH.
Qed.

Definition adv_prog `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.

(* MALLOC library entry *)
Definition malloc_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the malloc subroutine *)
  mkregion malloc_start malloc_memptr malloc_subroutine_instrs
  (* Capability to malloc's memory pool, used by the malloc subroutine *)
  ∪ list_to_map [(malloc_memptr, WCap RWX malloc_memptr malloc_end malloc_mem_start)]
  (* Malloc's memory pool, initialized to zero *)
  ∪ mkregion malloc_mem_start malloc_end (region_addrs_zeroes malloc_mem_start malloc_end).

Definition lib_entry_malloc `{memory_layout} : lib_entry :=
  {| lib_start := malloc_start ;
     lib_end := malloc_end ;
     lib_entrypoint := malloc_start ;
     lib_full_content := malloc_library_content |}.

(* FAIL library entry *)
Definition fail_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the failure subroutine *)
  (* tail contains pointer to the "failure" flag, set to 1 by the routine *)
  mkregion fail_start fail_end (assert_fail_instrs ++ [WCap RW fail_flag fail_flag_next fail_flag])
  ∪ list_to_map [(fail_flag, WInt 0%Z)] (* failure flag, initially set to 0 *).

Definition lib_entry_fail `{memory_layout} : lib_entry :=
  {| lib_start := fail_start ;
     lib_end := fail_end ;
     lib_entrypoint := fail_start ;
     lib_full_content := fail_library_content |}.

(* INTERVAL library entry *)
(* first we define the memory region of the nested seal library *)
Definition seal_library_content `{memory_layout} : gmap Addr Word :=
  mkregion seal_body_start seal_region_end (unseal_instrs ++ (seal_instrs 0) ++ (make_seal_preamble_instrs 0))
  ∪ list_to_map [(seal_region_start, WCap RO seal_table_start seal_table_end seal_table_start)]
  ∪ mkregion seal_table_start seal_table_end [WCap E malloc_start malloc_end malloc_start].

Definition interval_library_content `{memory_layout} : gmap Addr Word :=
  mkregion interval_closure_start interval_region_end ((interval_closure 0 1 offset_to_interval) ++ (interval 0))
  ∪ list_to_map [(interval_region_start, WCap RO int_table_start int_table_end int_table_start)]
  ∪ mkregion int_table_start int_table_end [WCap E malloc_start malloc_end malloc_start;
                                           WCap E seal_region_start seal_region_end seal_makeseal_entrypoint]
  ∪ seal_library_content.

Definition lib_entry_interval `{memory_layout} : lib_entry :=
  {| lib_start := interval_region_start ;
     lib_end := interval_region_end ;
     lib_entrypoint := interval_closure_start ;
     lib_full_content := interval_library_content |}.

(* full library *)
Definition library `{memory_layout} : lib :=
  {| priv_libs := [lib_entry_fail;lib_entry_interval] ;
     pub_libs := [lib_entry_malloc] |}.

Program Definition interval_client_table `{memory_layout} : @tbl_priv int_client_prog library :=
  {| prog_lower_bound := interval_client_region_start ;
     tbl_start := link_table_start ;
     tbl_end := link_table_end ;
     tbl_size := link_table_size ;
     tbl_prog_link := interval_client_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *. intros (_&Hd1&Hd2&Hd3&_).
  disjoint_map_to_list.
  assert (region_addrs interval_client_region_start interval_client_region_end =
          [interval_client_region_start] ++ region_addrs interval_client_closure_start interval_client_body_start
                                         ++ region_addrs interval_client_body_start interval_client_region_end) as ->;[|set_solver].
  pose proof interval_client_closure_size as Hs1.
  pose proof interval_client_body_size as Hs2.
  pose proof interval_client_region_start_offset as Hs3.
  rewrite (region_addrs_split interval_client_region_start interval_client_closure_start);[|solve_addr].
  rewrite region_addrs_single;[|solve_addr].
  rewrite (region_addrs_split interval_client_closure_start interval_client_body_start interval_client_region_end)//.
  solve_addr.
Qed.

Program Definition adv_table `{memory_layout} : @tbl_pub adv_prog library :=
  {| prog_lower_bound := adv_region_start ;
     tbl_start := adv_link_table_start ;
     tbl_end := adv_link_table_end ;
     tbl_size := adv_link_table_size ;
     tbl_prog_link := adv_region_start_offset ;
     tbl_disj := _
  |}.
Next Obligation.
  intros. simpl.
  pose proof (regions_disjoint) as Hdisjoint.
  rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
  disjoint_map_to_list. set_solver.
Qed.


Definition OK_invariant `{MachineParameters} `{memory_layout} (m : gmap Addr Word) : Prop :=
  ∀ w, m !! fail_flag = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} `{memory_layout} : gset Addr := {[ fail_flag ]}.

Program Definition OK_dom_correct `{MachineParameters} `{memory_layout} :
  ∀ m m',
    (∀ a, a ∈ OK_dom → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant m ↔ OK_invariant m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with fail_flag as [w [Hw1 Hw2] ]. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} `{memory_layout} : memory_inv :=
  {| minv := OK_invariant ;
     minv_dom := {[ fail_flag ]} ;
     minv_dom_correct := OK_dom_correct |}.

Lemma flag_inv_is_initial_memory `{memory_layout} m :
  is_initial_memory int_client_prog adv_prog library interval_client_table adv_table m →
  minv flag_inv m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs. rewrite map_union_empty in Hlibs.
  assert ((fail_library_content ∪ interval_library_content) ⊆ m) as Hfail'.
  { etrans;[|eauto]. apply map_union_subseteq_r. cbn in Hlibdisj.
    rewrite !map_union_empty in Hlibdisj. auto. }
  assert (fail_library_content ⊆ m) as Hfail.
  { etrans;[|eauto]. apply map_union_subseteq_l. }

  rewrite /fail_library_content in Hfail.
  assert (list_to_map [(fail_flag, WInt 0)] ⊆ m) as Hfail_flag.
  { etrans;[|eauto]. apply map_union_subseteq_r. disjoint_map_to_list.
    pose proof (regions_disjoint) as Hdisjoint.
    rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
    set_solver. }
  simpl in Hfail_flag.
  eapply (lookup_weaken _ _ fail_flag (WInt 0)) in Hfail_flag.
  by simplify_eq. by simplify_map_eq.
Qed.

Lemma flag_inv_sub `{memory_layout} :
  minv_dom flag_inv ⊆ dom (gset Addr) (lib_region (priv_libs library)).
Proof.
  cbn. rewrite map_union_empty.
  rewrite /fail_library_content.
  rewrite /= dom_union_L dom_union_L dom_insert_L dom_empty_L.
  rewrite union_empty_r. etrans. 2: apply union_subseteq_l. apply union_subseteq_r.
Qed.

Lemma flag_not_in_interval `{memory_layout} :
  ∀ (i : Addr) (x : Word), interval_library_content !! i = Some x → i ∉ minv_dom flag_inv.
Proof.
  intros i x Hin.
  rewrite /interval_library_content in Hin.
  simpl. apply not_elem_of_singleton_2.
  intros ->.
  rewrite lookup_union_r in Hin.
  { rewrite lookup_union_r in Hin.
    - match goal with
      | _ : mkregion ?X1 ?X2 ?X3 !! _ = _ |- _ => set l := mkregion X1 X2 X3
      end.
      assert (is_Some (l !! fail_flag))
        as Hdom%elem_of_gmap_dom;eauto.
      apply in_dom_mkregion in Hdom.
      pose proof (regions_disjoint) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
      set_solver.
    - apply lookup_union_None. split.
      + apply not_elem_of_dom. intros Hcontr%in_dom_mkregion.
        pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        set_solver.
      + simpl. destruct (decide (seal_region_start = fail_flag));simplify_map_eq;auto.
        exfalso.
        pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        set_solver. }
  { apply lookup_union_None. split;[apply lookup_union_None;split|].
    1,3: apply not_elem_of_dom;intros Hcontr%in_dom_mkregion.
    3: destruct (decide (interval_region_start = fail_flag));simplify_map_eq;auto;exfalso.
    all: pose proof (regions_disjoint) as Hdisjoint.
    1: rewrite (region_addrs_split _ interval_body_start) in Hcontr;
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH; solve_addr].
    1: apply elem_of_app in Hcontr as [Hcontr | Hcontr].
    all: rewrite !disjoint_list_cons in Hdisjoint |- *.
    all: intros (?&?&?&?&?&?&?&?&?).
    all: set_solver. }
Qed.

(* TODO: move to iris extra *)
Lemma big_sepM_to_big_sepL2 (PROP : bi) (A B : Type) `{EqDecision A} `{Countable A}
      (φ: A -> B -> PROP) (l1: list A) (l2: list B):
      NoDup l1 -> length l1 = length l2 →
      ⊢ (([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2) -∗
         ([∗ list] y1;y2 ∈ l1;l2, φ y1 y2))%I.
Proof.
  revert l2. iInduction (l1) as [|x l1] "IH"; iIntros (l2 Hnd Hlen) "H".
  - iSimpl. destruct l2;inversion Hlen. done.
  - destruct l2;inversion Hlen. simpl.
    inversion Hnd. subst.
    iDestruct (big_sepM_insert with "H") as "[A B]".
    + eapply not_elem_of_list_to_map.
      rewrite fst_zip; auto. lia.
    + iFrame. iApply ("IH" $! l2 H4 H1 with "B"); auto.
Qed.
Lemma map_filter_union :
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m1 m2 : M A),
      m1 ##ₘ m2 →
      filter P (m1 ∪ m2) = filter P m1 ∪ filter P m2.
Proof.
  intros. induction m1 using map_ind.
  - by rewrite map_filter_empty !map_empty_union.
  - apply map_disjoint_insert_l in H8 as [Hm2None Hdisj].
    destruct (decide (P (i,x))).
    + rewrite -insert_union_l !map_filter_insert// IHm1//.
      rewrite insert_union_l. auto.
    + rewrite map_filter_insert_not'//.
      2: intros; simplify_eq.
      rewrite -IHm1// -insert_union_l map_filter_insert_not'//.
      intros y Hy. rewrite lookup_union_r// in Hy. simplify_eq.
Qed.
Lemma map_filter_disjoint :
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m1 m2 : M A),
      m1 ##ₘ m2 →
      filter P m1 ##ₘfilter P m2.
Proof.
  intros. induction m1 using map_ind.
  - rewrite map_filter_empty. apply map_disjoint_empty_l.
  - apply map_disjoint_insert_l in H8 as [Hm2None Hdisj].
    destruct (decide (P (i,x))).
    + rewrite map_filter_insert//.
      apply map_disjoint_insert_l_2;auto.
      apply map_filter_lookup_None_2. left;auto.
    + rewrite map_filter_insert_not'//.
      2: intros; simplify_eq.
      apply IHm1;auto.
Qed.
Lemma map_filter_id :
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M
    → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m : M A),
      (∀ i x, m !! i = Some x → P (i, x)) → filter P m = m.
Proof.
  intros. apply map_eq.
  intros i. destruct (m !! i) eqn:Hsome.
  - apply map_filter_lookup_Some_2;auto.
  - apply map_filter_lookup_None_2;auto.
Qed.


Section int_client_adequacy.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {sealLLG: list_new.sealLLG Σ}
          `{memlayout: memory_layout}.

  Lemma int_client_correct :
    Forall (λ w, is_cap w = false) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom flag_inv) m in
  (∀ rmap,
      dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
      ⊢ inv invN (minv_sep flag_inv)
        ∗ na_own logrel_nais ⊤
        ∗ PC ↦ᵣ WCap RWX (prog_lower_bound interval_client_table) (prog_end int_client_prog) (prog_start int_client_prog)
        ∗ r_t0 ↦ᵣ WCap RWX (prog_lower_bound adv_table) (prog_end adv_prog) (prog_start adv_prog)
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
        (* P program and table *)
        ∗ (prog_lower_bound interval_client_table) ↦ₐ (WCap RO (tbl_start interval_client_table)
                                                            (tbl_end interval_client_table)
                                                            (tbl_start interval_client_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region interval_client_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region int_client_prog), a ↦ₐ w)
        (* Adv program and table *)
        ∗ (prog_lower_bound adv_table) ↦ₐ (WCap RO (tbl_start adv_table) (tbl_end adv_table) (tbl_start adv_table))
        ∗ ([∗ map] a↦w ∈ (tbl_region adv_table), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ (prog_region adv_prog), a ↦ₐ w)
        (* filtered entries *)
        ∗ ([∗ map] a↦w ∈ (lib_region (pub_libs library)), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ filtered_map (lib_region (priv_libs library)), a ↦ₐ w)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
  Proof.
    iIntros (Hints Hfilter rmap Hdom) "(#Hinv & Hown & HPC & Hr_adv & Hrmap & Hroe_link & Hroe_table & Hroe
                                 & Hadv_link & Hadv_table & Hadv & Hpubs & Hprivs)".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
    simpl. rewrite !map_union_empty.

    (* setting up client program (closure and body separate) *)
    iAssert (codefrag interval_client_closure_start (interval_client_closure 2 0 offset_to_checki)
            ∗ codefrag interval_client_body_start (check_interval 1))%I with "[Hroe] "as "[Hint_cls Hint]".
    { rewrite /prog_region.
      pose proof interval_client_closure_size as Hsize1.
      pose proof interval_client_body_size as Hsize2.
      iDestruct (mkregion_sepM_to_sepL2 with "Hroe") as "Hint".
      { simpl in *. solve_addr. }
      rewrite (region_addrs_split _ interval_client_body_start);[|simpl in *;solve_addr].
      iDestruct (big_sepL2_app' with "Hint") as "[Hint_cls Hint]".
      { rewrite region_addrs_length /region_size. simpl in *. solve_addr. }
      rewrite /codefrag. rewrite /incr_addr_default Hsize1 Hsize2 /=. iFrame. }

    (* cleaning up the environment tables *)
    rewrite /tbl_region /mkregion /=.
    pose proof link_table_size as Hsize.
    assert (is_Some (link_table_start + 1)%a) as [link_table_mid Hmid]. solve_addr+Hsize.
    assert (is_Some (link_table_start + 2)%a) as [link_table_mid' Hmid']. solve_addr+Hsize.
    assert (link_table_mid + 1 = Some link_table_mid')%a as Hmid''. solve_addr+Hmid Hmid'.
    rewrite region_addrs_cons;[|solve_addr +Hsize].
    rewrite region_addrs_cons;[|solve_addr +Hsize].
    rewrite Hmid /= region_addrs_single /=;[|solve_addr +Hmid Hsize].
    pose proof adv_link_table_size as Hsize_adv.
    rewrite region_addrs_single /=;[|solve_addr +Hsize_adv].
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_start Hroe_table]".
    { rewrite lookup_insert_ne//. 2: solve_addr +Hmid Hmid'.
      rewrite lookup_insert_ne//. solve_addr +Hmid Hmid'. }
    rewrite Hmid''. iSimpl in "Hroe_table".
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_mid Htable]";auto.
    { rewrite lookup_insert_ne//. solve_addr. }
    iDestruct (big_sepM_insert with "Htable") as "[Hlink_table_mid' _]";auto.
    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start _]";auto.

    (* allocate malloc invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv malloc_start malloc_end)
            with "[Hpubs]") as "#Hinv_malloc".
    { iNext. rewrite /malloc_inv. iExists malloc_memptr, malloc_mem_start.
      rewrite /malloc_library_content.
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hinit]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        disjoint_map_to_list. set_solver. }
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hmid]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?).
        disjoint_map_to_list. set_solver. }
      pose proof malloc_code_size as Hmalloc_size.
      pose proof malloc_memptr_size as Hmalloc_memptr_size.
      pose proof malloc_mem_size as Hmalloc_mem_size.
      iSplitL "Hpubs".
      iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
      rewrite region_addrs_length /region_size.  solve_addr +Hmalloc_size.
      assert ((malloc_start ^+ length malloc_subroutine_instrs)%a = malloc_memptr) as ->
      ;[solve_addr+Hmalloc_size|iFrame].
      iSplit;[auto|]. iDestruct (big_sepM_insert with "Hmid") as "[$ _]";auto.
      iSplit;[|iPureIntro;solve_addr+Hmalloc_size Hmalloc_memptr_size Hmalloc_mem_size].
      iApply big_sepM_to_big_sepL2. apply region_addrs_NoDup.
      rewrite region_addrs_length replicate_length /region_size. solve_addr +Hmalloc_mem_size. iFrame. }
    iDestruct (simple_malloc_subroutine_valid with "[$Hinv_malloc]") as "#Hmalloc_val".

    (* allocate adversary table *)
    iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
            with "[Hadv_link_table_start]") as "#Hadv_table_valid".
    { iNext. iExists _. iFrame. auto. }

    (* allocate validity of adversary *)
    pose proof adv_size as Hadv_size'.
    pose proof adv_region_start_offset as Hadv_region_offset.
    iDestruct (big_sepM_to_big_sepL2 with "Hadv") as "Hadv /=". apply region_addrs_NoDup.
    rewrite region_addrs_length /region_size /=. solve_addr+Hadv_size'.
    iMod (region_inv_alloc _ (region_addrs adv_region_start adv_end) (_::adv_instrs) with "[Hadv Hadv_link]") as "#Hadv".
    { rewrite (region_addrs_cons adv_region_start);[rewrite Hadv_region_offset /=|solve_addr +Hadv_region_offset Hadv_size'].
      iFrame. iSplit.
      { iApply fixpoint_interp1_eq. iSimpl. iClear "∗".
        rewrite region_addrs_single// /=. iSplit;[|done].
        iExists interp. iFrame "Hadv_table_valid". auto. }
      iApply big_sepL2_sep. iFrame. iApply big_sepL2_to_big_sepL_r.
      rewrite region_addrs_length /region_size /=. solve_addr+Hadv_size'.
      iApply big_sepL_forall. iIntros (k n Hin).
      revert Hints; rewrite Forall_forall =>Hints.
      assert (n ∈ adv_instrs) as HH%Hints;[apply elem_of_list_lookup;eauto|]. destruct n;inversion HH.
      iApply fixpoint_interp1_eq;eauto. }

    iAssert (interp (WCap RWX adv_region_start adv_end adv_start)) as "#Hadv_valid".
    { iClear "∗". iApply fixpoint_interp1_eq. iSimpl.
      iDestruct (big_sepL2_to_big_sepL_l with "Hadv") as "Hadv'".
      { rewrite region_addrs_length /region_size. solve_addr+Hadv_region_offset Hadv_size'. }
      iApply (big_sepL_mono with "Hadv'").
      iIntros (k y Hin) "Hint". iExists interp. iFrame. auto. }

    (* extract interval library from priv *)
    rewrite /Hfilter /=.
    assert (fail_library_content ##ₘ interval_library_content) as Hdisj.
    { rewrite /fail_library_content /interval_library_content.
      pose proof (regions_disjoint) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint |- *. intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      rewrite map_disjoint_union_l !map_disjoint_union_r. repeat split;disjoint_map_to_list.
      rewrite (region_addrs_split interval_closure_start interval_body_start). set_solver.
      pose proof interval_closure_size as HH.
      pose proof interval_body_size as HHH. solve_addr +HH HHH.
      1,2,3,4,5: set_solver.
      rewrite (region_addrs_split interval_closure_start interval_body_start). set_solver.
      pose proof interval_closure_size as HH.
      pose proof interval_body_size as HHH. solve_addr +HH HHH.
      all: set_solver. }
    rewrite map_filter_union; [|auto].
    iDestruct (big_sepM_union with "Hprivs") as "[_ Hprivs]".
    { eapply map_filter_disjoint;auto. apply _. }
    rewrite map_filter_id. 2: apply flag_not_in_interval.

    (* cleanup the content of the interval library *)
    rewrite /interval_library_content /seal_library_content.
    iDestruct (big_sepM_union with "Hprivs") as "[Hinterval_cls Hprivs]".
    { rewrite !map_disjoint_union_l !map_disjoint_union_r. repeat split.
      all: try disjoint_map_to_list.
      1,2,3: rewrite (region_addrs_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }

    iDestruct (big_sepM_union with "Hinterval_cls") as "[Hinterval_cls Hint_table]".
    { rewrite !map_disjoint_union_l. repeat split.
      all: try disjoint_map_to_list.
      1: rewrite (region_addrs_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        intros (?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }
    iDestruct (big_sepM_union with "Hinterval_cls") as "[Hinterval_cls Hinterval_link]".
    { disjoint_map_to_list.
      rewrite (region_addrs_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        intros (?&?&?&?&?&?&?&?&?&?).
      set_solver. }
    iDestruct (mkregion_sepM_to_sepL2 with "Hinterval_cls") as "Hinterval".
    { pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    rewrite (region_addrs_split interval_closure_start interval_body_start); cycle 1.
    { pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    iDestruct (big_sepL2_app' with "Hinterval") as "[Hinterval_cls Hinterval]".
    { rewrite /= region_addrs_length /region_size.
      pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    iDestruct (mkregion_sepM_to_sepL2 with "Hint_table") as "Hint_table".
    { pose proof int_table_size. auto. }
    assert (is_Some (int_table_start + 1)%a) as [int_table_mid Hint_table_mid].
    { pose proof int_table_size. solve_addr. }
    rewrite (region_addrs_cons int_table_start);cycle 1.
    { pose proof int_table_size. solve_addr. }
    rewrite Hint_table_mid. iSimpl in "Hint_table".
    assert (int_table_mid + 1 = Some int_table_end)%a as Hint_table_mid'.
    { pose proof int_table_size as HH. solve_addr+HH Hint_table_mid. }
    rewrite (region_addrs_cons int_table_mid);cycle 1.
    { solve_addr. }
    rewrite Hint_table_mid'. iSimpl in "Hint_table".
    iDestruct "Hint_table" as "(Hint_table_start & Hint_table_mid & _)".
    iSimpl in "Hinterval_link". iDestruct (big_sepM_insert with "Hinterval_link") as "[Hinterval_link _]";[auto|].

    (* cleanup the content of the nested seal library *)
    iDestruct (big_sepM_union with "Hprivs") as "[Hprivs Hseal_table]".
    { rewrite map_disjoint_union_l. split.
      all: disjoint_map_to_list.
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        intros (?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }
    iDestruct (big_sepM_union with "Hprivs") as "[Hseal Hseal_link]".
    { disjoint_map_to_list.
      pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        intros (?&?&?&?&?&?&?&?&?&?).
      set_solver. }
    iDestruct (big_sepM_insert with "Hseal_link") as "[Hseal_link _]";[auto|]. iSimpl in "Hseal_link".
    iDestruct (mkregion_sepM_to_sepL2 with "Hseal_table") as "Hseal_table".
    { pose proof seal_table_size. auto. }
    rewrite (region_addrs_single seal_table_start);cycle 1.
    { pose proof seal_table_size. auto. }
    iDestruct "Hseal_table" as "[Hseal_table _]".
    iAssert (codefrag interval_closure_start (interval_closure 0 1 offset_to_interval)) with "[Hinterval_cls]" as "Hinterval_cls".
    { rewrite /codefrag /incr_addr_default interval_closure_size. iFrame. }
    iAssert (codefrag seal_body_start (_)) with "[Hseal]" as "Hseal".
    { rewrite /codefrag /incr_addr_default. erewrite seal_size. iFrame.
      iDestruct (mkregion_sepM_to_sepL2 with "Hseal") as "$". apply seal_size. }
    iAssert (codefrag interval_body_start (interval 0)) with "[Hinterval]" as "Hinterval".
    { rewrite /codefrag /incr_addr_default interval_body_size. iFrame. }

    (* We apply the client specification *)
    assert (is_Some (interval_client_closure_start + interval_client_closure_move_offset)%a) as [? HH].
    { destruct ((interval_client_closure_start + interval_client_closure_move_offset)%a) eqn:Hsome;eauto. exfalso.
      rewrite /interval_client_closure_move_offset in Hsome. pose proof interval_client_closure_size. solve_addr. }
    assert (is_Some (interval_closure_start + interval_closure_move_offset)%a) as [? HHH].
    { destruct (interval_closure_start + interval_closure_move_offset)%a eqn:hsome;eauto. exfalso.
      rewrite /interval_closure_move_offset in hsome. pose proof interval_closure_size. solve_addr. }
    iDestruct (interval_client_closure_functional_spec with "[- Hown HPC Hr_adv Hrmap]") as "Hcont".
    16: { iFrame "Hint_cls Hint Hinterval_cls Hinterval Hseal".
          iFrame "Hinv_malloc Hroe_link". iFrame "Hlink_table_mid".
          iFrame "Hlink_table_mid' Hlink_table_start".
      iFrame "Hint_table_start Hseal_link Hinterval_link". iFrame.
      rewrite /incr_addr_default seal_makeseal_entrypoint_correct.
      iFrame "Hint_table_mid". }
    instantiate (1:=RWX). 2: instantiate (1:=RWX). 1,2:apply ExecPCPerm_RWX.
    { instantiate (1:=interval_client_region_end).
      pose proof interval_client_closure_size. pose proof interval_client_body_size.
      pose proof interval_client_region_start_offset. simpl in *. rewrite /SubBounds. solve_addr. }
    { pose proof interval_client_closure_size. pose proof interval_client_body_size.
      pose proof interval_client_region_start_offset. simpl in *. rewrite /SubBounds. solve_addr. }
    { rewrite /int_bounds.
      pose proof interval_closure_size. pose proof interval_body_size.
      pose proof interval_region_start_offset.
      pose proof seal_size.
      pose proof seal_region_start_offset.
      simpl in *. rewrite /SubBounds. solve_addr. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid'. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid'. }
    all: auto.
    { solve_addr. }
    { rewrite /int_table. repeat split;auto.
      1,2: apply le_addr_withinBounds'. all: try solve_addr.
      apply seal_table_size. }
    { eauto. }
    { rewrite /offset_to_checki. pose proof interval_client_closure_size.
      rewrite /interval_client_closure_move_offset in HH.
      rewrite /interval_client_closure_move_offset /interval_client_closure_instrs_length.
      simpl in *. solve_addr. }
    { split;eauto. rewrite /offset_to_interval /interval_closure_instrs_length /interval_closure_move_offset.
      rewrite /interval_closure_move_offset in HHH. pose proof interval_closure_size. solve_addr. }

    (* next we use wp_wand and assert the register state is valid *)
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr_adv]") as "Hrmap".
    { apply not_elem_of_dom. rewrite Hdom. set_solver+. }
    iDestruct (big_sepM_insert _ _ PC with "[$Hrmap $HPC]") as "Hrmap".
    { apply not_elem_of_dom. rewrite dom_insert_L Hdom. set_solver+. }
    rewrite -(insert_insert _ PC _ (WInt 0)).
    iDestruct ("Hcont" with "[$Hown $Hrmap]") as "Hcont".
    { rewrite /interp_reg /=. iSplit.
      iPureIntro. intros. simpl. apply elem_of_gmap_dom. rewrite !dom_insert_L Hdom.
      pose proof (all_registers_s_correct x1) as Hx1. set_solver +Hx1.
      iIntros (r v Hrv). rewrite lookup_insert_ne//.
      destruct (decide (r_t0 = r));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
      iIntros (Heq);inversion Heq. auto.
      iIntros (Hin). iDestruct (big_sepM_lookup _ _ r with "Hrmapvalid") as %Hncap;[apply Hin|].
      destruct v;inversion Hncap. iApply fixpoint_interp1_eq. eauto. }

    iApply (wp_wand with "Hcont"). auto.
  Qed.

End int_client_adequacy.

Theorem template_adequacy `{memory_layout}
    (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory int_client_prog adv_prog library interval_client_table adv_table m →
  is_initial_registers int_client_prog adv_prog library interval_client_table adv_table reg r_t0 →
  Forall (λ w, is_cap w = false) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! fail_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? Hints ?.
  pose proof (template_adequacy (GFunctor (authUR (monotoneUR list_new.prefR))) (* The extra resource needed by seal library *)
                                int_client_prog adv_prog library interval_client_table adv_table flag_inv) as Hadequacy.
  eapply Hadequacy;eauto.
  { apply flag_inv_is_initial_memory. auto. }
  { apply flag_inv_sub. }
  intros Σ ? ? ? ?.
  eapply int_client_correct. apply Hints. Unshelve. solve_inG.
Qed.
