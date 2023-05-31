From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental proofmode.
From cap_machine.examples Require Import addr_reg_sample malloc salloc macros_new
     interval_client_closure_arch interval_client_arch interval_closure_arch arch_sealing.
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
                          (length (interval_client_closure 3 0 offset_to_checki))
                                 = Some interval_client_body_start)%a;
  interval_client_body_size : (interval_client_body_start +
                               (length (check_interval 2))
                               = Some interval_client_region_end)%a ;
  interval_client_region_start_offset: (interval_client_region_start + 1)%a
                                       = Some interval_client_closure_start;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 4)%a = Some link_table_end;

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
    (adv_link_table_start + 2)%a = Some adv_link_table_end;

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
               length (unseal_instrs ++ seal_instrs ++ (make_seal_preamble_instrs 0 1))
               = Some seal_region_end)%a;
  seal_makeseal_entrypoint : Addr;
  seal_makeseal_entrypoint_correct :
    (seal_body_start + ((length unseal_instrs) + (length seal_instrs)) = Some seal_makeseal_entrypoint)%a;
  seal_region_start_offset: (seal_region_start + 1 = Some seal_body_start)%a;

  (* seal table *)
  seal_table_start : Addr;
  seal_table_end : Addr;
  seal_table_size : (seal_table_start + 2 = Some seal_table_end)%a;

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

  (* salloc routine - note: the available memory consists of a single otype pointer `salloc_optr` *)
  salloc_start : Addr;
  salloc_memptr : Addr;
  salloc_optr : Addr;
  salloc_end : Addr;

  salloc_code_size :
    (salloc_start + length salloc_subroutine_instrs)%a
    = Some salloc_memptr;

  salloc_memptr_size :
    (salloc_memptr + 1)%a = Some salloc_optr;

  salloc_optr_size :
    (salloc_optr + 1)%a = Some salloc_end;

  (* Define range of otypes to be allocated *)
  salloc_o_b : OType;
  salloc_o_e : OType;
  salloc_o_lt : (salloc_o_b <= salloc_o_e)%ot;

  (* assert routine *)
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

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
      (* components *)
      finz.seq_between adv_region_start adv_end;
      [interval_client_region_start];
      finz.seq_between interval_client_closure_start interval_client_body_start;
      finz.seq_between interval_client_body_start interval_client_region_end;
      (* tables *)
      finz.seq_between link_table_start link_table_end;
      finz.seq_between adv_link_table_start adv_link_table_end;
      (* libraries *)
      [interval_region_start];
      finz.seq_between interval_closure_start interval_body_start;
      finz.seq_between interval_body_start interval_region_end;
      finz.seq_between int_table_start int_table_end;
      [seal_region_start];
      finz.seq_between seal_body_start seal_region_end;
      finz.seq_between seal_table_start seal_table_end;
      finz.seq_between malloc_mem_start malloc_end;
      [malloc_memptr];
      finz.seq_between malloc_start malloc_memptr;
      [salloc_optr];
      [salloc_memptr];
      finz.seq_between salloc_start salloc_memptr;
      [assert_flag];
      [assert_cap];
      finz.seq_between assert_start assert_cap
      ]
}.

Program Definition int_client_prog `{memory_layout} : prog :=
  {| prog_start := interval_client_closure_start ;
     prog_end := interval_client_region_end ;
     prog_instrs := (interval_client_closure 3 0 offset_to_checki) ++ (check_interval 2);
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

(* SALLOC library entry *)
Definition salloc_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the salloc subroutine *)
  mkregion salloc_start salloc_memptr salloc_subroutine_instrs
  (* Capability to salloc's otype pool, used by the salloc subroutine + capability for otypes itself *)
  ∪ list_to_map [(salloc_memptr, WCap RWX salloc_optr salloc_end salloc_optr); (salloc_optr, WSealRange (true, true) salloc_o_b salloc_o_e salloc_o_b)].

Definition lib_entry_salloc `{memory_layout} : lib_entry :=
  {| lib_start := salloc_start ;
     lib_end := salloc_end ;
     lib_entrypoint := salloc_start ;
     lib_full_content := salloc_library_content |}.

(* assert library entry *)
Definition assert_library_content `{memory_layout} : gmap Addr Word :=
  (* code for the failure subroutine *)
  mkregion assert_start assert_cap assert_subroutine_instrs
  (* capability to the assert flag *)
  ∪ list_to_map [(assert_cap, WCap RW assert_flag assert_end assert_flag)]
 (* assert flag, initially set to 0 *)
  ∪ list_to_map [(assert_flag, WInt 0%Z)].

Definition lib_entry_fail `{memory_layout} : lib_entry :=
  {| lib_start := assert_start ;
     lib_end := assert_end ;
     lib_entrypoint := assert_start ;
     lib_full_content := assert_library_content |}.

(* INTERVAL library entry *)
(* first we define the memory region of the nested seal library *)
Definition seal_library_content `{memory_layout} : gmap Addr Word :=
  mkregion seal_body_start seal_region_end (unseal_instrs ++ seal_instrs ++ (make_seal_preamble_instrs 0 1))
  ∪ list_to_map [(seal_region_start, WCap RO seal_table_start seal_table_end seal_table_start)]
  ∪ mkregion seal_table_start seal_table_end [WCap E malloc_start malloc_end malloc_start; WCap E salloc_start salloc_end salloc_start].

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

(* full library: includes malloc and salloc - note that not all of these are needed for the client code, but now we only need to define one library *)
Definition library `{memory_layout} : lib :=
  {| priv_libs := [lib_entry_fail;lib_entry_interval] ;
     pub_libs := [lib_entry_malloc;lib_entry_salloc] |}.

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
  rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (_&Hd1&Hd2&Hd3&_).
  disjoint_map_to_list.
  assert (finz.seq_between interval_client_region_start interval_client_region_end =
          [interval_client_region_start] ++ finz.seq_between interval_client_closure_start interval_client_body_start
                                         ++ finz.seq_between interval_client_body_start interval_client_region_end) as ->;[|set_solver].
  pose proof interval_client_closure_size as Hs1.
  pose proof interval_client_body_size as Hs2.
  pose proof interval_client_region_start_offset as Hs3.
  rewrite (finz_seq_between_split interval_client_region_start interval_client_closure_start);[|solve_addr].
  rewrite finz_seq_between_singleton;[|solve_addr].
  rewrite (finz_seq_between_split interval_client_closure_start interval_client_body_start interval_client_region_end)//.
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
  rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
  disjoint_map_to_list. set_solver.
Qed.


Definition OK_invariant `{MachineParameters} `{memory_layout} (m : gmap Addr Word) : Prop :=
  ∀ w, m !! assert_flag = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} `{memory_layout} : gset Addr := {[ assert_flag ]}.

Program Definition OK_dom_correct `{MachineParameters} `{memory_layout} :
  ∀ m m',
    (∀ a, a ∈ OK_dom → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant m ↔ OK_invariant m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with assert_flag as [w [Hw1 Hw2] ]. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} `{memory_layout} : memory_inv :=
  {| minv := OK_invariant ;
     minv_dom := {[ assert_flag ]} ;
     minv_dom_correct := OK_dom_correct |}.

Lemma flag_inv_is_initial_memory `{memory_layout} m :
  is_initial_memory int_client_prog adv_prog library interval_client_table adv_table m →
  minv flag_inv m.
Proof.
  intros Hinit. intros a Hin.
  destruct Hinit as (?&?&Hlibs&?&?&?&Hlibdisj).
  cbn in Hlibs. rewrite map_union_empty in Hlibs.
  assert ((assert_library_content ∪ interval_library_content) ⊆ m) as Hfail'.
  { etrans;[| apply Hlibs].
    rewrite map_union_assoc.
    apply map_union_subseteq_r'; [|done]. cbn in Hlibdisj.
    rewrite !map_union_empty in Hlibdisj. auto. }
  assert (assert_library_content ⊆ m) as Hfail.
  { etrans;[|eauto]. apply map_union_subseteq_l. }

  rewrite /assert_library_content in Hfail.
  assert (list_to_map [(assert_flag, WInt 0)] ⊆ m) as Hassert_flag.
  { etrans;[|eauto]. apply map_union_subseteq_r. disjoint_map_to_list.
    apply elem_of_disjoint. intro. rewrite elem_of_app !elem_of_finz_seq_between !elem_of_list_singleton.
    pose proof assert_code_size. pose proof assert_cap_size.
    pose proof assert_flag_size. intros [ [? ?]|?] ->; solve_addr. }
  simpl in Hassert_flag.
  eapply (lookup_weaken _ _ assert_flag (WInt 0)) in Hassert_flag.
  by simplify_eq. by simplify_map_eq.
Qed.

Lemma flag_inv_sub `{memory_layout} :
  minv_dom flag_inv ⊆ dom (lib_region (priv_libs library)).
Proof.
  cbn. rewrite map_union_empty.
  rewrite /assert_library_content.
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
      assert (is_Some (l !! assert_flag))
        as Hdom%elem_of_dom;eauto.
      apply in_dom_mkregion in Hdom.
      pose proof (regions_disjoint) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
      set_solver.
    - apply lookup_union_None. split.
      + apply not_elem_of_dom. intros Hcontr%in_dom_mkregion.
        pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
        set_solver.
      + simpl. destruct (decide (seal_region_start = assert_flag));simplify_map_eq;auto.
        exfalso.
        pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
        set_solver. }
  { apply lookup_union_None. split;[apply lookup_union_None;split|].
    1,3: apply not_elem_of_dom;intros Hcontr%in_dom_mkregion.
    3: destruct (decide (interval_region_start = assert_flag));simplify_map_eq;auto;exfalso.
    all: pose proof (regions_disjoint) as Hdisjoint.
    1: rewrite (finz_seq_between_split _ interval_body_start) in Hcontr;
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH; solve_addr].
    1: apply elem_of_app in Hcontr as [Hcontr | Hcontr].
    all: rewrite !disjoint_list_cons in Hdisjoint.
    all: destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
    all: set_solver. }
Qed.

Section int_client_adequacy.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealg:sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{memlayout: memory_layout}.

  (* Note that this tactic can only be applied on the left of the disjointness condition *)
  Ltac union_resolve_mkregion :=
    repeat (
      try lazymatch goal with
          | |- _ ∪ _ ⊆ _ =>
            etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
          end;
      [ first [ apply dom_mkregion_incl | reflexivity ] |..]
    ).

  (* overwrite `disjoint_map_to_list` ltac to also simplify list_to_map occurrences *)
  (* TODO: replace original *)
  Ltac disjoint_map_to_list :=
    rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
    eapply disjoint_mono_l;
    rewrite ?dom_list_to_map_singleton;
    union_resolve_mkregion;
    try match goal with |- _ ## dom (mkregion _ _ _) =>
      eapply disjoint_mono_r; [ apply dom_mkregion_incl | ] end;
    try match goal with |- _ ## dom (list_to_map _ ) =>
    rewrite dom_list_to_map_L end;
    rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
    apply stdpp_extra.list_to_set_disj.

  Lemma int_client_correct :
    Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) adv_instrs →
    let filtered_map := λ (m : gmap Addr Word), filter (fun '(a, _) => a ∉ minv_dom flag_inv) m in
  (∀ rmap,
      dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
      ⊢ inv invN (minv_sep flag_inv)
        ∗ na_own logrel_nais ⊤
        ∗ PC ↦ᵣ WCap RWX (prog_lower_bound interval_client_table) (prog_end int_client_prog) (prog_start int_client_prog)
        ∗ r_t0 ↦ᵣ WCap RWX (prog_lower_bound adv_table) (prog_end adv_prog) (prog_start adv_prog)
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_z w = true⌝)
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
        (* Right to allocate sealed predicates *)
        ∗ ([∗ list] o ∈ finz.seq_between salloc_o_b salloc_o_e, can_alloc_pred o)
        (* filtered entries *)
        ∗ ([∗ map] a↦w ∈ (lib_region (pub_libs library)), a ↦ₐ w)
        ∗ ([∗ map] a↦w ∈ filtered_map (lib_region (priv_libs library)), a ↦ₐ w)

        -∗ WP Seq (Instr Executable) {{ λ _, True }}).
  Proof.
    iIntros (Hints Hfilter rmap Hdom) "(#Hinv & Hown & HPC & Hr_adv & Hrmap & Hroe_link & Hroe_table & Hroe
                                 & Hadv_link & Hadv_table & Hadv & Hseal_alloc & Hpubs & Hprivs)".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmapvalid]".
    simpl. rewrite !map_union_empty.

    (* setting up client program (closure and body separate) *)
    iAssert (codefrag interval_client_closure_start (interval_client_closure 3 0 offset_to_checki)
            ∗ codefrag interval_client_body_start (check_interval 2))%I with "[Hroe] "as "[Hint_cls Hint]".
    { rewrite /prog_region.
      pose proof interval_client_closure_size as Hsize1.
      pose proof interval_client_body_size as Hsize2.
      iDestruct (mkregion_sepM_to_sepL2 with "Hroe") as "Hint".
      { simpl in *. solve_addr. }
      rewrite (finz_seq_between_split _ interval_client_body_start);[|simpl in *;solve_addr].
      iDestruct (big_sepL2_app' with "Hint") as "[Hint_cls Hint]".
      { rewrite finz_seq_between_length /finz.dist. simpl in *. solve_addr. }
      rewrite /codefrag. rewrite (addr_incr_eq Hsize1) (addr_incr_eq Hsize2) /=. iFrame. }

    (* cleaning up the environment tables *)
    (* first for the client *)
    rewrite /tbl_region /mkregion /=.
    pose proof link_table_size as Hsize.
    assert (is_Some (link_table_start + 1)%a) as [link_table_mid Hmid]. solve_addr+Hsize.
    assert (is_Some (link_table_start + 2)%a) as [link_table_mid' Hmid']. solve_addr+Hsize.
    assert (is_Some (link_table_start + 3)%a) as [link_table_mid'' Hmid'']. solve_addr+Hsize.
    assert (link_table_mid + 1 = Some link_table_mid')%a as Hmidd. solve_addr+Hmid Hmid'.
    assert (link_table_mid' + 1 = Some link_table_mid'')%a as Hmidd'. solve_addr+Hmid' Hmid''.
    do 3 (rewrite finz_seq_between_cons;[|solve_addr +Hsize]).
    rewrite (addr_incr_eq Hmid) /= finz_seq_between_singleton /=;[|solve_addr +Hmid Hsize]. rewrite (addr_incr_eq Hmidd).

    (* then for the adversary *)
    pose proof adv_link_table_size as Hsize_adv.
    assert (is_Some (adv_link_table_start + 1)%a) as [adv_link_table_mid Hmid_adv]. solve_addr+Hsize_adv.
    rewrite finz_seq_between_cons;[|solve_addr +Hsize_adv].
    rewrite finz_seq_between_singleton /=;[|solve_addr +Hsize_adv].
    rewrite (addr_incr_eq Hmid_adv).

    (* now get individual pointers out *)
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_start Hroe_table]".
    { rewrite lookup_insert_ne//. 2: solve_addr +Hmid.
      rewrite lookup_insert_ne//. 2: solve_addr +Hmid'.
      rewrite lookup_insert_ne//. solve_addr +Hmid'. }
    rewrite (addr_incr_eq Hmidd'). iSimpl in "Hroe_table".
    iDestruct (big_sepM_insert with "Hroe_table") as "[Hlink_table_mid Htable]".
    { rewrite lookup_insert_ne//. 2: solve_addr +Hmidd.
      rewrite lookup_insert_ne//. solve_addr + Hmidd Hmidd'. }
    iDestruct (big_sepM_insert with "Htable") as "[Hlink_table_mid' Htable]".
    { rewrite lookup_insert_ne//. solve_addr +Hmidd'. }
    iDestruct (big_sepM_insert with "Htable") as "[Hlink_table_mid'' _]";auto.

    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start Hadv_table]".
    { rewrite lookup_insert_ne//. solve_addr. }
    iDestruct (big_sepM_insert with "Hadv_table") as "[Hadv_link_table_start' _]";auto.

    (* split malloc and salloc *)
    iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hsalloc]".
    { pose proof (regions_disjoint) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint.
      destruct Hdisjoint as (_&_&_&_&_&_&_&_&_&_&_&_&_&?&?&?&?&?&?&_).
      rewrite /malloc_library_content /salloc_library_content.
      rewrite !map_disjoint_union_r; repeat split; disjoint_map_to_list; set_solver.
    }

    (* allocate malloc invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv malloc_start malloc_end)
            with "[Hpubs]") as "#Hinv_malloc".
    { iNext. rewrite /malloc_inv. iExists malloc_memptr, malloc_mem_start.
      rewrite /malloc_library_content.
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hinit]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint.
        disjoint_map_to_list. set_solver. }
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hmid]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint.
        disjoint_map_to_list. set_solver. }
      pose proof malloc_code_size as Hmalloc_size.
      pose proof malloc_memptr_size as Hmalloc_memptr_size.
      pose proof malloc_mem_size as Hmalloc_mem_size.
      iSplitL "Hpubs".
      iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
      rewrite finz_seq_between_length /finz.dist.  solve_addr +Hmalloc_size.
      assert ((malloc_start ^+ length malloc_subroutine_instrs)%a = malloc_memptr) as ->
      ;[solve_addr+Hmalloc_size|iFrame].
      iSplit;[auto|]. iDestruct (big_sepM_insert with "Hmid") as "[$ _]";auto.
      iSplit;[|iPureIntro;solve_addr+Hmalloc_size Hmalloc_memptr_size Hmalloc_mem_size].
      iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
      rewrite finz_seq_between_length replicate_length /finz.dist. solve_addr +Hmalloc_mem_size. iFrame. }
    iDestruct (simple_malloc_subroutine_valid with "[$Hinv_malloc]") as "#Hmalloc_val".

    iRename "Hsalloc" into "Hpubs".
    (* allocate salloc invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ sallocN (salloc_inv salloc_start salloc_end)
            with "[Hpubs Hseal_alloc]") as "#Hinv_salloc".
    { iNext. rewrite /salloc_inv. iExists salloc_o_b, salloc_o_b, salloc_o_e, salloc_memptr, salloc_optr.
      rewrite /salloc_library_content.
      iDestruct (big_sepM_union with "Hpubs") as "[Hpubs Hinit]".
      { pose proof (regions_disjoint) as Hdisjoint.
        rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?).
        disjoint_map_to_list. set_solver. }

      iDestruct (big_sepM_delete _ _ salloc_memptr with "Hinit") as "[Hsa_mptr Hinit]";[ simplify_map_eq; auto |].
      assert (salloc_memptr ≠ salloc_optr) as Hne. {
          pose proof (regions_disjoint) as Hdisjoint.
          rewrite !disjoint_list_cons in Hdisjoint.
          destruct Hdisjoint as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hne&_&_).
          set_solver+Hne.
      }
      iDestruct (big_sepM_delete _ _ salloc_optr with "Hinit") as "[Hsa_optr _]".
      { rewrite delete_insert; simplify_map_eq; auto. }

      pose proof salloc_code_size as Hsalloc_size.
      pose proof salloc_memptr_size as Hsalloc_memptr_size.
      pose proof salloc_optr_size as Hsalloc_optr_size.
      pose proof salloc_o_lt as Hsalloc_o_lt.
      iFrame "∗ %".
      iSplitL "Hpubs".
      { iApply big_sepM_to_big_sepL2. apply finz_seq_between_NoDup.
        rewrite finz_seq_between_length /finz.dist.  solve_addr +Hsalloc_size.
        assert ((salloc_start ^+ length salloc_subroutine_instrs)%a = salloc_memptr) as ->
        ;[solve_addr+Hsalloc_size|iFrame]. }
      solve_addr.
   }
    iDestruct (simple_salloc_subroutine_valid with "[$Hinv_salloc]") as "#Hsalloc_val".

    (* allocate adversary table: entry for malloc and entry for salloc *)
    iMod (inv_alloc (logN .@ adv_link_table_start) ⊤ (interp_ref_inv adv_link_table_start interp)
            with "[Hadv_link_table_start]") as "#Hadv_table_valid".
    { iNext. iExists _. iFrame. auto. }
    iMod (inv_alloc (logN .@ adv_link_table_mid) ⊤ (interp_ref_inv adv_link_table_mid interp)
            with "[Hadv_link_table_start']") as "#Hadv_table_valid'".
    { iNext. iExists _. iFrame. auto. }

    (* allocate validity of adversary *)
    pose proof adv_size as Hadv_size'.
    pose proof adv_region_start_offset as Hadv_region_offset.
    iDestruct (big_sepM_to_big_sepL2 with "Hadv") as "Hadv /=". apply finz_seq_between_NoDup.
    rewrite finz_seq_between_length /finz.dist /=. solve_addr+Hadv_size'.

    iAssert (|={⊤}=> interp (WCap RWX adv_start adv_end adv_start))%I with "[Hadv]" as ">#Hadv".
    { iApply (region_valid_in_region _ _ _ _ adv_instrs);auto.
      apply Forall_forall. intros. set_solver+. }
    iAssert (|={⊤}=> interp (WCap RWX adv_region_start adv_end adv_start))%I with "[Hadv_link]" as ">#Hadv_valid".
    { iApply fixpoint_interp1_eq. iSimpl.
      rewrite (finz_seq_between_cons adv_region_start);
        [rewrite (addr_incr_eq Hadv_region_offset) /=|solve_addr +Hadv_region_offset Hadv_size'].
      iSplitL.
      - iExists interp. iSplitL;[|iModIntro;auto].
        iApply inv_alloc. iNext. iExists _. iFrame.
        iApply fixpoint_interp1_eq;simpl.
        rewrite finz_seq_between_cons; [|solve_addr].
        rewrite (addr_incr_eq Hmid_adv).
        rewrite finz_seq_between_singleton// /=. 2: solve_addr.
        iSplit;auto. iExists interp. iFrame "#".
        iNext. iModIntro. auto.
        iSplit;auto. iExists interp. iFrame "#".
        iNext. iModIntro. auto.
      - rewrite !fixpoint_interp1_eq /=. iFrame "#". done.
    }

    (* extract interval library from priv *)
    rewrite /Hfilter /=.
    assert (assert_library_content ##ₘ interval_library_content) as Hdisj.
    { rewrite /assert_library_content /interval_library_content.
      pose proof (regions_disjoint) as Hdisjoint.
      rewrite !disjoint_list_cons in Hdisjoint. destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      rewrite map_disjoint_union_l !map_disjoint_union_r. repeat split;disjoint_map_to_list.
      rewrite (finz_seq_between_split interval_closure_start interval_body_start). set_solver.
      pose proof interval_closure_size as HH.
      pose proof interval_body_size as HHH. solve_addr +HH HHH.
      1,2,3,4,5: set_solver.
      rewrite (finz_seq_between_split interval_closure_start interval_body_start). set_solver.
      pose proof interval_closure_size as HH.
      pose proof interval_body_size as HHH. solve_addr +HH HHH.
      all: set_solver. }
    rewrite map_filter_union; [|auto].

    iDestruct (big_sepM_union with "Hprivs") as "[Hassert Hprivs]".
    { eapply map_disjoint_filter;auto. }

    (* allocate the assert invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ assertN (assert_inv assert_start assert_flag assert_end)
            with "[Hassert]") as "#Hinv_assert".
    { iNext. rewrite /assert_library_content.
      pose proof assert_code_size. pose proof assert_cap_size. pose proof assert_flag_size.
      rewrite map_filter_union.
      2: { disjoint_map_to_list. apply elem_of_disjoint. intro.
           rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
           intros [ [? ?]|?]; solve_addr. }
      iDestruct (big_sepM_union with "Hassert") as "[Hassert _]".
      { eapply map_disjoint_filter. disjoint_map_to_list.
        apply elem_of_disjoint. intro.
        rewrite elem_of_app elem_of_finz_seq_between !elem_of_list_singleton.
        intros [ [? ?]|?]; solve_addr. }
      rewrite map_filter_id.
      2: { intros ? ? HH%elem_of_dom_2. rewrite !dom_union_L dom_mkregion_eq in HH.
           2: solve_addr. apply elem_of_union in HH.
           rewrite elem_of_singleton. destruct HH as [HH|HH].
           rewrite -> elem_of_list_to_set, elem_of_finz_seq_between in HH; solve_addr.
           rewrite -> dom_list_to_map_singleton, elem_of_list_to_set, elem_of_list_singleton in HH; solve_addr. }
      iDestruct (big_sepM_union with "Hassert") as "[Hassert Hcap]".
      { disjoint_map_to_list. apply elem_of_disjoint. intro.
        rewrite elem_of_finz_seq_between !elem_of_list_singleton. solve_addr. }
      iDestruct (mkregion_sepM_to_sepL2 with "Hassert") as "Hassert". solve_addr.
      rewrite /assert_inv. iExists assert_cap.
      rewrite (_: assert_cap = assert_start ^+ length assert_subroutine_instrs)%a. 2: solve_addr.
      iFrame "Hassert". iDestruct (big_sepM_insert with "Hcap") as "[Hcap _]". done.
      iFrame "Hcap". iPureIntro. repeat split; solve_addr. }

    rewrite map_filter_id. 2: by apply flag_not_in_interval.

    (* cleanup the content of the interval library *)
    rewrite /interval_library_content /seal_library_content.
    iDestruct (big_sepM_union with "Hprivs") as "[Hinterval_cls Hprivs]".
    { rewrite !map_disjoint_union_l !map_disjoint_union_r. repeat split.
      all: try disjoint_map_to_list.
      1,2,3: rewrite (finz_seq_between_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint;
        destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }

    iDestruct (big_sepM_union with "Hinterval_cls") as "[Hinterval_cls Hint_table]".
    { rewrite !map_disjoint_union_l. repeat split.
      all: try disjoint_map_to_list.
      1: rewrite (finz_seq_between_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }
    iDestruct (big_sepM_union with "Hinterval_cls") as "[Hinterval_cls Hinterval_link]".
    { disjoint_map_to_list.
      rewrite (finz_seq_between_split _ interval_body_start);
        [|pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH].
      pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?).
      set_solver. }
    iDestruct (mkregion_sepM_to_sepL2 with "Hinterval_cls") as "Hinterval".
    { pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    rewrite (finz_seq_between_split interval_closure_start interval_body_start); cycle 1.
    { pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    iDestruct (big_sepL2_app' with "Hinterval") as "[Hinterval_cls Hinterval]".
    { rewrite /= finz_seq_between_length /finz.dist.
      pose proof interval_closure_size as HH; pose proof interval_body_size as HHH;solve_addr+HH HHH. }
    iDestruct (mkregion_sepM_to_sepL2 with "Hint_table") as "Hint_table".
    { pose proof int_table_size. auto. }
    assert (is_Some (int_table_start + 1)%a) as [int_table_mid Hint_table_mid].
    { pose proof int_table_size. solve_addr. }
    rewrite (finz_seq_between_cons int_table_start);cycle 1.
    { pose proof int_table_size. solve_addr. }
    rewrite (addr_incr_eq Hint_table_mid). iSimpl in "Hint_table".
    assert (int_table_mid + 1 = Some int_table_end)%a as Hint_table_mid'.
    { pose proof int_table_size as HH. solve_addr+HH Hint_table_mid. }
    rewrite (finz_seq_between_cons int_table_mid);cycle 1.
    { solve_addr. }
    rewrite (addr_incr_eq Hint_table_mid'). iSimpl in "Hint_table".
    iDestruct "Hint_table" as "(Hint_table_start & Hint_table_mid & _)".
    iSimpl in "Hinterval_link". iDestruct (big_sepM_insert with "Hinterval_link") as "[Hinterval_link _]";[auto|].

    (* cleanup the content of the nested seal library *)
    iDestruct (big_sepM_union with "Hprivs") as "[Hprivs Hseal_table]".
    { rewrite map_disjoint_union_l. split.
      all: disjoint_map_to_list.
      all: pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?).
      all: set_solver. }
    iDestruct (big_sepM_union with "Hprivs") as "[Hseal Hseal_link]".
    { disjoint_map_to_list.
      pose proof (regions_disjoint) as Hdisjoint;
        rewrite !disjoint_list_cons in Hdisjoint |- *;
        destruct Hdisjoint as (?&?&?&?&?&?&?&?&?&?).
      set_solver. }
    iDestruct (big_sepM_insert with "Hseal_link") as "[Hseal_link _]";[auto|]. iSimpl in "Hseal_link".
    iDestruct (mkregion_sepM_to_sepL2 with "Hseal_table") as "Hseal_table".
    { pose proof seal_table_size. auto. }
    rewrite (finz_seq_between_cons seal_table_start);cycle 1.
    {  pose proof seal_table_size. solve_addr. }
    rewrite (finz_seq_between_singleton (seal_table_start ^+ 1)%a);cycle 1.
    { pose proof seal_table_size. solve_addr. }
    iDestruct "Hseal_table" as "[Hseal_table [Hseal_table' _]]".
    iAssert (codefrag interval_closure_start (interval_closure 0 1 offset_to_interval)) with "[Hinterval_cls]" as "Hinterval_cls".
    { rewrite /codefrag (addr_incr_eq interval_closure_size). iFrame. }
    iAssert (codefrag seal_body_start (_)) with "[Hseal]" as "Hseal".
    { rewrite /codefrag. erewrite (addr_incr_eq seal_size). iFrame.
      iDestruct (mkregion_sepM_to_sepL2 with "Hseal") as "$". apply seal_size. }
    iAssert (codefrag interval_body_start (interval 0)) with "[Hinterval]" as "Hinterval".
    { rewrite /codefrag (addr_incr_eq interval_body_size). iFrame. }

    (* We apply the client specification *)
    assert (is_Some (interval_client_closure_start + interval_client_closure_move_offset)%a) as [? HH].
    { destruct ((interval_client_closure_start + interval_client_closure_move_offset)%a) eqn:Hsome;eauto. exfalso.
      rewrite /interval_client_closure_move_offset in Hsome. pose proof interval_client_closure_size. solve_addr. }
    assert (is_Some (interval_closure_start + interval_closure_move_offset)%a) as [? HHH].
    { destruct (interval_closure_start + interval_closure_move_offset)%a eqn:hsome;eauto. exfalso.
      rewrite /interval_closure_move_offset in hsome. pose proof interval_closure_size. solve_addr. }
    iDestruct (interval_client_closure_functional_spec with "[- Hown HPC Hr_adv Hrmap]") as "Hcont".
    17: {
      iFrame "Hinv_malloc Hinv_assert Hinv_salloc".
      iFrame "Hint_cls Hint Hinterval_cls Hinterval Hseal".
      rewrite (addr_incr_eq seal_makeseal_entrypoint_correct).
      iFrame "Hroe_link Hint_table_mid Hlink_table_mid'".
      iFrame "Hinterval_link Hseal_link".
      iFrame "Hlink_table_start Hint_table_start Hseal_table".
      iFrame. (* NOTE: one seal_table entry too many here! *)
    }
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
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid'. }
    { apply le_addr_withinBounds'. solve_addr+Hsize Hmid''. }
    { apply le_addr_withinBounds'. solve_addr+Hsize. }
    all: auto.
    { solve_addr. }
    { rewrite /int_table. repeat split;auto.
      1,2: apply le_addr_withinBounds'. all: pose proof seal_table_size as Hsts; solve_addr. }
    { rewrite /mallocN /sallocN. apply ndot_ne_disjoint; auto. }
    { done. }
    { unfold offset_to_checki. pose proof interval_client_closure_size.
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
      iPureIntro. intros. simpl. apply elem_of_dom. rewrite !dom_insert_L Hdom.
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
  Forall (λ w, is_z w = true \/ in_region w adv_start adv_end) (prog_instrs adv_prog) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  (∀ w, m' !! assert_flag = Some w → w = WInt 0%Z).
Proof.
  intros ? ? Hints ?.
  pose proof (template_adequacy gFunctors.nil int_client_prog adv_prog library interval_client_table adv_table flag_inv) as Hadequacy.
  eapply Hadequacy;eauto.
  { apply flag_inv_is_initial_memory. auto. }
  { apply flag_inv_sub. }
  { by pose proof salloc_o_lt. }
  intros Σ ? ? ? ? ?.
  eapply int_client_correct. apply Hints.
Qed.
