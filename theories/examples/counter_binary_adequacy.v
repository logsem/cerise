From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From stdpp Require Import gmap fin_maps fin_sets.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra stdpp_comp iris_extra mkregion_helpers
     logrel_binary fundamental_binary linking malloc macros malloc_binary
     contextual_refinement contextual_refinement_adequacy.
From cap_machine.examples Require Import
  disjoint_regions_tactics counter_binary_preamble_def counter_binary_preamble counter_binary_preamble_left.

Definition machine_component: Type := component nat.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

(* Definition mbkregion (r_start r_end: Addr) (contents: list Word) (contents_spec: list Word): gmap Addr (Word * Word) := *)
(*   list_to_map (zip (region_addrs r_start r_end) (zip contents contents_spec)). *)

(* Instance segment_union : Union (segment Word). *)
(* Proof. rewrite /segment. apply _. Qed. *)


Class memory_layout `{MachineParameters} := {
  (* counter example: preamble & body *)
  counter_region_start : Addr;
  counter_preamble_start : Addr;
  counter_body_start : Addr;
  counter_region_end : Addr;

  (* pointer to the linking table, at the beginning of the region *)
  counter_linking_ptr_size :
    (counter_region_start + 1)%a = Some counter_preamble_start;

  (* preamble code, that allocates the closure *)
  counter_preamble_size :
    (counter_preamble_start + counter_preamble_instrs_length)%a
    = Some counter_body_start;

  (* code of the body, wrapped in the closure allocated by the preamble *)
  counter_body_size :
    (counter_body_start + counter_left_instrs_length)%a (* we need to pad the entry points to mask the bounds, both counters will thus be of the largest possible size *)
    = Some counter_region_end;

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

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 1)%a = Some link_table_end;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        finz.seq_between link_table_start link_table_end;
        finz.seq_between malloc_mem_start malloc_end;
        [malloc_memptr];
        finz.seq_between malloc_start malloc_memptr;
        finz.seq_between counter_body_start counter_region_end;
        finz.seq_between counter_preamble_start counter_body_start;
        [counter_region_start]
       ];
  }.


Definition offset_to_awkward `{memory_layout} : Z :=
  (* in this setup, the body of the counter comes just after the code
     of the preamble *)
  (counter_preamble_instrs_length - counter_preamble_move_offset)%Z.

Definition mk_initial_memory_left `{memory_layout} : gmap Addr Word :=
  (* pointer to the linking table *)
    list_to_map [(counter_region_start,
                  WCap RO link_table_start link_table_end link_table_start)]
  ∪ mkregion counter_preamble_start counter_body_start
       (* preamble: code that creates the awkward example closure *)
      (counter_left_preamble_instrs 0%Z (* offset to malloc in linking table *)
         offset_to_awkward (* offset to the body of the example *))
  ∪ mkregion counter_body_start counter_region_end
       (* body of the counter, that will be encapsulated in the closure
          created by the preamble *)
      (counter_left_instrs)

  (* ∪ mkregion adv_start adv_end *)
  (*     (* adversarial code: any code or data, but no capabilities (see condition below) except for malloc *) *)
  (*     (adv_val ++ [WCap E malloc_start malloc_end malloc_start]) *)
  ∪ mkregion malloc_start malloc_memptr
      (* code for the malloc subroutine *)
      malloc_subroutine_instrs
  ∪ list_to_map
      (* Capability to malloc's memory pool, used by the malloc subroutine *)
      [(malloc_memptr, WCap RWX malloc_memptr malloc_end malloc_mem_start)]
  ∪ mkregion malloc_mem_start malloc_end
      (* Malloc's memory pool, initialized to zero *)
      (region_addrs_zeroes malloc_mem_start malloc_end)
  ∪ mkregion link_table_start link_table_end
      (* link table, with pointers to the malloc subroutines *)
      [WCap E malloc_start malloc_end malloc_start]
.

Definition mk_initial_memory_right `{memory_layout} : gmap Addr Word :=
  (* pointer to the linking table *)
    list_to_map [(counter_region_start,
                  WCap RO link_table_start link_table_end link_table_start)]
  ∪ mkregion counter_preamble_start counter_body_start
       (* preamble: code that creates the awkward example closure *)
      (counter_left_preamble_instrs 0%Z (* offset to malloc in linking table *)
         offset_to_awkward (* offset to the body of the example *))
  ∪ mkregion counter_body_start counter_region_end
       (* body of the counter, that will be encapsulated in the closure
          created by the preamble *)
      (counter_right_instrs)

  (* ∪ mkregion adv_start adv_end *)
  (*     (* adversarial code: any code or data, but no capabilities (see condition below) except for malloc *) *)
  (*     (adv_val ++ [WCap E malloc_start malloc_end malloc_start]) *)
  ∪ mkregion malloc_start malloc_memptr
      (* code for the malloc subroutine *)
      malloc_subroutine_instrs
  ∪ list_to_map
      (* Capability to malloc's memory pool, used by the malloc subroutine *)
      [(malloc_memptr, WCap RWX malloc_memptr malloc_end malloc_mem_start)]
  ∪ mkregion malloc_mem_start malloc_end
      (* Malloc's memory pool, initialized to zero *)
      (region_addrs_zeroes malloc_mem_start malloc_end)
  ∪ mkregion link_table_start link_table_end
      (* link table, with pointers to the malloc subroutines *)
      [WCap E malloc_start malloc_end malloc_start]
.

Definition comp1 `{memory_layout} : machine_component := {|
  segment := mk_initial_memory_left;
  imports := ∅;
  exports := {[ 0 := WCap E counter_region_start counter_region_end counter_preamble_start ]};
|}.

Definition comp2 `{memory_layout} : machine_component := {|
  segment := mk_initial_memory_right;
  imports := ∅;
  exports := {[ 0 := WCap E counter_region_start counter_region_end counter_preamble_start ]};
|}.

Definition is_initial_context (c : machine_component) (r : Reg) :=
  code_all_ints c ∧
  (∀ r', r' ≠ PC → r !! r' = Some (WInt 0)) ∧
  (∃ p b e a,
      r !! PC = Some (WCap p b e a) ∧
      (p = RX ∨ p = RWX)) ∧
  (∃ a, imports c = {[a := 0]}) ∧
  exports c = ∅.
  (* extra assumptions on adv imports and exports that make the proof easier to go through *)

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {MP: MachineParameters}.

  Context {cfgg : inG Σ (authR cfgUR)}.

  Lemma confidentiality_adequacy_l' {ML:memory_layout} c_adv r (es : list cap_lang.expr) reg' m' :
    is_ctxt c_adv comp1 r →
    is_ctxt c_adv comp2 r →
    is_initial_context c_adv r →
    rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hs. exists [].
    inversion Hc as (Hallints & Hregs & (p & b & e & a & Hrpbea & Hp) & (addr & Himp) & Hexp).
    specialize (contextual_refinement_adequacy comp1 comp2 c_adv r p b e a es) as Href.
    destruct Href as [_ Href]; try done.
    - inversion Hm2. solve_can_link.
    - simpl. unfold mk_initial_memory_left, mk_initial_memory_right.
      rewrite !dom_union_L !dom_mkregion_eq.
      done.
      apply counter_body_size.
      apply link_table_size.
      rewrite replicate_length. apply finz_dist_incr. apply malloc_mem_size.
      apply malloc_code_size.
      apply counter_body_size.
      apply counter_preamble_size.
    - iIntros (memg regg logrel_na_invs Hcfg) "(#Hspec & Hmem & Hmemspec)".
      clear na_invg. (* Duplicate instances -> Coq stupidity *)
      simpl. unfold interp_exports. simpl.
      rewrite big_sepM_singleton lookup_singleton.

      pose proof regions_disjoint as Hdisjoint.
      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_link_table & Hdisjoint).
      rewrite /mk_initial_memory_left /mk_initial_memory_right.

      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hlink_table]".
      { disjoint_map_to_list. set_solver+ Hdisj_link_table. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hlink_table_spec]".
      { disjoint_map_to_list. set_solver+ Hdisj_link_table. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_mem & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_mem]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_mem_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_memptr & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_memptr]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_memptr_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }

      iDestruct (big_sepM_insert with "Hmalloc_memptr") as "[Hmalloc_memptr _]".
      by apply lookup_empty. cbn [fst snd].
      iDestruct (big_sepM_insert with "Hmalloc_memptr_spec") as "[Hmalloc_memptr_spec _]".
      by apply lookup_empty. cbn [fst snd].

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_code & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_code]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_code_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_counter_body & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcounter_body]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_body. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hcounter_body_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_body. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_counter_preamble & _).
      iDestruct (big_sepM_union with "Hmem") as "[Hcounter_link Hcounter_preamble]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_preamble. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hcounter_link_spec Hcounter_preamble_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_preamble. }

      iDestruct (big_sepM_insert with "Hcounter_link") as "[Hcounter_link _]". by apply lookup_empty.
      iDestruct (big_sepM_insert with "Hcounter_link_spec") as "[Hcounter_link_spec _]". by apply lookup_empty.
      cbn [fst snd].

      clear Hdisj_link_table Hdisj_malloc_mem
        Hdisj_malloc_memptr Hdisj_malloc_code Hdisj_counter_body Hdisj_counter_preamble.

      (* Massage points-to into sepL2s with permission-pointsto *)
      iDestruct (mkregion_prepare with "[$Hlink_table]") as ">Hlink_table". by apply link_table_size.
      iDestruct (mkregion_prepare with "[$Hmalloc_mem]") as ">Hmalloc_mem".
      { rewrite replicate_length /finz.dist. clear.
        generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
      iDestruct (mkregion_prepare with "[$Hmalloc_code]") as ">Hmalloc_code".
        by apply malloc_code_size.
      iDestruct (mkregion_prepare with "[$Hcounter_preamble]") as ">Hcounter_preamble".
        by apply counter_preamble_size.
      iDestruct (mkregion_prepare with "[$Hcounter_body]") as ">Hcounter_body". by apply counter_body_size.
      iDestruct (mkregion_prepare_spec with "[$Hlink_table_spec]") as ">Hlink_table_spec". by apply link_table_size.
      iDestruct (mkregion_prepare_spec with "[$Hmalloc_mem_spec]") as ">Hmalloc_mem_spec".
      { rewrite replicate_length /finz.dist. clear.
        generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
      iDestruct (mkregion_prepare_spec with "[$Hmalloc_code_spec]") as ">Hmalloc_code_spec".
        by apply malloc_code_size.
      iDestruct (mkregion_prepare_spec with "[$Hcounter_preamble_spec]") as ">Hcounter_preamble_spec".
        by apply counter_preamble_size.
      iDestruct (mkregion_prepare_spec with "[$Hcounter_body_spec]") as ">Hcounter_body_spec". by apply counter_body_size.

      rewrite -/(counter_left _) -/(counter_left_preamble _ _ _).
      rewrite -/(counter_right _) -/(counter_right_preamble _ _ _).

      (* Split the link table *)
      rewrite (finz_seq_between_cons link_table_start link_table_end).
      2: { generalize link_table_size; clear; solve_addr. }
      rewrite (_: (link_table_start ^+ 1)%a = link_table_end).
      2: { generalize link_table_size; clear.
           generalize link_table_start link_table_end. solve_addr. }
      iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink1 _]".
      iDestruct (big_sepL2_cons with "Hlink_table_spec") as "[Hlink1' _]".

      (* Allocate malloc invariant *)
      iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv_binary malloc_start malloc_end)
              with "[Hmalloc_code Hmalloc_memptr Hmalloc_mem Hmalloc_code_spec Hmalloc_memptr_spec Hmalloc_mem_spec]") as "#Hinv_malloc".
      { iNext. unfold malloc_inv_binary. iExists _,_. iFrame.
        iPureIntro. generalize malloc_code_size malloc_mem_size malloc_memptr_size. cbn.
        clear; unfold malloc_subroutine_instrs_length; intros; repeat split; solve_addr. }

      (* Facts about layout *)
      assert (isCorrectPC_range RX counter_region_start counter_region_end
                counter_preamble_start counter_body_start).
      { intros a' [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2. clear.
        unfold counter_left_instrs_length, counter_preamble_instrs_length. solve_addr. }
      set counter_preamble_move_addr := (counter_preamble_start ^+ counter_preamble_move_offset)%a.
      assert ((counter_preamble_start + counter_preamble_move_offset)%a = Some counter_preamble_move_addr).
      { clear. subst counter_preamble_move_addr.
        generalize counter_preamble_size.
        unfold counter_preamble_instrs_length, counter_preamble_move_offset.
        generalize counter_preamble_start counter_body_start. solve_addr. }
      assert (counter_preamble_move_addr + offset_to_awkward = Some counter_body_start)%a.
      { generalize counter_preamble_size.
        unfold counter_preamble_move_addr, offset_to_awkward, counter_preamble_instrs_length.
        unfold counter_preamble_move_offset. clear.
        generalize counter_preamble_start counter_body_start. solve_addr. }
      assert (isCorrectPC_range RX counter_region_start counter_region_end
                counter_body_start counter_region_end).
      { intros a' [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2; clear.
        unfold counter_left_instrs_length, counter_preamble_instrs_length. solve_addr. }

      (* Extract validity of library *)
      pose proof (
        @counter_binary_preamble.counter_preamble_spec Σ memg regg logrel_na_invs Hcfg
        ) as Spec.
      iApply (Spec with "[$Hspec $Hinv_malloc $Hcounter_preamble $Hcounter_body
                      $Hcounter_preamble_spec $Hcounter_body_spec $Hcounter_link $Hcounter_link_spec $Hlink1 $Hlink1']").
      apply H. apply H.
      { apply contiguous_between_region_addrs. generalize counter_preamble_size; clear.
        unfold counter_preamble_instrs_length. solve_addr. }
      { apply contiguous_between_region_addrs. generalize counter_preamble_size; clear.
        unfold counter_preamble_instrs_length. solve_addr. }
      { apply le_addr_withinBounds. clear; solve_addr.
        generalize link_table_size; clear; solve_addr. }
      { generalize link_table_start; clear; solve_addr. }
      { apply le_addr_withinBounds. solve_addr.
        generalize link_table_start link_table_end link_table_size. clear; solve_addr. }
      { generalize link_table_start; clear; solve_addr. }
      { eassumption. }
      { eassumption. }
      { apply H2. }
      { apply contiguous_between_region_addrs. generalize counter_body_size; clear.
        unfold counter_left_instrs_length. solve_addr. }
      { eassumption. }
      { eassumption. }
      { apply H2. }
      { apply contiguous_between_region_addrs. generalize counter_body_size; clear.
        unfold counter_left_instrs_length. solve_addr. }
      { auto. }
    - exists (reg', m'). rewrite link_comm. done. inversion Hm1. solve_can_link.
    - rewrite link_comm. done. inversion Hm2. solve_can_link.
  Qed.


  Lemma confidentiality_adequacy_r' {ML:memory_layout} c_adv r (es: list cap_lang.expr) reg' m' :
    is_ctxt c_adv comp1 r →
    is_ctxt c_adv comp2 r →
    is_initial_context c_adv r →
    rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hs. exists [].
    inversion Hc as (Hallints & Hregs & (p & b & e & a & Hrpbea & Hp) & (addr & Himp) & Hexp).
    specialize (contextual_refinement_adequacy comp2 comp1 c_adv r p b e a es) as Href.
    destruct Href as [_ Href]; try done.
    - inversion Hm2. solve_can_link.
    - simpl. unfold mk_initial_memory_left, mk_initial_memory_right.
      rewrite !dom_union_L !dom_mkregion_eq.
      done.
      apply counter_body_size.
      apply link_table_size.
      rewrite replicate_length. apply finz_dist_incr. apply malloc_mem_size.
      apply malloc_code_size.
      apply counter_body_size.
      apply counter_preamble_size.
    - iIntros (memg regg logrel_na_invs Hcfg) "(#Hspec & Hmem & Hmemspec)".
      clear na_invg. (* Duplicate instances -> Coq stupidity *)
      simpl. unfold interp_exports. simpl.
      rewrite big_sepM_singleton lookup_singleton.

      pose proof regions_disjoint as Hdisjoint.
      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_link_table & Hdisjoint).
      rewrite /mk_initial_memory_left /mk_initial_memory_right.

      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hlink_table]".
      { disjoint_map_to_list. set_solver+ Hdisj_link_table. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hlink_table_spec]".
      { disjoint_map_to_list. set_solver+ Hdisj_link_table. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_mem & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_mem]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_mem_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_memptr & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_memptr]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_memptr_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }

      iDestruct (big_sepM_insert with "Hmalloc_memptr") as "[Hmalloc_memptr _]".
      by apply lookup_empty. cbn [fst snd].
      iDestruct (big_sepM_insert with "Hmalloc_memptr_spec") as "[Hmalloc_memptr_spec _]".
      by apply lookup_empty. cbn [fst snd].

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_malloc_code & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_code]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hmalloc_code_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_counter_body & Hdisjoint).
      iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcounter_body]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_body. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hcounter_body_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_body. }

      rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_counter_preamble & _).
      iDestruct (big_sepM_union with "Hmem") as "[Hcounter_link Hcounter_preamble]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_preamble. }
      iDestruct (big_sepM_union with "Hmemspec") as "[Hcounter_link_spec Hcounter_preamble_spec]".
      { disjoint_map_to_list. set_solver +Hdisj_counter_preamble. }

      iDestruct (big_sepM_insert with "Hcounter_link") as "[Hcounter_link _]". by apply lookup_empty.
      iDestruct (big_sepM_insert with "Hcounter_link_spec") as "[Hcounter_link_spec _]". by apply lookup_empty.
      cbn [fst snd].

      clear Hdisj_link_table Hdisj_malloc_mem
        Hdisj_malloc_memptr Hdisj_malloc_code Hdisj_counter_body Hdisj_counter_preamble.

      (* Massage points-to into sepL2s with permission-pointsto *)
      iDestruct (mkregion_prepare with "[$Hlink_table]") as ">Hlink_table". by apply link_table_size.
      iDestruct (mkregion_prepare with "[$Hmalloc_mem]") as ">Hmalloc_mem".
      { rewrite replicate_length /finz.dist. clear.
        generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
      iDestruct (mkregion_prepare with "[$Hmalloc_code]") as ">Hmalloc_code".
        by apply malloc_code_size.
      iDestruct (mkregion_prepare with "[$Hcounter_preamble]") as ">Hcounter_preamble".
        by apply counter_preamble_size.
      iDestruct (mkregion_prepare with "[$Hcounter_body]") as ">Hcounter_body". by apply counter_body_size.
      iDestruct (mkregion_prepare_spec with "[$Hlink_table_spec]") as ">Hlink_table_spec". by apply link_table_size.
      iDestruct (mkregion_prepare_spec with "[$Hmalloc_mem_spec]") as ">Hmalloc_mem_spec".
      { rewrite replicate_length /finz.dist. clear.
        generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
      iDestruct (mkregion_prepare_spec with "[$Hmalloc_code_spec]") as ">Hmalloc_code_spec".
        by apply malloc_code_size.
      iDestruct (mkregion_prepare_spec with "[$Hcounter_preamble_spec]") as ">Hcounter_preamble_spec".
        by apply counter_preamble_size.
      iDestruct (mkregion_prepare_spec with "[$Hcounter_body_spec]") as ">Hcounter_body_spec". by apply counter_body_size.

      rewrite -/(counter_left _) -/(counter_left_preamble _ _ _).
      rewrite -/(counter_right _) -/(counter_right_preamble _ _ _).

      (* Split the link table *)
      rewrite (finz_seq_between_cons link_table_start link_table_end).
      2: { generalize link_table_size; clear; solve_addr. }
      rewrite (_: (link_table_start ^+ 1)%a = link_table_end).
      2: { generalize link_table_size; clear.
          generalize link_table_start link_table_end. solve_addr. }
      iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink1 _]".
      iDestruct (big_sepL2_cons with "Hlink_table_spec") as "[Hlink1' _]".

      (* Allocate malloc invariant *)
      iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv_binary malloc_start malloc_end)
              with "[Hmalloc_code Hmalloc_memptr Hmalloc_mem Hmalloc_code_spec Hmalloc_memptr_spec Hmalloc_mem_spec]") as "#Hinv_malloc".
      { iNext. unfold malloc_inv_binary. iExists _,_. iFrame.
        iPureIntro. generalize malloc_code_size malloc_mem_size malloc_memptr_size. cbn.
        clear; unfold malloc_subroutine_instrs_length; intros; repeat split; solve_addr. }

      (* Facts about layout *)
      assert (isCorrectPC_range RX counter_region_start counter_region_end
                counter_preamble_start counter_body_start).
      { intros a' [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2. clear.
        unfold counter_left_instrs_length, counter_preamble_instrs_length. solve_addr. }
      set counter_preamble_move_addr := (counter_preamble_start ^+ counter_preamble_move_offset)%a.
      assert ((counter_preamble_start + counter_preamble_move_offset)%a = Some counter_preamble_move_addr).
      { clear. subst counter_preamble_move_addr.
        generalize counter_preamble_size.
        unfold counter_preamble_instrs_length, counter_preamble_move_offset.
        generalize counter_preamble_start counter_body_start. solve_addr. }
      assert (counter_preamble_move_addr + offset_to_awkward = Some counter_body_start)%a.
      { generalize counter_preamble_size.
        unfold counter_preamble_move_addr, offset_to_awkward, counter_preamble_instrs_length.
        unfold counter_preamble_move_offset. clear.
        generalize counter_preamble_start counter_body_start. solve_addr. }
      assert (isCorrectPC_range RX counter_region_start counter_region_end
                counter_body_start counter_region_end).
      { intros a' [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2; clear.
        unfold counter_left_instrs_length, counter_preamble_instrs_length. solve_addr. }

      (* Extract validity of library *)
      pose proof (
        @counter_binary_preamble_left.counter_preamble_spec Σ memg regg logrel_na_invs Hcfg
        ) as Spec.
      iApply (Spec with "[$Hspec $Hinv_malloc $Hcounter_preamble $Hcounter_body
                      $Hcounter_preamble_spec $Hcounter_body_spec $Hcounter_link $Hcounter_link_spec $Hlink1 $Hlink1']").
      apply H. apply H.
      { apply contiguous_between_region_addrs. generalize counter_preamble_size; clear.
        unfold counter_preamble_instrs_length. solve_addr. }
      { apply contiguous_between_region_addrs. generalize counter_preamble_size; clear.
        unfold counter_preamble_instrs_length. solve_addr. }
      { apply le_addr_withinBounds. clear; solve_addr.
        generalize link_table_size; clear; solve_addr. }
      { generalize link_table_start; clear; solve_addr. }
      { apply le_addr_withinBounds. solve_addr.
        generalize link_table_start link_table_end link_table_size. clear; solve_addr. }
      { generalize link_table_start; clear; solve_addr. }
      { eassumption. }
      { eassumption. }
      { apply H2. }
      { apply contiguous_between_region_addrs. generalize counter_body_size; clear.
        unfold counter_left_instrs_length. solve_addr. }
      { eassumption. }
      { eassumption. }
      { apply H2. }
      { apply contiguous_between_region_addrs. generalize counter_body_size; clear.
        unfold counter_left_instrs_length. solve_addr. }
      { auto. }
    - exists (reg', m'). rewrite link_comm. done. inversion Hm1. solve_can_link.
    - rewrite link_comm. done. inversion Hm2. solve_can_link.
  Qed.

End Adequacy.
