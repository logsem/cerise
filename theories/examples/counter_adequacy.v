From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import
     macros malloc counter_preamble disjoint_regions_tactics mkregion_helpers.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout `{MachineParameters} := {
  (* awkward example: preamble & body *)
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
    (counter_body_start + counter_instrs_length)%a
    = Some counter_region_end;

  (* adversary code *)
  adv_start : Addr;
  adv_end : Addr;

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

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* failure flag *)
  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        [fail_flag];
        region_addrs link_table_start link_table_end;
        region_addrs fail_start fail_end;
        region_addrs malloc_mem_start malloc_end;
        [malloc_memptr];
        region_addrs malloc_start malloc_memptr;
        region_addrs adv_start adv_end;
        region_addrs counter_body_start counter_region_end;
        region_addrs counter_preamble_start counter_body_start;
        [counter_region_start]
       ];
}.

Definition offset_to_awkward `{memory_layout} : Z :=
  (* in this setup, the body of the counter comes just after the code
     of the preamble *)
  (counter_preamble_instrs_length - counter_preamble_move_offset)%Z.

Definition mk_initial_memory `{memory_layout} (adv_val: list Word) : gmap Addr Word :=
  (* pointer to the linking table *)
    list_to_map [(counter_region_start,
                  inr (RO, link_table_start, link_table_end, link_table_start))]
  ∪ mkregion counter_preamble_start counter_body_start
       (* preamble: code that creates the awkward example closure *)
      (counter_preamble_instrs 0%Z (* offset to malloc in linking table *)
         offset_to_awkward (* offset to the body of the example *))
  ∪ mkregion counter_body_start counter_region_end
       (* body of the counter, that will be encapsulated in the closure
          created by the preamble *)
      (counter_instrs 1) (* offset to fail in the linking table *)
      
  ∪ mkregion adv_start adv_end
      (* adversarial code: any code or data, but no capabilities (see condition below) except for malloc *)
      (adv_val ++ [inr (E, malloc_start, malloc_end, malloc_start)])
  ∪ mkregion malloc_start malloc_memptr
      (* code for the malloc subroutine *)
      malloc_subroutine_instrs
  ∪ list_to_map
      (* Capability to malloc's memory pool, used by the malloc subroutine *)
      [(malloc_memptr, inr (RWX, malloc_memptr, malloc_end, malloc_mem_start))]
  ∪ mkregion malloc_mem_start malloc_end
      (* Malloc's memory pool, initialized to zero *)
      (region_addrs_zeroes malloc_mem_start malloc_end)
  ∪ mkregion fail_start fail_end
      ((* code for the failure subroutine *)
        assert_fail_instrs ++
       (* pointer to the "failure" flag, set to 1 by the routine *)
       [inr (RW, fail_flag, fail_flag_next, fail_flag)])
  ∪ mkregion link_table_start link_table_end
      (* link table, with pointers to the malloc and failure subroutines *)
      [inr (E, malloc_start, malloc_end, malloc_start);
       inr (E, fail_start, fail_end, fail_start)]
  ∪ list_to_map [(fail_flag, inl 0%Z)] (* failure flag, initially set to 0 *)
.

Definition is_initial_memory `{memory_layout} (m: gmap Addr Word) :=
  ∃ (adv_val: list Word),
  m = mk_initial_memory adv_val
  ∧
  (* the adversarial region in memory must only contain instructions, no
     capabilities (it can thus only access capabilities the awkward preamble
     passes it through the registers) *)
  Forall (λ w, is_cap w = false) adv_val
  ∧
  (adv_start + (length adv_val + 1)%nat)%a = Some adv_end.

Definition is_initial_registers `{memory_layout} (reg: gmap RegName Word) :=
  reg !! PC = Some (inr (RX, counter_region_start, counter_region_end, counter_preamble_start)) ∧
  reg !! r_t0 = Some (inr (RWX, adv_start, adv_end, adv_start)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; r_t0 ]} : gset RegName) →
    ∃ (w:Word), reg !! r = Some w ∧ is_cap w = false).

Lemma initial_registers_full_map `{MachineParameters, memory_layout} reg :
  is_initial_registers reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hr0 & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_t0)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Definition flagN : namespace := nroot .@ "awk" .@ "fail_flag".
  Definition mallocN : namespace := nroot .@ "awk" .@ "malloc".

  Lemma counter_adequacy' `{memory_layout} (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
    is_initial_memory m →
    is_initial_registers reg →
    rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
    m' !! fail_flag = Some (inl 0%Z).
  Proof.
    intros Hm Hreg Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c: ExecConf) => c.2 !! fail_flag = Some (inl 0%Z)) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, m) es (reg', m') (state_is_good (reg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    destruct Hm as (adv_val & Hm & Hadv_val & adv_size).
    iMod (gen_heap_init (∅:Mem)) as (mem_heapg) "Hmem_ctx".
    iMod (gen_heap_init (∅:Reg)) as (reg_heapg) "Hreg_ctx".
    (* unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*) *)
    (* set W0 := ((∅, (∅, ∅)) : WORLD). *)
    (* iMod heap_init as (heapg) "HRELS". *)
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    
    pose proof (
      @counter_preamble_spec Σ memg regg logrel_na_invs
    ) as Spec.

    iMod (gen_heap_alloc_gen _ reg with "Hreg_ctx") as "(Hreg_ctx & Hreg & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.
    iMod (gen_heap_alloc_gen _ m with "Hmem_ctx") as "(Hmem_ctx & Hmem & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.

    (* Extract points-to for the various regions in memory *)
      
    pose proof regions_disjoint as Hdisjoint.
    rewrite {2}Hm.
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_fail_flag & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hfail_flag]".
    { disjoint_map_to_list. set_solver +Hdisj_fail_flag. }
    iDestruct (big_sepM_insert with "Hfail_flag") as "[Hfail_flag _]".
      by apply lookup_empty. cbn [fst snd].
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_link_table & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hlink_table]".
    { disjoint_map_to_list. set_solver +Hdisj_link_table. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_fail & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hfail]".
    { disjoint_map_to_list. set_solver +Hdisj_fail. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_mem & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_mem]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_memptr & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_memptr]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }
    iDestruct (big_sepM_insert with "Hmalloc_memptr") as "[Hmalloc_memptr _]".
      by apply lookup_empty. cbn [fst snd].
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_code & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_code]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_adv & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]".
    { disjoint_map_to_list. set_solver +Hdisj_adv. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_counter_body & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcounter_body]".
    { disjoint_map_to_list. set_solver +Hdisj_counter_body. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_counter_preamble & _).
    iDestruct (big_sepM_union with "Hmem") as "[Hcounter_link Hcounter_preamble]".
    { disjoint_map_to_list. set_solver +Hdisj_counter_preamble. }
    iDestruct (big_sepM_insert with "Hcounter_link") as "[Hcounter_link _]". by apply lookup_empty.
    cbn [fst snd].
    clear Hdisj_fail_flag Hdisj_link_table Hdisj_fail Hdisj_malloc_mem Hdisj_malloc_memptr
          Hdisj_malloc_code Hdisj_adv Hdisj_counter_body Hdisj_counter_preamble.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare with "[$Hlink_table]") as ">Hlink_table". by apply link_table_size.
    iDestruct (mkregion_prepare with "[$Hfail]") as ">Hfail". by apply fail_size.
    iDestruct (mkregion_prepare with "[$Hmalloc_mem]") as ">Hmalloc_mem".
    { rewrite replicate_length /region_size. clear.
      generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
    iDestruct (mkregion_prepare with "[$Hmalloc_code]") as ">Hmalloc_code".
      by apply malloc_code_size.
    iDestruct (mkregion_prepare with "[$Hadv]") as ">Hadv". rewrite app_length /=. by apply adv_size.
    iDestruct (mkregion_prepare with "[$Hcounter_preamble]") as ">Hcounter_preamble".
      by apply counter_preamble_size.
    iDestruct (mkregion_prepare with "[$Hcounter_body]") as ">Hcounter_body". by apply counter_body_size.
    rewrite -/(counter _ _ _ _) -/(counter_preamble _ _ _ _).

    (* Split the link table *)

    rewrite (region_addrs_cons link_table_start link_table_end).
    2: { generalize link_table_size; clear; solve_addr. }
    set link_entry_fail := ^(link_table_start + 1)%a.
    rewrite (region_addrs_cons link_entry_fail link_table_end).
    2: { generalize link_table_size; clear. subst link_entry_fail.
         generalize link_table_start link_table_end. solve_addr. }
    rewrite (_: ^(link_entry_fail + 1)%a = link_table_end).
    2: { generalize link_table_size; clear. subst link_entry_fail.
         generalize link_table_start link_table_end. solve_addr. }
    iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink1 Hlink_table]".
    iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink2 _]".

    (* Allocate relevant invariants *)

    iMod (inv_alloc flagN ⊤ (fail_flag ↦ₐ inl 0%Z) with "Hfail_flag")%I as "#Hinv_fail_flag".
    iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv malloc_start malloc_end)
            with "[Hmalloc_code Hmalloc_memptr Hmalloc_mem]") as "#Hinv_malloc".
    { iNext. rewrite /malloc_inv. iExists malloc_memptr, malloc_mem_start.
      iFrame. rewrite /proofmode.codefrag.
      rewrite (_: (malloc_start ^+ length malloc_subroutine_instrs)%a = malloc_memptr).
      2: { generalize malloc_code_size. solve_addr. } iFrame.
      iPureIntro. generalize malloc_code_size malloc_mem_size malloc_memptr_size. cbn.
      clear; unfold malloc_subroutine_instrs_length; intros; repeat split; solve_addr. }
    iDestruct (simple_malloc_subroutine_valid with "[$Hinv_malloc]") as "Hmalloc_val".
    (* Allocate a permanent region for the adversary code *)

    (* iAssert (⌜∀ k, *)
    (*   is_Some (mkregion stack_start stack_end stack_val !! k) → *)
    (*   k ∉ region_addrs adv_start adv_end⌝)%I *)
    (* as %Hstack_adv_disj. *)
    (* { iIntros (k Hk Hk'). destruct Hk. *)
    (*   iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto. *)
    (*   apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi]. *)
    (*   iDestruct (big_sepL2_length with "Hadv") as %Hlen. *)
    (*   destruct (lookup_lt_is_Some_2 adv_val i). *)
    (*   { rewrite -Hlen. apply lookup_lt_is_Some_1. eauto. } *)
    (*   iDestruct (big_sepL2_lookup _ _ _ i with "Hadv") as "Hk'"; eauto. *)
    (*   iApply (cap_duplicate_false with "[$Hk $Hk']"). done. } *)

    assert (contiguous_between (region_addrs adv_start adv_end) adv_start adv_end) as Hcont.
    { apply contiguous_between_region_addrs. clear -adv_size. solve_addr. }
    iDestruct (contiguous_between_program_split with "Hadv") as (adv_words malloc_word adv_end') "(Hadv & Hmalloc & #Hcont)";[eauto|]. 
    iDestruct "Hcont" as %(Hcontadv & Hcontmalloc & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hmalloc") as %Hlen1. simpl in Hlen1.
    iDestruct (big_sepL2_length with "Hadv") as %Hlen2. simpl in Hlen2.
      
    iMod (region_inv_alloc _ (adv_words ++ malloc_word)
                           (adv_val ++ [inr (E, malloc_start, malloc_end, malloc_start)])
            with "[Hadv Hmalloc]") as "Hadv".
    { iApply (big_sepL2_app');[auto|]. 
      iSplitL "Hadv". 
      - iApply (big_sepL2_mono with "Hadv").
        intros k v1 v2 Hv1 Hv2. cbn. iIntros. iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ Hadv_val Hv2) as Hncap.
        destruct v2; [| by inversion Hncap].
        rewrite fixpoint_interp1_eq /=. done.
      - destruct malloc_word;[inversion Hlen1|]. destruct malloc_word;[|inversion Hlen1].
        iDestruct "Hmalloc" as "[Hmalloc _]". iFrame "∗ #". done. 
    }
    iDestruct "Hadv" as "#Hadv".
    
    (* Apply the spec, obtain that the PC is in the expression relation *)

    iAssert ((interp_expr interp reg) (inr (RX, counter_region_start, counter_region_end, counter_preamble_start)))
      with "[Hcounter_preamble Hcounter_body Hinv_malloc Hcounter_link Hlink1 Hlink2]" as "HE".
    { assert (isCorrectPC_range RX counter_region_start counter_region_end
                                counter_preamble_start counter_body_start).
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2. clear.
        unfold counter_instrs_length, counter_preamble_instrs_length. solve_addr. }
      set counter_preamble_move_addr := ^(counter_preamble_start + counter_preamble_move_offset)%a.
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
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize counter_linking_ptr_size counter_preamble_size counter_body_size. revert Ha1 Ha2; clear.
        unfold counter_instrs_length, counter_preamble_instrs_length. solve_addr. }

      iApply (Spec with "[$Hinv_malloc $Hcounter_body $Hcounter_preamble $Hcounter_link $Hlink1 $Hlink2]");
        try eassumption.
      - apply contiguous_between_region_addrs. generalize counter_preamble_size; clear.
        unfold counter_preamble_instrs_length. solve_addr.
      - apply le_addr_withinBounds. clear; solve_addr.
        generalize link_table_size; clear; solve_addr.
      - subst link_entry_fail. apply le_addr_withinBounds.
        generalize link_table_start; clear; solve_addr.
        generalize link_table_start link_table_end link_table_size. clear; solve_addr.
      - clear; generalize link_table_start; solve_addr.
      - clear; subst link_entry_fail;
        generalize link_table_start link_table_end link_table_size; solve_addr.
      - apply contiguous_between_region_addrs. generalize counter_body_size; clear.
        unfold counter_instrs_length. solve_addr. }
    
    clear Hm Spec. rewrite /interp_expr /=.

    (* prepare registers *)

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hstk & Hrothers).

    (* Specialize the expression relation, showing that registers are valid *)

    iSpecialize ("HE" with "[Hreg Hna]").
    { iFrame. iSplit; cycle 1.
      { iFrame. rewrite /registers_mapsto. by rewrite insert_id. }
      { iSplit. iPureIntro; intros; by apply initial_registers_full_map.
        (* All capabilities in registers are valid! *)
        iIntros (r HrnPC).
        (* r0 (return pointer to the adversary) is valid. Prove it using the
           fundamental theorem. *)
        destruct (decide (r = r_t0)) as [ -> |].
        { rewrite /RegLocate Hstk !fixpoint_interp1_eq /=.
          iDestruct (big_sepL2_length with "Hadv") as %Hadvlength. 
          iDestruct (big_sepL2_to_big_sepL_l with "Hadv") as "Hadv'";auto. rewrite -Heqapp. 
          iApply (big_sepL_mono with "Hadv'"). iIntros (k v Hkv). cbn.
          iIntros "H". iExists (interp). iFrame.
          iSplit;auto. 
        }
        
        (* Other registers *)
        rewrite /RegLocate.
        destruct (Hrothers r) as [rw [Hrw Hncap] ]. set_solver.
        destruct rw; [| by inversion Hncap].
        by rewrite Hrw !fixpoint_interp1_eq /=. } }

    (* We get a WP; conclude using the rest of the Iris adequacy theorem *)

    iDestruct "HE" as "[_ HWP]". unfold interp_conf.

    iModIntro.
    (* Same as the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL "HWP". { iApply (wp_wand with "HWP"). eauto. }
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. apply Hm'_flag.
  Qed.

End Adequacy.

Theorem counter_adequacy `{MachineParameters} `{memory_layout}
        (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory m →
  is_initial_registers reg →
  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  m' !! fail_flag = Some (inl 0%Z).
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              na_invΣ]).
  eapply (@counter_adequacy' Σ); typeclasses eauto.
Qed.
