From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From stdpp Require Import gmap fin_maps fin_sets.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra stdpp_comp iris_extra mkregion_helpers
     logrel_binary fundamental_binary linking malloc macros malloc_binary.
From cap_machine.examples Require Import
  disjoint_regions_tactics counter_binary_preamble_def counter_binary_preamble counter_binary_preamble_left.

Definition machine_component: Type := component nat.

Definition initial_state `{MachineParameters} (c: machine_component) (r:Reg): cfg cap_lang :=
  ([Seq (Instr Executable)], (r, segment c)).


(* Definition can_address_only (w: Word) (addrs: gset Addr): Prop :=
  match w with
  | WInt _ => True
  | WSealable (SCap p b e _) =>
      forall a, (b <= a < e)%a -> a ∈ addrs
  | _ => False
  end. *)

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


(* Definition initial_state_stk `{MachineParameters} (c: machine_component): cfg cap_lang :=
  match c with
  | Lib _ _ _ _ pre_comp => ([Seq (Instr Executable)], (∅, ∅)) (* dummy value *)
  | Main _ _ _ _ (ms, _, _) c_main => ([Seq (Instr Executable)], (<[PC := c_main]> (gset_to_gmap (WInt 0%Z) (list_to_set all_registers)), (ms : Mem)))
  end. *)

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

Definition code_all_ints (c : machine_component) :=
  (∀ w, w ∈ img (segment c) -> is_int w).

Definition is_initial_context (c : machine_component) (r : Reg) :=
  code_all_ints c ∧
  (∀ r', r' ≠ PC → r !! r' = Some (WInt 0)) ∧
  (∃ p b e a,
      r !! PC = Some (WCap p b e a) ∧
      (p = RX ∨ p = RWX)) ∧
  (∃ a, imports c = {[a := 0]}) ∧
  exports c = ∅.
  (* extra assumptions on adv imports and exports that make the proof easier to go through *)

Definition is_machine_program `{memory_layout} (c : machine_component) (r : Reg) :=
  is_program can_address_only_no_seals c r /\
  ∀ w, r !! PC = Some w -> isCorrectPC w.
Definition is_machine_context `{memory_layout} (c comp : machine_component) (r : Reg) :=
  is_context can_address_only_no_seals c comp r /\
  ∀ w, r !! PC = Some w -> isCorrectPC w.

(*Lemma initial_registers_full_map `{MachineParameters, memory_layout} (c : machine_component) reg :
  is_machine_program c →
  (initial_state c).2.1 = reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros Hprog Hini.
  inv Hprog.
  intros r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  rewrite lookup_insert_ne//.
  pose proof (all_registers_s_correct r) as Hin. clear -Hin.
  apply elem_of_dom. eauto.
Qed.

Definition ms_of (c : machine_component) : Mem :=
  match c with
  | Lib _ _ _ _ (ms,_,_) => ms
  | Main _ _ _ _ (ms, _, _) _ => ms
  end.

Definition main_of (c : machine_component) : Word :=
  match c with
  | Lib _ _ _ _ (_,_,_) => WInt 0%Z
  | Main _ _ _ _ (_,_,_) c_main => c_main
  end.*)

(* Instance merge_diagnone : DiagNone (λ o1 o2 : option Word, match o1 with *)
(*                                   | Some _ => o1 *)
(*                                   | None => o2 *)
(*                                                            end). *)
(* Proof. *)
(*   rewrite /DiagNone //. *)
(* Qed. *)

(* Instance merge_LeftId : LeftId eq None (λ o1 o2 : option Word, match o1 with *)
(*                                         | Some _ => o1 *)
(*                                         | None => o2 *)
(*                                                                end). *)
(* Proof. rewrite /LeftId //. Qed. *)
(* Instance addr_semiset : SemiSet Addr (list Addr). *)
(* Proof. apply listset_simple_set. *)

Lemma regions_disjoint_eq `{MachineParameters, memory_layout} (c_adv : machine_component) main (r : Reg) :
  is_machine_context c_adv comp1 r →
  is_machine_context c_adv comp2 r →
  is_initial_context c_adv r →
  r !! PC = Some main →

  ∃ (resolved_ms : gmap Addr Word),
      segment (c_adv ⋈ comp1) = mk_initial_memory_left ∪ resolved_ms ∧
      segment (c_adv ⋈ comp2) = mk_initial_memory_right ∪ resolved_ms ∧
      can_address_only_no_seals main (dom (resolved_ms)) ∧
      (∀ w, w ∈ img resolved_ms →
          (is_int w ∨
           w = WCap E counter_region_start counter_region_end counter_preamble_start)) ∧
      isCorrectPC main ∧
      mk_initial_memory_left ##ₘ resolved_ms ∧
      mk_initial_memory_right ##ₘ resolved_ms.
Proof.
  intros Hc1 Hc2 Hinit Hr.
  inversion Hc1 as [ [] ]. inversion Hc2 as [ [] _ ].
  inversion Hinit as (Hallints & _ & (p & b & e & a & Hrpbea & Hp) & (addr & Himp) & Hexp).
  set (resolved_ms := <[addr:=WCap E counter_region_start counter_region_end counter_preamble_start]> (segment c_adv)).
  exists resolved_ms.
  assert (Hdisj1: segment comp1 ##ₘ segment c_adv) by solve_can_link.
  assert (Hdisj2: segment comp2 ##ₘ segment c_adv) by solve_can_link.
  assert (Haddr: addr ∈ dom (segment c_adv)). {
    inversion Hcan_link as [ [_ Himp_cadv _ _] _ _ _].
    apply Himp_cadv. by rewrite elem_of_dom Himp lookup_insert.
  }
  rewrite -singleton_subseteq_l in Haddr.
  simpl in Hdisj1, Hdisj2.
  assert (Hdisj3: mk_initial_memory_left ##ₘ resolved_ms). {
    unfold resolved_ms.
    by rewrite map_disjoint_dom dom_insert_L (subseteq_union_1_L _ _ Haddr) -map_disjoint_dom.
  }
  assert (Hdisj4: mk_initial_memory_right ##ₘ resolved_ms). {
    unfold resolved_ms.
    by rewrite map_disjoint_dom dom_insert_L (subseteq_union_1_L _ _ Haddr) -map_disjoint_dom.
  }

  repeat split_and.
  - rewrite map_union_comm; [|done]. simpl.
    rewrite Himp resolve_imports_imports_empty. f_equal.
    unfold resolve_imports.
    by rewrite map_compose_singletons -insert_union_singleton_l.
  - rewrite map_union_comm; [|done]. simpl.
    rewrite Himp resolve_imports_imports_empty. f_equal.
    unfold resolve_imports.
    by rewrite map_compose_singletons -insert_union_singleton_l.
  - replace (dom resolved_ms) with (dom (segment c_adv)).
    apply (Hwr_regs main (elem_of_map_img_2 _ _ _ Hr)).
    unfold resolved_ms. by rewrite dom_insert_L (subseteq_union_1_L _ _ Haddr).
  - intros w Hw. apply map_img_insert_subseteq, elem_of_union in Hw as [Hw | Hw].
    + rewrite elem_of_singleton in Hw. by right.
    + left. by apply Hallints.
  - apply (H2 main Hr).
  - done.
  - done.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Lemma regspec_mapsto_alloc {cfg: cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) r (w : Word) :
    σ.1 !! r = None →
    spec_res e σ ==∗ spec_res e (<[r:=w]> σ.1,σ.2) ∗ r ↣ᵣ w.
  Proof.
    iIntros (Hnone) "Hσ".
    rewrite /spec_res /regspec_mapsto.
    iMod (own_update with "Hσ") as "[Hσ Hr]".
    { eapply auth_update_alloc,prod_local_update_2,prod_local_update_1.
      eapply (alloc_singleton_local_update (to_spec_map σ.1) r (1%Qp, to_agree w)).
      by rewrite lookup_fmap Hnone. done. }
    iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
  Qed.
  Lemma memspec_mapsto_alloc {cfg: cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) a (w : Word) :
    σ.2 !! a = None →
    spec_res e σ ==∗ spec_res e (σ.1,<[a:=w]> σ.2) ∗ a ↣ₐ w.
  Proof.
    iIntros (Hnone) "Hσ".
    rewrite /spec_res /memspec_mapsto.
    iMod (own_update with "Hσ") as "[Hσ Hr]".
    { eapply auth_update_alloc,prod_local_update_2,prod_local_update_2.
      eapply (alloc_singleton_local_update (to_spec_map σ.2) a (1%Qp, to_agree w)).
      by rewrite lookup_fmap Hnone. done. }
    iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
  Qed.
  Lemma regspec_alloc_big {cfg: cfgSG Σ} e σ σ' σs :
    σ' ##ₘ σ →
    spec_res e (σ,σs) ==∗
    spec_res e (σ' ∪ σ,σs) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ᵣ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    iMod (regspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
      by apply lookup_union_None. done.
  Qed.
  Lemma memspec_alloc_big {cfg: cfgSG Σ} e σ σ' σr :
    σ' ##ₘ σ →
    spec_res e (σr, σ) ==∗
    spec_res e (σr, map_union σ' σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ₐ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert //.
    assert (map_union (<[l:=v]> σ') σ = <[l:=v]> (map_union σ' σ)) as ->.
    { rewrite insert_union_l. auto. }
    iMod (memspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
    simpl. rewrite lookup_union_None//. done.
  Qed.

  Instance list_addr_semiset : SemiSet Addr (list Addr).
  Proof.
    apply Build_SemiSet.
    - intros. intros Hcontr. inversion Hcontr.
    - intros. split;intros.
      inversion H;subst;auto. inversion H2.
      rewrite /singleton /Singleton_list. apply elem_of_list_singleton. auto.
    - intros. split;intros.
      rewrite /union /Union_list in H.
      apply elem_of_app in H. auto.
      rewrite /union /Union_list.
      apply elem_of_app. auto.
  Qed.

  Lemma establish_interp `{memG Σ,regG Σ,cfgSG Σ,logrel_na_invs Σ} ms v :
    (∀ w, w ∈ img ms → (is_int w ∨ w = v)) ->
    interp (v,v) -∗
    ([∗ map] k↦x ∈ ms, k ↦ₐ x ∗ k ↣ₐ x) ={⊤}=∗ ([∗ map] k↦x ∈ ms, inv (logN .@ k) (∃ x1 x2, k ↦ₐ x1 ∗ k ↣ₐ x2 ∗ interp(x1,x2))).
  Proof.
    iIntros (Hcond) "#Hv".
    iInduction (ms) as [] "IH" using map_ind.
    { rewrite !big_sepM_empty. done. }
    { rewrite !big_sepM_insert//.
      iIntros "[[Hi Hsi] Hmap]".
      iDestruct ("IH" with "[] Hmap") as ">Hmap".
      { iPureIntro. intros w Hin. apply Hcond.
        rewrite map_img_insert elem_of_union. right.
        by rewrite delete_notin. }
      iFrame.
      specialize (Hcond x (elem_of_map_img_insert _ _ _)).
      destruct Hcond as [Hint | Heq];auto.
      - iApply inv_alloc. iNext. iExists x,x. iFrame.
        iApply fixpoint_interp1_eq.
        destruct x;[|destruct sb;inv Hint|inv Hint].
        iSimpl. auto.
      - subst x.
        iApply inv_alloc.
        iNext. iExists v,v. iFrame "∗ #".
    }
  Qed.



  Context {cfgg : inG Σ (authR cfgUR)}.

  Definition codeN : namespace := nroot .@ "conf" .@ "code".

  Lemma confidentiality_adequacy_l' {ML:memory_layout} c_adv r (es: list cap_lang.expr)
        reg' m' :
    is_machine_context c_adv comp1 r →
    is_machine_context c_adv comp2 r →
    is_initial_context c_adv r →
    rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hstep.
    inversion Hc as (Hallints & Hregs & (p & b & e & a & Hrpbea & Hp) & (addr & Himp) & Hexp).
    (* set (reg1 := (initial_state_stk p1).2.1). *)
    set (m1 := (initial_state (c_adv ⋈ comp1) r).2.2).
    (* set (reg2 := (initial_state_stk p2).2.1). *)
    set (m2 := (initial_state (c_adv ⋈ comp2) r).2.2).
    cut (@adequate cap_lang NotStuck (Seq (Instr Executable)) (r,m1)
                   (λ v _, v = HaltedV → ∃ thp' conf', rtc erased_step (initial_state (c_adv ⋈ comp2) r)
                                             (of_val HaltedV :: thp', conf'))).
    { destruct 1. destruct Hm1 as [ [] ].
      apply adequate_result in Hstep. auto. auto. }
    eapply (wp_adequacy Σ _); iIntros (Hinv ?).

    iMod (gen_heap_init (m1:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (r:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (seal_store_init) as (seal_storeg) "Hseal_store".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    iMod (own_alloc (● (Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅))
                       ⋅ ◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)))
      as (γc) "[Hcfg1 Hcfg2]".
    { apply auth_both_valid_discrete. split=>//. }

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    set (Hcfg := CFGSG _ _ γc).

    iMod (regspec_alloc_big _ ∅ r ∅ with "[Hcfg1]") as "(Hcfg1 & Hregspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.
    iMod (memspec_alloc_big _ ∅ m2 r with "[Hcfg1]") as "(Hcfg1 & Hmemspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.

    pose proof (
      @counter_binary_preamble.counter_preamble_spec Σ memg regg logrel_na_invs Hcfg
      ) as Spec.

    pose proof (regions_disjoint_eq c_adv (WCap p b e a) r Hm1 Hm2 Hc Hrpbea)
      as (resolved_ms & Hm1eq & Hm2eq & Hcanaddress & Hresolved_ms_spec & Hreg & Hdisj & Hdisj').

    unfold m1, m2, initial_state. rewrite {2}Hm1eq {2}Hm2eq.

    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]";[auto|].
    iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hadvspec]";[auto|].

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

    (* Allocate the spec invariant *)
    iMod (inv_alloc specN _ (spec_inv ([Seq (Instr Executable)],(r,m2)) ) with "[Hcfg1]") as "#Hspec_∅".
    { iNext. iExists _,_. iFrame. iPureIntro. rewrite /m2 /=. left. }
    iAssert (spec_ctx)%I as "#Hspec".
    { iExists _. iFrame "#". }

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
    iMod (Spec with "[$Hspec $Hinv_malloc $Hcounter_preamble $Hcounter_body
                    $Hcounter_preamble_spec $Hcounter_body_spec $Hcounter_link $Hcounter_link_spec $Hlink1 $Hlink1']") as "#Hlib".
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

    (* Validity of the adv region *)
    iDestruct (big_sepM_sep with "[$Hadv $Hadvspec]") as "Hadv".
    iMod (establish_interp with "Hlib Hadv") as "#Hadvvalid"; [auto|].

    (* Validity of Main *)
    inversion Hreg as [? ? ? ? Hbounds _].
    iAssert (interp (WCap p b e a,WCap p b e a)) as "#Hval".
    { clear -Hbounds Hp Hcanaddress.
      iApply fixpoint_interp1_eq.
      destruct Hp as [-> | ->];simpl.
      - iSplit;auto.
        iApply big_sepL_forall.
        iIntros (k x Hin).
        apply elem_of_list_lookup_2 in Hin.
        apply elem_of_finz_seq_between in Hin. apply Hcanaddress in Hin.
        apply elem_of_dom in Hin as [? ?].
        iExists interp. iSplit;auto.
        iDestruct (big_sepM_lookup with "Hadvvalid") as "$".
        eauto.
      - iSplit;auto.
        iApply big_sepL_forall.
        iIntros (k x Hin).
        apply elem_of_list_lookup_2 in Hin.
        apply elem_of_finz_seq_between in Hin. apply Hcanaddress in Hin.
        apply elem_of_dom in Hin as [? ?].
        iExists interp. iSplit;auto.
        iDestruct (big_sepM_lookup with "Hadvvalid") as "$".
        eauto.
    }

    iDestruct (fundamental_binary (r,r) with "[Hspec] Hval") as "Hval_exec".
    { iExact "Hspec". }

    unfold interp_expression. iSimpl in "Hval_exec".
    iDestruct ("Hval_exec" with "[Hreg Hregspec Hcfg2 $Hna]") as "[_ Hconf]".
    { iSplitR;[|iSplitL "Hreg";[|iSplitL "Hregspec"] ];[..|iExact "Hcfg2"].
      - iSplit.
        + iPureIntro. intros x. simpl. clear -Hm1.
          inversion Hm1 as [ [ _ _ Hall _ _ ] _ ]. by split.
        + iIntros (r' v1 v2 Hne Hr Hr').
          rewrite (Hregs r' Hne) in Hr, Hr'.
          apply (inj Some) in Hr, Hr'. rewrite -Hr -Hr'.
          iApply fixpoint_interp1_eq. auto.
      - rewrite insert_id. iFrame. done.
      - rewrite insert_id. iFrame. done. }

    unfold interp_conf.
    iModIntro.
    iExists (fun σ κs => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. iFrame. iApply wp_fupd. iApply wp_wand_r. iFrame.

    iIntros (v) "Hcond".
    destruct v;[|iModIntro;iIntros (Hcontr);done..].
    iDestruct ("Hcond" $! eq_refl) as (r') "(Hj & Hcond)".
    iInv specN as ">Hres" "Hcls". iDestruct "Hres" as (e' σ') "[Hown Hsteps]".
    iDestruct "Hsteps" as %Hsteps.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    iMod ("Hcls" with "[Hown]") as "_".
    { iNext. iExists _,_. eauto. }
    iModIntro.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    iIntros (_).
    apply prod_included in Hincl as [Hincl Hincl']. simpl in *.
    revert Hincl; rewrite Excl_included =>Hincl.
    apply leibniz_equiv in Hincl as <-.
    iExists [],σ'. iPureIntro. apply Hsteps.
  Qed.


  Lemma confidentiality_adequacy_r' {ML:memory_layout} c_adv r (es: list cap_lang.expr)
      reg' m' :
    is_machine_context c_adv comp1 r →
    is_machine_context c_adv comp2 r →
    is_initial_context c_adv r →
    rtc erased_step (initial_state (c_adv ⋈ comp2) r) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state (c_adv ⋈ comp1) r) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hstep.
    inversion Hc as (Hallints & Hregs & (p & b & e & a & Hrpbea & Hp) & (addr & Himp) & Hexp).
    (* set (reg1 := (initial_state_stk p1).2.1). *)
    set (m1 := (initial_state (c_adv ⋈ comp1) r).2.2).
    (* set (reg2 := (initial_state_stk p2).2.1). *)
    set (m2 := (initial_state (c_adv ⋈ comp2) r).2.2).
    cut (@adequate cap_lang NotStuck (Seq (Instr Executable)) (r,m2)
                   (λ v _, v = HaltedV → ∃ thp' conf', rtc erased_step (initial_state (c_adv ⋈ comp1) r)
                                             (of_val HaltedV :: thp', conf'))).
    { destruct 1. destruct Hm2 as [ [] ].
      apply adequate_result in Hstep. auto. auto. }
    eapply (wp_adequacy Σ _); iIntros (Hinv ?).

    iMod (gen_heap_init (m2:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (r:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (seal_store_init) as (seal_storeg) "Hseal_store".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    iMod (own_alloc (● (Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅))
                       ⋅ ◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)))
      as (γc) "[Hcfg1 Hcfg2]".
    { apply auth_both_valid_discrete. split=>//. }

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    set (Hcfg := CFGSG _ _ γc).

    iMod (regspec_alloc_big _ ∅ r ∅ with "[Hcfg1]") as "(Hcfg1 & Hregspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.
    iMod (memspec_alloc_big _ ∅ m1 r with "[Hcfg1]") as "(Hcfg1 & Hmemspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.

    pose proof (
      @counter_binary_preamble_left.counter_preamble_spec Σ memg regg logrel_na_invs Hcfg
      ) as Spec.

    pose proof (regions_disjoint_eq c_adv (WCap p b e a) r Hm1 Hm2 Hc Hrpbea)
      as (resolved_ms & Hm1eq & Hm2eq & Hcanaddress & Hresolved_ms_spec & Hreg & Hdisj & Hdisj').

    unfold m1, m2, initial_state. rewrite {2}Hm1eq {2}Hm2eq.

    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]";[auto|].
    iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hadvspec]";[auto|].

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

    (* Allocate the spec invariant *)
    iMod (inv_alloc specN _ (spec_inv ([Seq (Instr Executable)],(r,m1)) ) with "[Hcfg1]") as "#Hspec_∅".
    { iNext. iExists _,_. iFrame. iPureIntro. rewrite /m1 /=. left. }
    iAssert (spec_ctx)%I as "#Hspec".
    { iExists _. iFrame "#". }

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
    iMod (Spec with "[$Hspec $Hinv_malloc $Hcounter_preamble $Hcounter_body
                    $Hcounter_preamble_spec $Hcounter_body_spec $Hcounter_link $Hcounter_link_spec $Hlink1 $Hlink1']") as "#Hlib".
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

    (* Validity of the adv region *)
    iDestruct (big_sepM_sep with "[$Hadv $Hadvspec]") as "Hadv".
    iMod (establish_interp with "Hlib Hadv") as "#Hadvvalid"; [auto|].

    (* Validity of Main *)
    inversion Hreg as [? ? ? ? Hbounds _].
    iAssert (interp (WCap p b e a,WCap p b e a)) as "#Hval".
    { clear -Hbounds Hp Hcanaddress.
      iApply fixpoint_interp1_eq.
      destruct Hp as [-> | ->];simpl.
      - iSplit;auto.
        iApply big_sepL_forall.
        iIntros (k x Hin).
        apply elem_of_list_lookup_2 in Hin.
        apply elem_of_finz_seq_between in Hin. apply Hcanaddress in Hin.
        apply elem_of_dom in Hin as [? ?].
        iExists interp. iSplit;auto.
        iDestruct (big_sepM_lookup with "Hadvvalid") as "$".
        eauto.
      - iSplit;auto.
        iApply big_sepL_forall.
        iIntros (k x Hin).
        apply elem_of_list_lookup_2 in Hin.
        apply elem_of_finz_seq_between in Hin. apply Hcanaddress in Hin.
        apply elem_of_dom in Hin as [? ?].
        iExists interp. iSplit;auto.
        iDestruct (big_sepM_lookup with "Hadvvalid") as "$".
        eauto.
    }

    iDestruct (fundamental_binary (r,r) with "[Hspec] Hval") as "Hval_exec".
    { iExact "Hspec". }

    unfold interp_expression. iSimpl in "Hval_exec".
    iDestruct ("Hval_exec" with "[Hreg Hregspec Hcfg2 $Hna]") as "[_ Hconf]".
    { iSplitR;[|iSplitL "Hreg";[|iSplitL "Hregspec"] ];[..|iExact "Hcfg2"].
      - iSplit.
        + iPureIntro. intros x. simpl. clear -Hm1.
          inversion Hm1 as [ [ _ _ Hall _ _ ] _ ]. by split.
        + iIntros (r' v1 v2 Hne Hr Hr').
          rewrite (Hregs r' Hne) in Hr, Hr'.
          apply (inj Some) in Hr, Hr'. rewrite -Hr -Hr'.
          iApply fixpoint_interp1_eq. auto.
      - rewrite insert_id. iFrame. done.
      - rewrite insert_id. iFrame. done. }

    unfold interp_conf.
    iModIntro.
    iExists (fun σ κs => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. iFrame. iApply wp_fupd. iApply wp_wand_r. iFrame.

    iIntros (v) "Hcond".
    destruct v;[|iModIntro;iIntros (Hcontr);done..].
    iDestruct ("Hcond" $! eq_refl) as (r') "(Hj & Hcond)".
    iInv specN as ">Hres" "Hcls". iDestruct "Hres" as (e' σ') "[Hown Hsteps]".
    iDestruct "Hsteps" as %Hsteps.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    iMod ("Hcls" with "[Hown]") as "_".
    { iNext. iExists _,_. eauto. }
    iModIntro.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    iIntros (_).
    apply prod_included in Hincl as [Hincl Hincl']. simpl in *.
    revert Hincl; rewrite Excl_included =>Hincl.
    apply leibniz_equiv in Hincl as <-.
    iExists [],σ'. iPureIntro. apply Hsteps.
  Qed.

End Adequacy.
