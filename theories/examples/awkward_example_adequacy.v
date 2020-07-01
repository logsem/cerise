From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants sts
     region_invariants_revocation region_invariants_static
     region_invariants_uninitialized.
From cap_machine.examples Require Import
     stack_macros malloc awkward_example_u awkward_example_preamble.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout `{MachineParameters} := {
  (* awkward example: preamble & body *)
  awk_region_start : Addr;
  awk_preamble_start : Addr;
  awk_body_start : Addr;
  awk_region_end : Addr;

  (* pointer to the linking table, at the beginning of the region *)
  awk_linking_ptr_size :
    (awk_region_start + 1)%a = Some awk_preamble_start;

  (* preamble code, that allocates the closure *)
  awk_preamble_size :
    (awk_preamble_start + awkward_preamble_instrs_length)%a
    = Some awk_body_start;

  (* code of the body, wrapped in the closure allocated by the preamble *)
  awk_body_size :
    (awk_body_start + awkward_instrs_length)%a
    = Some awk_region_end;

  (* stack *)
  stack_start : Addr;
  stack_end : Addr;

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
        region_addrs stack_start stack_end;
        region_addrs awk_body_start awk_region_end;
        region_addrs awk_preamble_start awk_body_start;
        [awk_region_start]
       ];
}.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (region_addrs r_start r_end) contents).

Definition offset_to_awkward `{memory_layout} : Z :=
  (* in this setup, the body of the awkward examples comes just after the code
     of the preamble *)
  (awkward_preamble_instrs_length - awkward_preamble_move_offset)%Z.

(* FIXME: the link table permission could be restricted to RO *)
Definition is_initial_memory `{memory_layout} (m: gmap Addr Word) :=
  ∃ (adv_val stack_val: list Word),
  m =   (* pointer to the linking table *)
        list_to_map [(awk_region_start,
                      inr (RW, Global, link_table_start, link_table_end, link_table_start))]
      ∪ mkregion awk_preamble_start awk_body_start
           (* preamble: code that creates the awkward example closure *)
          (awkward_preamble_instrs 0%Z (* offset to malloc in linking table *)
             offset_to_awkward (* offset to the body of the example *))
      ∪ mkregion awk_body_start awk_region_end
           (* body of the awkward example, that will be encapsulated in the closure
              created by the preamble *)
          (awkward_instrs 1%Z (* offset to fail in the linking table *)
             r_adv (* register used to call to arbitrary code *))
      ∪ mkregion stack_start stack_end
          (* initial content of the stack: can be anything *)
          stack_val
      ∪ mkregion adv_start adv_end
          (* adversarial code: any code or data, but no capabilities (see condition below) *)
          adv_val
      ∪ mkregion malloc_start malloc_memptr
          (* code for the malloc subroutine *)
          malloc_subroutine_instrs
      ∪ list_to_map
          (* Capability to malloc's memory pool, used by the malloc subroutine *)
          [(malloc_memptr, inr (RWX, Global, malloc_memptr, malloc_end, malloc_mem_start))]
      ∪ mkregion malloc_mem_start malloc_end
          (* Malloc's memory pool, initialized to zero *)
          (region_addrs_zeroes malloc_mem_start malloc_end)
      ∪ mkregion fail_start fail_end
          ((* code for the failure subroutine *)
            assert_fail_instrs ++
           (* pointer to the "failure" flag, set to 1 by the routine *)
           [inr (RW, Global, fail_flag, fail_flag_next, fail_flag)])
      ∪ mkregion link_table_start link_table_end
          (* link table, with pointers to the malloc and failure subroutines *)
          [inr (E, Global, malloc_start, malloc_end, malloc_start);
           inr (E, Global, fail_start, fail_end, fail_start)]
      ∪ list_to_map [(fail_flag, inl 0%Z)] (* failure flag, initially set to 0 *)
  ∧
  (* the adversarial region in memory must only contain instructions, no
     capabilities (it can thus only access capabilities the awkward preamble
     passes it through the registers) *)
  Forall (λ w, is_cap w = false) adv_val
  ∧
  (adv_start + length adv_val)%a = Some adv_end
  ∧
  (stack_start + length stack_val)%a = Some stack_end.

Definition is_initial_registers `{memory_layout} (reg: gmap RegName Word) :=
  reg !! PC = Some (inr (RX, Global, awk_region_start, awk_region_end, awk_preamble_start)) ∧
  reg !! r_stk = Some (inr (URWLX, Local, stack_start, stack_end, stack_start)) ∧
  reg !! r_t0 = Some (inr (RWX, Global, adv_start, adv_end, adv_start)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; r_stk; r_t0 ]} : gset RegName) →
    ∃ (w:Word), reg !! r = Some w ∧ is_cap w = false).

Lemma initial_registers_full_map `{MachineParameters, memory_layout} reg :
  is_initial_registers reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hstk & Hr0 & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_stk)) as [->|]. by eauto.
  destruct (decide (r = r_t0)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

(* TODO: move elsewhere *)
Section WorldUpdates.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Lemma extend_region_perm_sepL2 E W l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     Forall (λ k, std W !! k = None) l1 →
     (sts_full_world W -∗ region W -∗
     ([∗ list] k;v ∈ l1;l2, k ↦ₐ[p] v ∗ φ (W, v) ∗ future_priv_mono φ v)

     ={E}=∗

     region (std_update_multiple W l1 Permanent)
     ∗ ([∗ list] k ∈ l1, rel k p φ)
     ∗ sts_full_world (std_update_multiple W l1 Permanent))%I.
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros * ? [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (cap_duplicate_false with "[$H1 $H2]"). auto. }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iDestruct (extend_region_perm with "Hf Hsts Hr Ha [Hφ]") as ">(? & ? & ?)"; auto.
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
        eapply Forall_impl; eauto.
        intros. by rewrite not_elem_of_dom. }
      iModIntro. cbn. iFrame. }
  Qed.

  Lemma extend_region_static_single E W l p v φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     l ∉ dom (gset Addr) (std W) →
     (sts_full_world W -∗ region W -∗ l ↦ₐ[p] v
     ={E}=∗
     region (<s[l := Static {[l := v]}]s>W)
     ∗ rel l p φ
     ∗ sts_full_world (<s[l := Static {[l := v]} ]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1) "Hfull Hreg Hl".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HdomM & HdomMρ & Hpreds)".
    iDestruct "HdomM" as %HdomM. iDestruct "HdomMρ" as %HdomMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l (Static {[l:=v]})
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    eapply (related_sts_pub_world_fresh W l (Static {[l:=v]})) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomM. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists (Static {[l:=v]}). iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,_,φ. iSplitR;[auto|]. iFrame "∗ #".
        iSplitR;[done|]. iExists _. iFrame. repeat iSplit;auto.
        iPureIntro. apply lookup_singleton.
        iPureIntro. intro. rewrite dom_singleton elem_of_singleton.
        intros ->. apply lookup_insert. }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Heq Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hg Hne') "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. split;auto.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma dom_map_imap_full {K A B}
        `{Countable A, EqDecision A, Countable B, EqDecision B, Countable K, EqDecision K}
        (f: K -> A -> option B) (m: gmap K A):
    (∀ k a, m !! k = Some a → is_Some (f k a)) →
    dom (gset K) (map_imap f m) = dom (gset K) m.
  Proof.
    intros Hf.
    apply elem_of_equiv_L. intros k.
    rewrite -!elem_of_gmap_dom map_lookup_imap.
    destruct (m !! k) eqn:Hmk.
    - destruct (Hf k a Hmk) as [? Hfk]. cbn. rewrite Hfk. split; eauto.
    - cbn. split; inversion 1; congruence.
  Qed.

  Lemma override_uninitializedW_dom' W (m: gmap Addr Word) :
    dom (gset Addr) (override_uninitializedW m W).1 =
    dom (gset Addr) m ∪ dom (gset Addr) W.1.
  Proof.
    rewrite /override_uninitializedW /override_uninitialized.
    rewrite dom_union_L dom_difference_het.
    rewrite dom_map_imap_full. 2: by intros; eauto.
    set Dm := dom (gset Addr) m.
    set DW := dom (gset Addr) W.1. clearbody Dm DW.
    rewrite elem_of_equiv_L. intro x.
    rewrite !elem_of_union !elem_of_difference.
    split.
    - intros [? | [? ?] ]. auto. auto.
    - intros [? | ?]. auto. destruct (decide (x ∈ Dm)); auto.
  Qed.

  Lemma extend_region_static_single_sepM E W (m: gmap Addr Word) p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     (∀ k, is_Some (m !! k) → std W !! k = None) →
     (sts_full_world W -∗ region W -∗
     ([∗ map] k↦v ∈ m, k ↦ₐ[p] v)

     ={E}=∗

     region (override_uninitializedW m W)
     ∗ ([∗ map] k↦_ ∈ m, rel k p φ)
     ∗ sts_full_world (override_uninitializedW m W))%I.
  Proof.
    induction m using map_ind.
    { intros. rewrite !override_uninitializedW_empty !big_sepM_empty.
      iIntros. by iFrame. }
    { iIntros (? HnW) "Hsts Hr H". rewrite big_sepM_insert //.
      iDestruct "H" as "(Hk & Hm)".
      rewrite !override_uninitializedW_insert.
      iMod (IHm with "Hsts Hr Hm") as "(Hr & Hm & Hsts)"; auto.
      { intros. apply HnW. rewrite lookup_insert_is_Some.
        destruct (decide (i = k)); auto. }
      iDestruct (extend_region_static_single with "Hsts Hr Hk")
        as ">(Hr & Hrel & Hsts)"; auto.
      { rewrite override_uninitializedW_dom'.
        rewrite not_elem_of_union !not_elem_of_dom. split; auto.
        apply HnW. rewrite lookup_insert //. eauto. }
      iFrame. iModIntro. iApply big_sepM_insert; eauto. }
  Qed.

End WorldUpdates.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {MonRef: @MonRefG (leibnizO _) CapR_rtc Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {heappreg: heapPreG Σ}.
  Context `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).

  Lemma dom_mkregion_incl a e l:
    dom (gset Addr) (mkregion a e l) ⊆ list_to_set (region_addrs a e).
  Proof.
    rewrite /mkregion. generalize (region_addrs a e). induction l.
    { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
    { intros ll. destruct ll as [| x ll].
      - cbn. rewrite dom_empty_L. done.
      - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
        set_solver. }
  Qed.

  Lemma dom_mkregion_incl_rev a e l:
    (a + length l = Some e)%a →
    list_to_set (region_addrs a e) ⊆ dom (gset Addr) (mkregion a e l).
  Proof.
    rewrite /mkregion. intros Hl.
    assert (length (region_addrs a e) = length l) as Hl'.
    { rewrite region_addrs_length /region_size. solve_addr. }
    clear Hl. revert Hl'. generalize (region_addrs a e). induction l.
    { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
      destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
    { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
      cbn [list_to_set zip zip_with list_to_map foldr fst snd].
      rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
      specialize (IHl ll Hll). set_solver. }
  Qed.

  Lemma dom_mkregion_eq a e l:
    (a + length l = Some e)%a →
    dom (gset Addr) (mkregion a e l) = list_to_set (region_addrs a e).
  Proof.
    intros Hlen. apply (anti_symm _).
    - apply dom_mkregion_incl.
    - by apply dom_mkregion_incl_rev.
  Qed.

  Lemma in_dom_mkregion a e l k:
    k ∈ dom (gset Addr) (mkregion a e l) →
    k ∈ region_addrs a e.
  Proof.
    intros H.
    pose proof (dom_mkregion_incl a e l) as HH.
    rewrite elem_of_subseteq in HH |- * => HH.
    specialize (HH _ H). eapply elem_of_list_to_set; eauto.
  Qed.

  Lemma in_dom_mkregion' a e l k:
    (a + length l = Some e)%a →
    k ∈ region_addrs a e →
    k ∈ dom (gset Addr) (mkregion a e l).
  Proof.
    intros. rewrite dom_mkregion_eq // elem_of_list_to_set //.
  Qed.

  Lemma disjoint_mono_l A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Y ## Z → X ## Z.
  Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

  Lemma disjoint_mono_r A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Z ## Y → Z ## X.
  Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

  Lemma dom_list_to_map_singleton (x:Addr) (y:Word):
    dom (gset Addr) (list_to_map [(x, y)] : gmap Addr Word) = list_to_set [x].
  Proof. rewrite dom_insert_L /= dom_empty_L. set_solver. Qed.

  Lemma list_to_set_disj (l1 l2: list Addr) : l1 ## l2 → (list_to_set l1: gset Addr) ## list_to_set l2.
  Proof.
    intros * HH. rewrite elem_of_disjoint. intros x.
    rewrite !elem_of_list_to_set. rewrite elem_of_disjoint in HH |- *. eauto.
  Qed.

  Ltac disjoint_map_to_list :=
    rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
    eapply disjoint_mono_l;
    rewrite ?dom_list_to_map_singleton;
    repeat (
      try lazymatch goal with
          | |- _ ∪ _ ⊆ _ =>
            etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
          end;
      [ first [ apply dom_mkregion_incl | reflexivity ] |..]
    );
    try match goal with |- _ ## dom _ (mkregion _ _ _) =>
      eapply disjoint_mono_r; [ apply dom_mkregion_incl |] end;
    rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
    apply list_to_set_disj.

  Lemma contiguous_between_region_addrs a e :
    (a <= e) %a → contiguous_between (region_addrs a e) a e.
  Proof. intros; by apply contiguous_between_of_region_addrs. Qed.

  Lemma mkregion_sepM_to_sepL2 (a e: Addr) l (φ: Addr → Word → iProp Σ) :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (region_addrs a e); l, φ k v).
  Proof.
    rewrite /mkregion. revert a e. induction l as [| x l].
    { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
      rewrite /region_addrs region_size_0. 2: solve_addr. cbn. eauto. }
    { cbn. intros a e Hlen. rewrite region_addrs_cons. 2: solve_addr.
      cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      iFrame. iApply (IHl with "H"). solve_addr. }
  Qed.

  (* TODO: move to iris? *)
  Lemma big_sepL2_bupd
     : ∀ (PROP : bi) (H : BiBUpd PROP) (A B : Type) (Φ : A → B → PROP) (l1 : list A) (l2: list B),
         ([∗ list] k;x ∈ l1;l2, |==> Φ k x) -∗ |==> [∗ list] k;x ∈ l1;l2, Φ k x.
  Proof.
    intros. revert l2. induction l1 as [| x l1].
    { intros. iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. cbn in Hlen.
      destruct l2; [| by inversion Hlen]. cbn. eauto. }
    { intros. iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen. cbn in Hlen.
      destruct l2; [by inversion Hlen |]. cbn. iDestruct "H" as "[>? H]".
      iDestruct (IHl1 with "H") as ">?". iModIntro. iFrame. }
  Qed.

  Lemma MonRefAlloc_sepL2 `{memG Σ} (p:Perm) (l1: list Addr) (l2: list Word) :
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ[p] v).
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_mono with "H") as "H".
    { intros. apply MonRefAlloc. }
    iDestruct (big_sepL2_bupd with "H") as "H". eauto.
  Qed.

  Lemma MonRefAlloc_sepM `{memG Σ} (p:Perm) (m: gmap Addr Word) :
    ([∗ map] k↦v ∈ m, k ↦ₐ v) ==∗ ([∗ map] k↦v ∈ m, k ↦ₐ[p] v).
  Proof.
    iIntros "H".
    iDestruct (big_sepM_mono with "H") as "H".
    { intros. apply MonRefAlloc. }
    iDestruct (big_sepM_bupd with "H") as "H". eauto.
  Qed.

  Lemma mkregion_prepare `{memG Σ} p (a e: Addr) l :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (region_addrs a e); l, k ↦ₐ[p] v).
  Proof.
    iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
    iMod (MonRefAlloc_sepL2 with "H"). eauto.
  Qed.

  Definition flagN : namespace := nroot .@ "awk" .@ "fail_flag".
  Definition mallocN : namespace := nroot .@ "awk" .@ "malloc".

  Lemma awkward_example_adequacy' `{memory_layout} (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
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

    destruct Hm as (adv_val & stack_val & Hm & Hadv_val & adv_size & stack_size).
    iMod (gen_heap_init (∅:Mem)) as (mem_heapg) "Hmem_ctx".
    iMod (gen_heap_init (∅:Reg)) as (reg_heapg) "Hreg_ctx".
    unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*)
    set W0 := ((∅, (∅, ∅)) : WORLD).
    iMod heap_init as (heapg) "HRELS".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

    pose proof (
      @awkward_preamble_spec Σ memg regg stsg heapg MonRef logrel_na_invs
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
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_stack & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hstack]".
    { disjoint_map_to_list. set_solver +Hdisj_stack. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_awk_body & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hawk_body]".
    { disjoint_map_to_list. set_solver +Hdisj_awk_body. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_awk_preamble & _).
    iDestruct (big_sepM_union with "Hmem") as "[Hawk_link Hawk_preamble]".
    { disjoint_map_to_list. set_solver +Hdisj_awk_preamble. }
    iDestruct (big_sepM_insert with "Hawk_link") as "[Hawk_link _]". by apply lookup_empty.
    cbn [fst snd].
    clear Hdisj_fail_flag Hdisj_link_table Hdisj_fail Hdisj_malloc_mem Hdisj_malloc_memptr
          Hdisj_malloc_code Hdisj_adv Hdisj_stack Hdisj_awk_body Hdisj_awk_preamble.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare RW with "Hlink_table") as ">Hlink_table". by apply link_table_size.
    iDestruct (mkregion_prepare RW with "Hfail") as ">Hfail". by apply fail_size.
    iDestruct (mkregion_prepare RWX with "Hmalloc_mem") as ">Hmalloc_mem".
    { rewrite replicate_length /region_size. clear.
      generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
    iMod (MonRefAlloc _ _ RWX with "Hmalloc_memptr") as "Hmalloc_memptr".
    iDestruct (mkregion_prepare RX with "Hmalloc_code") as ">Hmalloc_code".
      by apply malloc_code_size.
    iDestruct (mkregion_prepare RWX with "Hadv") as ">Hadv". by apply adv_size.
    (* Keep the stack as a sepM, it'll be easier to allocate the corresponding
       uninitialized region later. *)
    iDestruct (MonRefAlloc_sepM RWLX with "Hstack") as ">Hstack".
    iDestruct (mkregion_prepare RWX with "Hawk_preamble") as ">Hawk_preamble".
      by apply awk_preamble_size.
    iDestruct (mkregion_prepare RWX with "Hawk_body") as ">Hawk_body". by apply awk_body_size.
    iMod (MonRefAlloc _ _ RWX (* FIXME: RO instead?? *) with "Hawk_link") as "Hawk_link".
    rewrite -/(awkward_example _ _ _ _) -/(awkward_preamble _ _ _ _).

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
      iFrame. iPureIntro. generalize malloc_code_size malloc_mem_size malloc_memptr_size. cbn.
      clear; solve_addr. }

    (* Allocate a permanent region for the adversary code *)

    iAssert (region W0) with "[HRELS]" as "Hr".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    iAssert (⌜∀ k,
      is_Some (mkregion stack_start stack_end stack_val !! k) →
      k ∉ region_addrs adv_start adv_end⌝)%I
    as %Hstack_adv_disj.
    { iIntros (k Hk Hk'). destruct Hk.
      iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto.
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hadv") as %Hlen.
      destruct (lookup_lt_is_Some_2 adv_val i).
      { rewrite -Hlen. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hadv") as "Hk'"; eauto.
      iApply (cap_duplicate_false with "[$Hk $Hk']"). done. }

    iMod (extend_region_perm_sepL2 _ _ _ _ RWX (λ Wv, interp Wv.1 Wv.2)
            with "Hsts Hr [Hadv]") as "(Hr & Hadv & Hsts)".
    3: { iApply (big_sepL2_mono with "Hadv").
         intros k v1 v2 Hv1 Hv2. cbn. iIntros. iFrame.
         pose proof (Forall_lookup_1 _ _ _ _ Hadv_val Hv2) as Hncap.
         destruct v2; [| by inversion Hncap].
         rewrite fixpoint_interp1_eq /=. iSplit; eauto.
         unfold future_priv_mono. iModIntro. iIntros.
         rewrite !fixpoint_interp1_eq //=. }
    done.
    { rewrite Forall_lookup. intros. cbn.
      eapply (@lookup_empty _ (gmap Addr)); typeclasses eauto. }
    iDestruct "Hadv" as "#Hadv".

    set W1 := (std_update_multiple W0 (region_addrs adv_start adv_end) Permanent).

    iMod (extend_region_static_single_sepM _ _ _ RWLX (λ Wv, interp Wv.1 Wv.2)
            with "Hsts Hr Hstack") as "(Hr & Hstack & Hsts)"; auto.
    { intros ? ?%Hstack_adv_disj. rewrite /W1.
      rewrite std_sta_update_multiple_lookup_same_i //. }
    iDestruct (big_sepM_to_big_sepL _ (region_addrs stack_start stack_end) with "Hstack")
      as "Hstack".
    { apply region_addrs_NoDup. }
    { intros a Ha. eapply in_dom_mkregion' in Ha; [| apply stack_size].
      apply elem_of_gmap_dom in Ha; auto. }
    iDestruct "Hstack" as "#Hstack".

    set W2 := (override_uninitializedW (mkregion stack_start stack_end stack_val) W1).

    (* Apply the spec, obtain that the PC is in the expression relation *)

    iAssert (((interp_expr interp reg) W2) (inr (RX, Global, awk_region_start, awk_region_end, awk_preamble_start)))
      with "[Hawk_preamble Hawk_body Hinv_malloc Hawk_link Hlink1 Hlink2]" as "HE".
    { assert (isCorrectPC_range RX Global awk_region_start awk_region_end
                                awk_preamble_start awk_body_start).
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize awk_linking_ptr_size awk_preamble_size awk_body_size. revert Ha1 Ha2. clear.
        unfold awkward_instrs_length, awkward_preamble_instrs_length. solve_addr. }
      set awk_preamble_move_addr := ^(awk_preamble_start + awkward_preamble_move_offset)%a.
      assert ((awk_preamble_start + awkward_preamble_move_offset)%a = Some awk_preamble_move_addr).
      { clear. subst awk_preamble_move_addr.
        generalize awk_preamble_size.
        unfold awkward_preamble_instrs_length, awkward_preamble_move_offset.
        generalize awk_preamble_start awk_body_start. solve_addr. }
      assert (awk_preamble_move_addr + offset_to_awkward = Some awk_body_start)%a.
      { generalize awk_preamble_size.
        unfold awk_preamble_move_addr, offset_to_awkward, awkward_preamble_instrs_length.
        unfold awkward_preamble_move_offset. clear.
        generalize awk_preamble_start awk_body_start. solve_addr. }
      assert (isCorrectPC_range RX Global awk_region_start awk_region_end
                                awk_body_start awk_region_end).
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize awk_linking_ptr_size awk_preamble_size awk_body_size. revert Ha1 Ha2; clear.
        unfold awkward_instrs_length, awkward_preamble_instrs_length. solve_addr. }

      iApply (Spec with "[$Hinv_malloc $Hawk_body $Hawk_preamble $Hawk_link $Hlink1 $Hlink2]");
        try eassumption.
      - done.
      - apply contiguous_between_region_addrs. generalize awk_preamble_size; clear.
        unfold awkward_preamble_instrs_length. solve_addr.
      - apply le_addr_withinBounds. clear; solve_addr.
        generalize link_table_size; clear; solve_addr.
      - subst link_entry_fail. apply le_addr_withinBounds.
        generalize link_table_start; clear; solve_addr.
        generalize link_table_start link_table_end link_table_size. clear; solve_addr.
      - clear; generalize link_table_start; solve_addr.
      - clear; subst link_entry_fail;
        generalize link_table_start link_table_end link_table_size; solve_addr.
      - apply contiguous_between_region_addrs. generalize awk_body_size; clear.
        unfold awkward_instrs_length. solve_addr. }

    clear Hm Spec. rewrite /interp_expr /=.

    (* prepare registers *)

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hstk & Hr0 & Hrothers).

    (* Specialize the expression relation, showing that registers are valid *)

    iSpecialize ("HE" with "[Hreg Hr Hsts Hna]").
    { iFrame. iSplit; cycle 1.
      { iFrame. rewrite /registers_mapsto. by rewrite insert_id. }
      { iSplit. iPureIntro; intros; by apply initial_registers_full_map.
        (* All capabilities in registers are valid! *)
        iIntros (r HrnPC).
        (* r0 (return pointer to the adversary) is valid. Prove it using the
           fundamental theorem. *)
        destruct (decide (r = r_t0)) as [ -> |].
        { rewrite /RegLocate Hr0 fixpoint_interp1_eq /=.
          iAssert
            ([∗ list] a ∈ region_addrs adv_start adv_end,
              ∃ p : Perm, ⌜PermFlows RWX p⌝
                        ∗ read_write_cond a p (fixpoint interp1) ∧ ⌜std W2 !! a = Some Permanent⌝)%I
            as "#Hrwcond".
          { iApply (big_sepL_mono with "Hadv"). iIntros (k v Hkv). cbn.
            iIntros "H". rewrite /read_write_cond /=. iExists RWX. iFrame. iSplit;auto. iPureIntro.
            rewrite override_uninitializedW_lookup_nin.
            { eapply std_sta_update_multiple_lookup_in_i, elem_of_list_lookup_2; eauto. }
            intro Hv. eapply Hstack_adv_disj. by rewrite elem_of_gmap_dom //.
            eapply elem_of_list_lookup_2; eauto. }
          auto. }

        (* Stack: trivially valid because fully uninitialized *)
        destruct (decide (r = r_stk)) as [ -> |].
        { rewrite /RegLocate Hstk fixpoint_interp1_eq /=.
          rewrite (region_addrs_empty stack_start (min _ _)) /=.
          2: clear; solve_addr. iSplitR; [auto|].
          rewrite (_: max stack_start stack_start = stack_start). 2: clear; solve_addr.
          iApply (big_sepL_mono with "Hstack").
          iIntros (? ? Hk) "H". iDestruct "H" as (?) "?".
          rewrite /read_write_cond /region_state_U_pwl. iExists _. iFrame.
          iSplitL; [done|]. iPureIntro. right.
          assert (is_Some (mkregion stack_start stack_end stack_val !! y)) as [? ?].
          { rewrite elem_of_gmap_dom //. apply in_dom_mkregion'. apply stack_size.
            eapply elem_of_list_lookup_2; eauto. }
          unfold W2. eexists. erewrite override_uninitializedW_lookup_some; eauto. }

        (* Other registers *)
        rewrite /RegLocate.
        destruct (Hrothers r) as [rw [Hrw Hncap] ]. set_solver.
        destruct rw; [| by inversion Hncap].
        by rewrite Hrw fixpoint_interp1_eq /=. } }

    (* We get a WP; conclude using the rest of the Iris adequacy theorem *)

    iDestruct "HE" as "[_ HWP]". unfold interp_conf.

    iModIntro.
    (* Same as the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs _ => ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL "HWP". { iApply (wp_wand with "HWP"). eauto. }
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. apply Hm'_flag.
  Qed.

End Adequacy.

Existing Instance subG_MonRefIGΣ.

Theorem awkward_example_adequacy `{MachineParameters} `{memory_layout}
        (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory m →
  is_initial_registers reg →
  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  m' !! fail_flag = Some (inl 0%Z).
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              @MonRefΣ (leibnizO _) CapR_rtc; na_invΣ;
              STS_preΣ Addr region_type; heapPreΣ;
              savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word)
      ]).
  eapply (@awkward_example_adequacy' Σ); typeclasses eauto.
Qed.

(* Print Assumptions awkward_example_adequacy. *)
(* -> Closed under the global context. *)
