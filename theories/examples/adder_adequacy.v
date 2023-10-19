From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.proofmode Require Import disjoint_regions_tactics mkregion_helpers.
From cap_machine.examples Require Import macros malloc adder.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout `{MachineParameters} := {
  (* Code of g and f *)
  g_start : Addr;
  f_start : Addr;
  f_end : Addr;

  (* Memory cell for x *)
  x : Addr;
  x' : Addr; (* x' = x+1 *)

  (* Memory for the activation record *)
  act_start : Addr;
  act_end : Addr;

  (* adversary code *)
  adv_start : Addr;
  adv_end : Addr;

  g_size :
    (g_start + adder_g_instrs_length)%a = Some f_start;
  f_size :
    (f_start + adder_f_instrs_length)%a = Some f_end;

  act_size :
    (act_start + 8)%a = Some act_end;

  x_size :
    (x + 1)%a = Some x';

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        finz.seq_between adv_start adv_end;
        finz.seq_between act_start act_end;
        [x];
        finz.seq_between f_start f_end;
        finz.seq_between g_start f_start
       ]
}.

Definition mk_initial_memory `{memory_layout} (adv_val act_val : list Word) : gmap Addr Word :=
    mkregion g_start f_start (adder_g_instrs f_start f_end)
  ∪ mkregion f_start f_end adder_f_instrs
  ∪ list_to_map [(x, WInt 0%Z)] (* x: initially set to 0 (could be any positive number) *)
  ∪ mkregion act_start act_end act_val (* the activation region can hold arbitrary words *)
  ∪ mkregion adv_start adv_end adv_val
    (* adversarial code: any code or data, but no capabilities
       (see condition below) *)
.

Definition is_initial_memory `{memory_layout} (m: gmap Addr Word) :=
  ∃ (adv_val act_val: list Word),
    m = mk_initial_memory adv_val act_val
  (* The adversarial region in memory must only contain instructions, no
     capabilities (it can thus only access the capability [g] passes it
     through the registers, including a capability to the adversarial region
     (so the adversarial code *CAN* access (RWX) its own memory)
  *)
  ∧ Forall (λ w, is_z w = true) adv_val
  ∧ length act_val = 8
  ∧ (adv_start + length adv_val)%a = Some adv_end.

Definition is_initial_registers `{memory_layout} (reg: gmap RegName Word) :=
  reg !! PC = Some (WCap RX g_start f_end g_start) ∧
  reg !! r_t0 = Some (WCap RWX adv_start adv_end adv_start) ∧
  reg !! r_t1 = Some (WCap RWX act_start act_end act_start) ∧
  reg !! r_t3 = Some (WCap RW x x' x) ∧
  (∀ (r: RegName), r ∉ ({[ PC; r_t0; r_t1; r_t3 ]} : gset RegName) →
     ∃ (w:Word), reg !! r = Some w ∧ is_z w = true).

Lemma initial_registers_full_map `{MachineParameters, memory_layout} reg :
  is_initial_registers reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hr0 & Hr1 & Hr3 & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_t0)) as [->|]. by eauto.
  destruct (decide (r = r_t1)) as [->|]. by eauto.
  destruct (decide (r = r_t3)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Definition invN : namespace := nroot .@ "adder" .@ "inv".

  Lemma adder_adequacy' {ML:memory_layout} (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
    is_initial_memory m →
    is_initial_registers reg →
    rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
    ∃ (n: Z), m' !! x = Some (WInt n) ∧ (n >= 0)%Z.
  Proof.
    intros Hm Hreg Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c:ExecConf) => ∃ n, c.2 !! x = Some (WInt n) ∧ (n >= 0)%Z) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, m) es (reg', m') (state_is_good (reg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    unfold is_initial_memory in Hm.
    destruct Hm as (adv_val & act_val & Hm & Hadv_val & act_len & adv_size).
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .
    iMod (seal_store_init) as (seal_storeg) "Hseal_store".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

    pose proof (
      @adder_full_spec Σ memg regg seal_storeg logrel_na_invs MP invN f_start f_end
    ) as Spec.

    (* Extract points-to for the various regions in memory *)

    pose proof regions_disjoint as Hdisjoint.
    rewrite {2}Hm.
    rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_adv & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]".
    { disjoint_map_to_list. set_solver +Hdisj_adv. }
    rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_act & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hact]".
    { disjoint_map_to_list. set_solver +Hdisj_act. }
    rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_x & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hx]".
    { disjoint_map_to_list. set_solver +Hdisj_x. }
    iDestruct (big_sepM_insert with "Hx") as "[Hx _]". by apply lookup_empty. cbn [fst snd].
    rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_f & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hg Hf]".
    { disjoint_map_to_list. set_solver +Hdisj_f. }
    rewrite disjoint_list_cons in Hdisjoint |- *. destruct Hdisjoint as (Hdisj_g & _).
    clear Hdisj_adv Hdisj_act Hdisj_x Hdisj_f Hdisj_g.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare with "[$Hf]") as ">Hf". by apply f_size.
    iDestruct (mkregion_prepare with "[$Hg]") as ">Hg". by apply g_size.
    iDestruct (mkregion_prepare with "[$Hact]") as ">Hact".
      rewrite act_len; by apply act_size.
    iDestruct (mkregion_prepare with "[$Hadv]") as ">Hadv". by apply adv_size.

    (* Allocate the invariant about x *)

    iMod (inv_alloc invN ⊤ (∃ n, x ↦ₐ WInt n ∗ ⌜(0 ≤ n)%Z⌝)%I with "[Hx]") as "#Hinv".
    { iNext. eauto. }

    (* Establish that the adversary region is valid *)
    iMod (region_integers_alloc _ adv_start adv_end adv_start _ RWX with "Hadv") as "#Hadv"; auto.

    (* Prepare the registers *)
    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hr0 & Hr1 & Hr3 & Hrothers).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; eauto.
    iDestruct (big_sepM_delete _ _ r_t0 with "Hreg") as "[Hr0 Hreg]".
    by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hreg") as "[Hr1 Hreg]".
    by rewrite !lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hreg") as "[Hr3 Hreg]".
    by rewrite !lookup_delete_ne //.
    destruct (Hrothers r_t2) as [r2v [Hr2v Hr2V] ]. set_solver+.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hreg") as "[Hr2 Hreg]".
    by rewrite !lookup_delete_ne //.

    match goal with |- context [([∗ map] _↦_ ∈ ?r, _)%I] => set rmap := r end.
    iAssert ([∗ map] r↦w ∈ rmap, (r ↦ᵣ w ∗ interp w))%I with "[Hreg]" as "Hreg".
    { iApply (big_sepM_mono with "Hreg"). intros r w Hr. cbn.
      iIntros "?". iFrame. rewrite fixpoint_interp1_eq.
      assert (HH: r ∈ dom rmap). by apply elem_of_dom; eauto.
      rewrite /rmap !dom_delete_L in HH.
      destruct (Hrothers r) as [w' [? Hncap] ]. { subst rmap. set_solver+ HH. }
      subst rmap. repeat (rewrite lookup_delete_ne in Hr; [|set_solver+ HH]).
      simplify_eq. destruct w'; [|by inversion Hncap..]. eauto. }

    assert (∀ r, is_Some (reg !! r)) as Hreg_full.
    { intros r.
      destruct (decide (r = PC)); subst; [by eauto|].
      destruct (decide (r = r_t0)); subst; [by eauto|].
      destruct (decide (r = r_t1)); subst; [by eauto|].
      destruct (decide (r = r_t3)); subst; [by eauto|].
      destruct (Hrothers r) as [? [? ?] ]; eauto. set_solver. }

    (* Use the resources to instantiate the spec and obtain a WP *)

    iPoseProof (Spec with "[$HPC $Hr0 $Hr1 $Hr2 $Hr3 $Hreg $Hna $Hf $Hg $Hact $Hinv $Hadv]")
      as "SpecWP".
    { apply contiguous_between_region_addrs. generalize g_size; clear; solve_addr. }
    { apply contiguous_between_region_addrs. generalize f_size; clear; solve_addr. }
    { apply x_size. }
    { apply act_size. }
    { generalize f_size; clear; solve_addr. }
    { subst rmap. rewrite !dom_delete_L regmap_full_dom. set_solver+.
      apply Hreg_full. }

    (* We get a WP; conclude using the rest of the Iris adequacy theorem *)

    iModIntro.
    (* Must match the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    iDestruct "Hx" as (n) "[Hx %]".
    iDestruct (gen_heap_valid with "Hmem' Hx") as %Hm'_x.
    iModIntro. iPureIntro. rewrite /state_is_good //.
    exists n. cbn. split; eauto. lia.
  Qed.

End Adequacy.

Theorem adder_adequacy `{MachineParameters} `{memory_layout}
        (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory m →
  is_initial_registers reg →
  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  ∃ (n: Z), m' !! x = Some (WInt n) ∧ (n >= 0)%Z.
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; sealStorePreΣ;
              na_invΣ]).
  eapply (@adder_adequacy' Σ); typeclasses eauto.
Qed.
