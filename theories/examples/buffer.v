From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Export template_adequacy_concurrency.
From iris.program_logic Require Import adequacy.
Open Scope Z_scope.

Section buffer.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Definition buffer_code (off: Z) : list Word :=
    (* code: *)
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 4 (* [data-code] *);
      Subseg r_t1 (off + 4)%Z (* [data] *) (off + 7)%Z (* [data+3] *);
      Jmp r_t0
    ].
  Definition buffer_data : list Word :=
    (* data: *)
    map WInt [72 (* 'H' *); 105 (* 'i' *); 0; 42 (* secret value *)]
    (* end: *).

  Lemma buffer_spec (i: CoreN) (a_first: Addr) wadv w1 φ :
    let len_region := length (buffer_code a_first) + length buffer_data in
    ContiguousRegion a_first len_region →

   ⊢ (( (i, PC) ↦ᵣ WCap RWX a_first (a_first ^+ len_region)%a a_first
      ∗ (i, r_t0) ↦ᵣ wadv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ codefrag a_first (buffer_code a_first)
      ∗ ▷ (let a_data := (a_first ^+ 4)%a in
             (i, PC) ↦ᵣ updatePcPerm wadv
           ∗ (i, r_t0) ↦ᵣ wadv
           ∗ (i, r_t1) ↦ᵣ WCap RWX a_data (a_data ^+ 3)%a a_data
           ∗ codefrag a_first (buffer_code a_first)
           -∗ WP (i, Seq (Instr Executable)) {{ φ }}))
      -∗ WP (i, Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    intros len_region.
    iIntros (Hcont) "(HPC & Hr0 & Hr1 & Hprog & Hφ)".
    iGo "Hprog".
    { transitivity (Some (a_first ^+ 4)%a); auto. solve_addr. }
    { transitivity (Some (a_first ^+ 7)%a); auto. solve_addr. }
    solve_addr.
    iInstr "Hprog". iApply "Hφ". iFrame.
    rewrite (_: (a_first ^+ 4) ^+ 3 = a_first ^+ 7)%a //. solve_addr.
  Qed.

  Lemma buffer_full_run_spec i (a_first: Addr) b_adv e_adv w1 rmap adv :
    let len_region := length (buffer_code a_first) + length buffer_data in
    ContiguousRegion a_first len_region →
    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0); (i, r_t1) ]} →
    Forall (λ w, is_cap w = false) adv →
    (b_adv + length adv)%a = Some e_adv →

   ⊢ (  (i, PC) ↦ᵣ WCap RWX a_first (a_first ^+ len_region)%a a_first
      ∗ (i, r_t0) ↦ᵣ WCap RWX b_adv e_adv b_adv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
      ∗ codefrag a_first (buffer_code a_first)
      ∗ ([∗ map] a↦w ∈ mkregion (a_first ^+ 4)%a (a_first ^+ 7)%a (take 3%nat buffer_data), a ↦ₐ w)
      ∗ ([∗ map] a↦w ∈ mkregion b_adv e_adv adv, a ↦ₐ w)
      -∗ WP (i, Seq (Instr Executable)) {{ λ _, True }})%I.
  Proof.
    iIntros (? ? Hrmap_dom ? ?) "(HPC & Hr0 & Hr1 & Hrmap & Hcode & Hdata & Hadv)".

    (* The capability to the adversary is safe and we can also jmp to it *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". done.
    iDestruct (region_integers_alloc' _ _ _ b_adv _ RWX with "Hadv") as ">#Hadv". done.
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iApply (buffer_spec i a_first with "[-]"). solve_addr. iFrame.
    iNext. iIntros "(HPC & Hr0 & Hr1 & _)".

    (* Show that the contents of r1 are safe *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hdata") as "Hdata". solve_addr.
    iDestruct (region_integers_alloc' _ _ _ (a_first ^+ 4)%a _ RWX with "Hdata") as ">#Hdata".
      by repeat constructor.

    (* Show that the contents of unused registers is safe *)
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    (* put the other registers back into the register map *)
    iDestruct (big_sepM_insert _ _ (i, r_t1) with "[$Hrmap Hr1]") as "Hrmap".
      apply not_elem_of_dom. rewrite Hrmap_dom. set_solver+.
    { iFrame. rewrite (_: (a_first ^+ _) ^+ _ = a_first ^+ 7)%a. solve_addr+. solve_addr. }
    iDestruct (big_sepM_insert _ _ (i, r_t0) with "[$Hrmap Hr0]") as "Hrmap".
      rewrite lookup_insert_ne ; [| clear Hrmap_dom ; simplify_pair_eq].
      apply not_elem_of_dom. rewrite Hrmap_dom. set_solver+.
      { by iFrame. }
    iApply (wp_wand with "[-]").
    { iApply "Hcont"; cycle 1. iFrame. iPureIntro. rewrite !dom_insert_L Hrmap_dom.
      clear Hrmap_dom.
      do 2 rewrite singleton_union_difference_L.
      set_solver+. }
    eauto.
Qed.

End buffer.

Section adequacy.

  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG (CoreN * RegName) Word Σ}.
  Context `{MP: MachineParameters}.


  (** Buffer adequacy theorem *)

  Definition mem_inv (m : Mem) (pstart : Addr ):=
    m !! (pstart ^+ 7)%a = Some (WInt 42).

  Ltac solve_addr' P :=
    pose proof (Hsize := prog_size P)
    ; try (
          match goal with
          | h: prog_instrs P = ?L |- _ =>
              rewrite h in Hsize
          end) ; solve_addr.

  (* TODO move somewhere else *)
  Tactic Notation "solve_length_seq" "by" tactic3(solve_a) :=
    cbn ; rewrite finz_seq_between_length
    ; repeat (rewrite finz_dist_S ; last solve_a)
    ; by rewrite finz_dist_0 ; last solve_a.

  Lemma adequacy_shared_buffer
    (m m': Mem) (reg reg': Reg) (es : list cap_lang.expr)
    (P Adv : prog) (* Programs, adversaries and buffer *)
    (i j : CoreN) :

    (* Machine with one single-core identified by {0} *)
    machine_base.CoreNum = 1 ->
    i = core_zero ->

    (* The adversary contains only instructions *)
    Forall (λ w, is_cap w = false) (prog_instrs Adv) →

    (* The program P contains the instructions of buffer_code *)
    prog_instrs P = buffer_code (prog_start P) ++ buffer_data →

    (* Initial state *)
    with_adv.is_initial_registers_with_adv P Adv r_t0 reg i ->
    with_adv.is_initial_memory [P;Adv] [] m ->

    (* The invariant holds on the initial memory *)
    mem_inv m (prog_start P) ->

    (* Final goal - at all steps of execution, the invariant holds *)
    rtc (@erased_step cap_lang) (init_cores, (reg, m)) (es, (reg', m')) →
    mem_inv m' (prog_start P).

  Proof.
    intros Hn_cores Hi Hadv Hprog Hreg1 Hmem Hmem_inv Hstep.
    apply erased_steps_nsteps in Hstep as (n & κs & Hstep).

    (* We apply the Iris adequacy theorem, and we unfold the definition,
       generate the resources and unfold the definition *)
    (* Mostly boilerplates *)
    apply (@wp_strong_adequacy Σ cap_lang _
             init_cores (reg,m) n κs es (reg', m')) ; last assumption.
    intros.

    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .
    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.

    iExists NotStuck.
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (map (fun _ => (fun _ => True)%I) all_cores).
    iExists (fun _ => True)%I. cbn.
    iFrame.

    (* Split the memory into 2 parts: prog and adv*)
    iDestruct (big_sepM_subseteq with "Hmem") as "Hmem".
    by apply Hmem.
    cbn.
    iDestruct (big_sepM_union with "Hmem") as "[Hprog Hmem]".
    { rewrite /with_adv.is_initial_memory in Hmem.
      destruct Hmem as (_ & Hmem)
      ; rewrite /disjoint_list_map /= in Hmem
      ; destruct Hmem as (?&_&_).
      auto.
    }
    iDestruct (big_sepM_union with "Hmem") as "[Hadv _]"
    ; first apply map_disjoint_empty_r.



    (* Allocation of all the required invariants *)
    (* Split the shared_buffer into public and secret buffer *)
    rewrite {1}/prog_region Hprog.
    iDestruct ( mkregion_sepM_to_sepL2 with "Hprog" ) as "Hprog".
    1: { solve_addr' P. }
    erewrite (finz_seq_between_split (prog_start P)
                (prog_start P ^+ (length (buffer_code (prog_start P))))%a
                (prog_end P))
    ; last solve_addr' P.
    iDestruct (big_sepL2_app' with "Hprog") as "[Hprog Hbuffer]".
    { solve_length_seq by (solve_addr' P). }
    
    cbn.
    replace ( [WInt 72; WInt 105; WInt 0; WInt 42] ) with
      ( [WInt 72; WInt 105; WInt 0] ++ [WInt 42]) by auto.
    erewrite (finz_seq_between_split (prog_start P ^+ 4%nat)%a
                ((prog_start P ^+ 4%nat) ^+ 3%nat)%a
                (prog_end P))
    ; last solve_addr' P.
    iDestruct (big_sepL2_app' with "Hbuffer") as "[Hpublic Hsecret]".
    { solve_length_seq by (solve_addr' P). }
    iDestruct (mkregion_sepL2_to_sepM with "Hpublic") as "Hpublic".
    { solve_addr' P. }
    
    (* Allocates the invariant about the secret buffer *)
    replace ((prog_start P ^+ 4%nat) ^+ 3%nat)%a with (prog_start P ^+ 7%nat)%a
    by solve_addr' P.
    replace ( finz.seq_between (prog_start P ^+ 7%nat)%a (prog_end P) )
              with [(prog_start P ^+ 7%nat)%a]
                   by (rewrite finz_seq_between_singleton ; [done|solve_addr' P]).
    iDestruct "Hsecret" as "[Hsecret _]".

    iMod (inv_alloc
            (nroot.@"A")
            ⊤ ((prog_start P ^+ 7)%a ↦ₐ WInt 42)%I
           with "[Hsecret]") as "#Hinv_secret".
    { iNext ; iFrame. }

    iModIntro.
    iSplitL.
    (** For all cores, prove that it executes completely and safely *)
    {
      (* Since we have a machine with 2 cores, split the list into 2 WP *)
      unfold CoreN in i,Hi.
      rewrite /init_cores /all_cores.
      rewrite /core_zero in Hi.
      assert (Hn_cores': (BinIntDef.Z.to_nat machine_base.CoreNum) = 1%nat) by lia.
      rewrite Hn_cores' ; cbn.
      rewrite <- Hi ; clear Hi.
      fold CoreN in i.

      (* We separate the registers into two sets of registers:
         - the registers for i
         - the registers for j
       *)
      destruct Hreg1 as ((Hreg1_some & Hreg1_valid) & Hreg1_adv & Hneq1).
      set (rmap_i := @set_map _ _ _ _ _ _ _
                       (@gset_union (CoreN * RegName) _ _)
                       (fun r : RegName => (i,r)) all_registers_s).
      set (Pi:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = i )).
      set (NPi := (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) ≠ i )).

      replace reg with
        (filter Pi reg ∪
           filter NPi reg) by set_solver.
      assert (dom _ ( filter Pi reg ) = rmap_i).
      { set_solver. }

      iDestruct (big_sepM_union with "Hreg") as "[Hreg_i _]"
      ; first apply map_disjoint_filter.

      (* For each core, we prove the WP, using the specification previously
         defined *)

      (* We extracts the needed registers for the full_run_spec *)
      iDestruct (big_sepM_delete _ _ (i, PC) with "Hreg_i") as "[HPC_i Hreg_i]".
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.

      iDestruct (big_sepM_delete _ _ (i, r_t0) with "Hreg_i") as
        "[Hadv_i Hreg_i]".
      rewrite lookup_delete_ne ; [|simplify_pair_eq] ; eauto.
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.

      destruct (Hreg1_valid r_t1) as [w1 [Hw1 _] ]
      ; [clear -i; set_solver |].
      iDestruct (big_sepM_delete _ _ (i, r_t1) with "Hreg_i") as "[Hr1_i Hreg_i]".
      rewrite lookup_delete_ne ; [|simplify_pair_eq] ; eauto.
      rewrite lookup_delete_ne ; [|simplify_pair_eq] ; eauto.
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.
      iSplitL ; [|done].
      iApply (buffer_full_run_spec i (prog_start P) _ _ _
                ( delete (i, r_t1) (delete (i, r_t0) (delete (i, PC) (filter Pi reg))))
               with "[HPC_i $Hadv_i $Hr1_i $Hadv Hreg_i $Hprog Hpublic]")
      ; cycle -1.
      replace (prog_start P ^+ (length (buffer_code (prog_start P)) + length buffer_data))%a
        with (prog_end P) by solve_addr' P.
      iFrame.

      iAssert ([∗ map] r↦w ∈
                 delete (i, r_t1) (delete (i, r_t0) (delete (i, PC) (filter Pi reg)))
                , r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
        with "[Hreg_i]" as "Hreg_i".
      { iApply (big_sepM_mono with "Hreg_i"). intros r w Hr. cbn.
        apply lookup_delete_Some in Hr as [Hr_r1 Hr].
        apply lookup_delete_Some in Hr as [Hr_r0 Hr].
        apply lookup_delete_Some in Hr as [Hr_PC Hr].
        assert (Hr' := Hr).
        apply (map_filter_lookup_Some_1_2
                 (λ v : CoreN * RegName * Word, Pi v) reg r w) in Hr.
        subst Pi ; cbn in Hr.
        destruct r as [? r] ; inversion Hr ; subst.
        feed pose proof (Hreg1_valid r) as HH. clear -Hr_PC ; set_solver.
        destruct HH as [? (Hr_reg & Hcap)].
        iIntros ; iFrame ; iPureIntro.
        clear -Hr_reg Hr' Hcap.
        cbn in *.
        apply map_filter_lookup_Some in Hr'.
        destruct Hr' as [? _].
        simplify_map_eq. auto.
      }
      iFrame.
      solve_addr' P.

      { rewrite !dom_delete_L.
        set (X := set_map (λ r : RegName, (i, r)) all_registers_s).
        rewrite - !difference_difference_L.
        replace ( dom (gset (CoreN * RegName)) (filter Pi reg)) with X by set_solver.
        set_solver.
      }
      assumption.
      solve_addr' Adv.
    }

    (** The invariant holds on the resulting memory *)
    iIntros (es' t2) "%Hes %Hlength_es %Hstuck [Hreg' Hmem'] Hopt _".
    rewrite /mem_inv.
    iInv "Hinv_secret" as ">Hsecret" "_".
    iDestruct (gen_heap_valid m' with "Hmem' Hsecret") as "#%secret".
    iApply fupd_mask_intro_discard ; [set_solver|iPureIntro].
    assumption.
  Qed.

End adequacy.


