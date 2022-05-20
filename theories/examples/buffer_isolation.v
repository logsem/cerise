From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine.examples Require Export mkregion_helpers
  disjoint_regions_tactics contiguous.
From cap_machine.examples Require Export template_adequacy_concurrency.
From iris.program_logic Require Import adequacy.
Open Scope Z_scope.

Section buffer.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Definition buffer_code (b_buf e_buf: Addr) : list Word :=
    (* code: *)
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 7 ;
      Load r_t1 r_t1 ;
      Store r_t1 42 ;
      Lea r_t1 (-3);
      Subseg r_t1 b_buf (b_buf+3)%Z;
      Jmp r_t0
    ].

  Definition data (b_buf e_buf: Addr) : list Word  :=
      [ WCap RWX b_buf e_buf (b_buf ^+ 3)%a ].

  Definition buffer_prog a_first b_buf e_buf :=
    ([∗ list] a_i;w ∈ a_first;(buffer_code b_buf e_buf) ++ (data b_buf e_buf), a_i ↦ₐ w)%I.

  Definition secret_buffer := map WInt [ 0 ].
  Definition public_buffer := map WInt [ 72 (* 'H' *); 105 (* 'i' *); 0].
  Definition full_buffer : list Word :=
    public_buffer++secret_buffer.


  (** We define the invariants *)
  Definition Nsb : namespace := nroot .@ "Nshared_buffer".

  Definition bufferN := Nsb.@"buffer".
  Definition buffer_inv {Hinv} (b_buf e_buf : Addr) : iProp Σ :=
      inv (invG0 := Hinv) (Nsb .@ (b_buf ^+ 3)%a)
                 ((b_buf ^+ 3)%a ↦ₐ (WInt 0) ∨ (b_buf ^+ 3)%a ↦ₐ (WInt 42))%I.

  Lemma buffer_spec (i: CoreN)
    p b e a a_first a_last
    (b_buf e_buf: Addr)
    wadv w1 φ :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length full_buffer))%a ->
    (b_buf ^+ 3)%a < e_buf ->

   ⊢ (( (i, PC) ↦ᵣ WCap p b e a_first
      ∗ (i, r_t0) ↦ᵣ wadv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ buffer_prog a b_buf e_buf
      ∗ buffer_inv b_buf e_buf
      ∗ ▷ ((i, PC) ↦ᵣ updatePcPerm wadv
           ∗ (i, r_t0) ↦ᵣ wadv
           ∗ (i, r_t1) ↦ᵣ WCap RWX b_buf (b_buf ^+ 3)%a b_buf%a
           ∗ buffer_prog a b_buf e_buf
           ∗ buffer_inv b_buf e_buf
           -∗ WP (i, Seq (Instr Executable)) {{ φ }}))
      -∗ WP (i, Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf HVe_buf)
      "(HPC & Hr0 & Hr1 & Hprog & #Hsecret_inv & Hφ)" .
    set (e_buf' := e_buf).
    rename e_buf into eb ; rename e_buf' into e_buf ; subst eb.
    rewrite {1}/buffer_prog.

    iDestruct (contiguous_between_program_split with "Hprog") as
      (buffer_codes datas a_data) "(Hprog & Hdata & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont_code & Hcont_buffer & Heqapp1 & Ha_data).
    rewrite /data.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_code.
    iDestruct (big_sepL2_length with "Hdata") as %Hlength_data.
    simpl in Hlength_data.
    inversion Hcont_buffer ; subst ; try discriminate.
    inversion H0 ; subst ; try discriminate.
    clear H0.
    iDestruct ((big_sepL2_singleton (λ _ a_i w_i, (a_i ↦ₐ w_i)%I)) with "Hdata")
      as "Hdata".

    iAssert (codefrag a_first (buffer_code b_buf e_buf)) with "[Hprog]" as "Hprog".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace buffer_codes with (finz.seq_between a_first (a_first ^+ 7%nat)%a).
      done.
      symmetry.
      apply region_addrs_of_contiguous_between.
      replace (a_first ^+ 7%nat)%a with a_data. done.
      apply contiguous_between_length in Hcont_code.
      rewrite Hlength_code in Hcont_code.
      solve_addr. }
    codefrag_facts "Hprog".
    iGo "Hprog".
    replace (a_first ^+ 7)%a with a_data ; last solve_addr.
    iInstr "Hprog" ; first solve_addr.

    rewrite /full_buffer /map /buffer_code.
    wp_instr.
    iInv "Hsecret_inv" as ">Hsecret" "Hcls".
    iDestruct "Hsecret" as "[Hsecret | Hsecret]".
    all: iInstr "Hprog" ; first (subst e_buf ; solve_addr).
    all: iMod ("Hcls" with "[Hsecret]") as "_"
    ; [ iNext ; iRight ; iAssumption| iModIntro ; wp_pure].
    all: iInstr "Hprog"
    ; [ transitivity (Some b_buf); auto ; solve_addr |].
    all: iInstr "Hprog"
    ; [ transitivity (Some (b_buf ^+ 3)%a); auto ; solve_addr
      | subst e_buf ; solve_addr |].
    all: iInstr "Hprog" ; iApply "Hφ"; iFrame "HPC Hr0 Hr1 # Hdata".
    all: rewrite /codefrag /region_mapsto /buffer_code.
    all: replace buffer_codes with (finz.seq_between a_first (a_first ^+ 7%nat)%a)
    ; [iFrame ; auto|].
    all: symmetry
    ; apply region_addrs_of_contiguous_between
    ; replace (a_first ^+ 7%nat)%a with a_data ; [done|].
    all: apply contiguous_between_length in Hcont_code
    ; rewrite Hlength_code in Hcont_code
    ; solve_addr.
  Qed.

  Lemma buffer_full_run_spec
    (i: CoreN)
    p b e a a_first a_last (* PC capabilities *)
    (b_buf e_buf: Addr) (* Shared buffer *)
    b_adv e_adv adv (* Adversary *)
    rmap :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length full_buffer))%a ->
    (b_buf + (length full_buffer))%a = Some (b_buf ^+ (length full_buffer))%a →

    Forall (λ w, is_cap w = false) adv →
    (b_adv + length adv)%a = Some e_adv →

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0) ]} →

    ⊢ (  (i, PC) ↦ᵣ WCap p b e a_first
         ∗ (i, r_t0) ↦ᵣ WCap RWX b_adv e_adv b_adv
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)

         ∗ buffer_prog a b_buf e_buf
         ∗ ([∗ map] a↦w ∈ mkregion b_adv e_adv adv, a ↦ₐ w)
         ∗ ([∗ map] a↦w ∈ mkregion b_buf (b_buf ^+3)%a public_buffer, a ↦ₐ w)
         ∗ buffer_inv b_buf e_buf

         -∗ WP (i, Seq (Instr Executable)) {{ λ _, True }})%I.

  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf HV_buf
               HVadv Hlength_adv Hrmap_dom)
      "(HPC & Hr0 & Hrmap & Hprog & Hadv & Hbuffer_pub & #Hsecret_inv)" .

    (* Continuation - executes completelety after the jump to the adversary *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". done.
    iDestruct (region_integers_alloc' _ _ _ b_adv _ RWX with "Hadv") as ">#Hadv". done.
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iDestruct ( mkregion_sepM_to_sepL2 with "Hbuffer_pub") as "Hbuffer_pub"
    ; first solve_addr.
    iDestruct (region_integers_alloc' _ _ _ b_buf _ RWX with "Hbuffer_pub") as
      ">#Hbuffer_public".
    rewrite /public_buffer ; cbn.
    repeat (apply Forall_cons_2 ; auto).
    (* Extract the register r1 *)
    assert (is_Some (rmap !! (i,r_t1)))
      as [w1 Hw1]
           by (rewrite elem_of_gmap_dom Hrmap_dom; set_solver+).
      iDestruct (big_sepM_delete _ _ (i, r_t1) with "Hrmap") as "[[Hr1 %HVw1] Hrmap]"
      ; first eauto.

    iApply (buffer_spec with "[-]"); eauto ; try solve_addr.
    iFrame "∗#".
    iNext. iIntros "(HPC & Hr0 & Hr1 & _)".

    (* Show that the contents of unused registers is safe *)
    set (rmap' := delete (i, r_t1) rmap).
    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    (* put the other registers back into the register map *)
    iDestruct (big_sepM_insert _ _ (i, r_t1) with "[$Hrmap Hr1]") as "Hrmap".
    { apply not_elem_of_dom ; set_solver+. }
    iFrame "∗#".
    subst rmap' ; rewrite insert_delete.
    iDestruct (big_sepM_insert _ _ (i, r_t0) with "[$Hrmap Hr0]") as "Hrmap".
    { rewrite lookup_insert_ne ; [| clear Hrmap_dom ; simplify_pair_eq].
    apply not_elem_of_dom . rewrite Hrmap_dom; set_solver+. }
    by iFrame.
    iApply (wp_wand with "[-]").
    { iApply "Hcont"; cycle 1. iFrame. iPureIntro. rewrite !dom_insert_L Hrmap_dom.
      clear Hrmap_dom.
      do 2 rewrite singleton_union_difference_L.
      set_solver+. }
    eauto.
  Qed.

  Lemma adversary_full_run_spec
    (i: CoreN)
    (Adv : adv_prog)
    (b_buf e_buf: Addr) (* Shared buffer *)
    rmap :

    let b_adv := (adv_start Adv) in
    let e_adv := (adv_end Adv) in
    let adv := (adv_instrs Adv) in
    let l_buf := (length full_buffer) in

    e_buf = (b_buf ^+ l_buf )%a ->
    (b_buf + l_buf)%a = Some (b_buf ^+ l_buf)%a →

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC)]} →

    ⊢ (  (i, PC) ↦ᵣ WCap RWX b_adv e_adv b_adv
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
         ∗ ([∗ map] a↦w ∈ adv_region Adv, a ↦ₐ w)
         ∗ buffer_inv b_buf e_buf

         -∗ WP (i, Seq (Instr Executable)) {{ λ _, True }})%I.
  Proof.
    intros b_adv e_adv adv l_buf.
    iIntros (He_buf HV_buf Hrmap_dom)
      "(HPC & Hrmap & Hadv & #Hsecret_inv)" .
    subst.
    (* Continuation - executes completelety after the jump to the adversary *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv".
    { pose proof (adv_size Adv); solve_addr. }
    iDestruct (region_integers_alloc' with "Hadv") as ">#Hadv"
    ; first apply (adv_valid Adv).
    iDestruct (jmp_to_unknown_adv with "Hadv") as "#Hcont"; first by right.

    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    iApply (wp_wand with "[-]").
    { iApply "Hcont"; cycle 1. iFrame. iPureIntro. assumption. }
    eauto.
  Qed.


End buffer.

Section adequacy.

  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG (CoreN * RegName) Word Σ}.
  Context `{MP: MachineParameters}.


  (** Shared buffer adequacy theorem *)


  Definition mem_inv (m : Mem) (b_buf : Addr ):=
    (m !! (b_buf^+3)%a = Some (WInt 0) \/ m !! (b_buf^+3)%a = Some (WInt 42) ).

  Ltac solve_addr' SB Hsbuf b_buf e_buf :=
    ( pose proof (Hsize := prog_size SB)
      ; rewrite Hsbuf in Hsize
      ; subst b_buf e_buf ; solve_addr).

  Lemma adequacy_shared_buffer
    (m m': Mem) (reg reg': Reg) (es : list cap_lang.expr)
    (P Adv1 B : prog) (* Programs, adversaries and buffer *)
    (Adv2 : adv_prog)
    (i j : CoreN) :

    let b_buf := (prog_start B) in
    let e_buf := (prog_end B) in

    (* Machine with 2 cores identified by {0, 1} *)
    machine_base.CoreNum = 2 ->
    i = core_zero ->
    j = (i^+1)%f ->

    (* The adversary contains only instructions *)
    Forall (λ w, is_cap w = false) (prog_instrs Adv1) →
    (* The program P contains the instructions of buffer_code *)
    prog_instrs P = (buffer_code b_buf e_buf ++ data b_buf e_buf) ->
    (* The initial content of the full buffer *)
    prog_instrs B = full_buffer ->

    (* Initial state *)
    is_initial_registers_with_adv P Adv1 r_t0 reg i ->
    is_initial_registers_adv Adv2 reg j ->
    is_initial_memory [P;Adv1;B] [Adv2] m ->

    (* The invariant holds on the initial memory *)
    mem_inv m b_buf ->

    (* Final goal - at all steps of execution, the invariant holds *)
    rtc (@erased_step cap_lang) (init_cores, (reg, m)) (es, (reg', m')) →
    mem_inv m' b_buf.

  Proof.
    intros b_buf e_buf.
    intros Hn_cores Hi Hj Hadv1 Hprog Hsbuf Hreg1 Hreg2 Hmem Hmem_inv Hstep.
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

    (* Split the memory into 5 parts: prog1, prog2, adv1, adv2, shared_buffer*)
    iDestruct (big_sepM_subseteq with "Hmem") as "Hmem".
    by apply Hmem.
    iDestruct (big_sepM_union with "Hmem") as "[Hprog Hmem]".
    { rewrite /is_initial_memory in Hmem.
      destruct Hmem as (_ & Hmem)
      ; rewrite /disjoint_list_map /= in Hmem
      ; destruct Hmem as (?&?&?&?&?).
      repeat (apply map_disjoint_union_l_2 ; auto)
      ; auto.
    }
    iDestruct (big_sepM_union with "Hmem") as "[Hadv1 Hmem]".
    { rewrite /is_initial_memory in Hmem.
      destruct Hmem as (_ & Hmem)
      ; rewrite /disjoint_list_map /= in Hmem
      ; destruct Hmem as (?&?&?&?&?).
      repeat (apply map_disjoint_union_l_2 ; auto)
      ; auto.
    }
    iDestruct (big_sepM_union with "Hmem") as "[Hbuffer Hmem]".
    { rewrite /is_initial_memory in Hmem.
      destruct Hmem as (_ & Hmem)
      ; rewrite /disjoint_list_map /= in Hmem
      ; destruct Hmem as (?&?&?&?&?).
      repeat (apply map_disjoint_union_l_2 ; auto)
      ; auto.
    }
    iDestruct (big_sepM_union with "Hmem") as "[Hadv2 _]"
    ; first apply map_disjoint_empty_r.



    (* Allocation of all the required invariants *)
    (* Split the shared_buffer into public and secret buffer *)
    rewrite {3}/prog_region Hsbuf /full_buffer.
    rewrite mkregion_app.
    2:{ solve_addr' B Hsbuf b_buf e_buf. }
    iDestruct (big_sepM_union with "Hbuffer") as "[Hpublic Hsecret]".
    {
    rewrite /mkregion ; cbn.
    do 3 (rewrite finz_seq_between_cons ; [| solve_addr' B Hsbuf b_buf e_buf ]).
    rewrite finz_seq_between_empty  ; [| solve_addr' B Hsbuf b_buf e_buf ].
    rewrite finz_seq_between_cons ; [| solve_addr' B Hsbuf b_buf e_buf ].
    rewrite finz_seq_between_empty  ; [| solve_addr' B Hsbuf b_buf e_buf ].
    cbn.
    apply map_disjoint_insert_r_2 ; [|apply map_disjoint_empty_r ].
    assert ( (prog_start B) ≠  (prog_start B ^+ 3%nat)%a )
      by solve_addr' B Hsbuf b_buf e_buf.
    assert ( (prog_start B ^+ 1%nat)%a ≠  (prog_start B ^+ 3%nat)%a )
      by solve_addr' B Hsbuf b_buf e_buf.
    assert ( ((prog_start B ^+ 1) ^+ 1)%a ≠  (prog_start B ^+ 3%nat)%a )
      by solve_addr' B Hsbuf b_buf e_buf.
    simplify_map_eq ; reflexivity.
    }
    iDestruct (mkregion_sepM_to_sepL2 with "Hsecret") as "Hsecret".
    solve_addr' B Hsbuf b_buf e_buf.
    (* Allocates the invariant about the secret buffer *)
    rewrite /secret_buffer ; simpl.
    replace (finz.seq_between (prog_start B ^+ 3%nat)%a (prog_end B))
      with ([(prog_start B ^+ 3%nat)%a]).
    2: { rewrite finz_seq_between_singleton
         ; [done| solve_addr' B Hsbuf b_buf e_buf]. }
    simpl. iDestruct "Hsecret" as "[Hsecret _]".
    iMod (inv_alloc (invG0 := Hinv)
            (Nsb.@(b_buf ^+ 3)%a)
            ⊤ ((b_buf ^+ 3)%a ↦ₐ WInt 0 ∨ (b_buf ^+ 3)%a ↦ₐ WInt 42)
           with "[Hsecret]") as "#Hinv_secret".
    { iNext ; iLeft ; iFrame. }

    iModIntro.
    iSplitL.
    (** For all cores, prove that it executes completely and safely *)
    {
      (* Since we have a machine with 2 cores, split the list into 2 WP *)
      unfold CoreN in i,j,Hi,Hj.
      rewrite /init_cores /all_cores.
      rewrite /core_zero in Hi.
      assert (Hn_cores': (BinIntDef.Z.to_nat machine_base.CoreNum) = 2%nat) by lia.
      rewrite Hn_cores' ; cbn.
      assert (Hcores: i ≠ j).
      { solve_finz. }
      rewrite <- Hi ; rewrite <- Hj ; clear Hi Hj.
      fold CoreN in i,j.

      (* We separate the registers into two sets of registers:
         - the registers for i
         - the registers for j
       *)
      rewrite /is_initial_registers in Hreg1, Hreg2.
      destruct Hreg1 as ((Hreg1_some & Hreg1_dom & Hreg1_valid) & Hreg1_adv & Hneq1).
      destruct Hreg2 as (Hreg2_some & Hreg2_dom & Hreg2_valid).
      set (rmap_i := @set_map _ _ _ _ _ _ _
                       (@gset_union (CoreN * RegName) _ _)
                       (fun r : RegName => (i,r)) all_registers_s).
      set (rmap_j := @set_map _ _ _ _ _ _ _
                       (@gset_union (CoreN * RegName) _ _)
                       (fun r : RegName => (j,r)) all_registers_s).
      set (Pi:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = i )).
      set (Pj:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = j )).
      set (NPi := (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) ≠ i )).
      set (NPj := (λ v : CoreN * RegName * Word, (¬ Pj v)%type)).

      replace reg with
        (filter Pi reg ∪
           filter NPi reg) by set_solver.
      assert (dom _ ( filter Pi reg ) = rmap_i).
      { set_solver. }
      set (regs_ni := filter NPi reg).
      replace regs_ni with
        (filter Pj regs_ni ∪
           filter NPj regs_ni)
      by (by rewrite map_union_filter).
      assert (dom _ ( filter Pj regs_ni ) = rmap_j).
      { subst rmap_j.
        subst regs_ni.
        erewrite <- dom_filter_L.
        reflexivity.
        intros.
        split; intros.
        { destruct i0.
          apply elem_of_map_1 in H0.
          destruct H0 as (? & ? & ?). inversion H0 ; subst.
          destruct (decide (x = PC)) as [->|Hx] ; subst.
          - eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst NPi ; cbn ; auto.
            cbn ; auto.
          - destruct (Hreg2_valid x) as (? & ? & _); eauto.
            { clear -Hx. set_solver. }
            eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst NPi ; cbn ; auto.
            cbn ; auto.
        }
        { destruct H0 as (w & Hfilter & core_i0).
          destruct i0.
          cbn in core_i0. subst c.
          apply elem_of_map_2.
          apply all_registers_s_correct.
        }
      }

      iDestruct (big_sepM_union with "Hreg") as "[Hreg_i Hreg]".
      {
        cbn.

        rewrite (map_filter_commute _ _ _ _ _ _ _ _ _ _ _ _ Pj _ NPi).
        rewrite (map_filter_commute _ _ _ _ _ _ _ _ _ _ _ _ NPj _ NPi).

        replace ( filter NPi (filter Pj reg) ∪ filter NPi (filter NPj reg) )
          with (filter NPi ((filter Pj reg) ∪ (filter NPj reg))).
        2: { eapply map_filter_union.
             apply gmap_finmap.
             apply map_disjoint_filter. }
        replace (filter Pj reg ∪ filter NPj reg)
          with reg by (by rewrite map_union_filter).
        apply map_disjoint_filter.
      }
      iDestruct (big_sepM_union with "Hreg") as "[Hreg_j Hreg]".
      { apply map_disjoint_filter. }
      iClear "Hreg".

      (* For each core, we prove the WP, using the specification previously
         defined *)
      iSplitL "Hprog Hadv1 Hreg_i Hpublic".
      - (* We extracts the needed registers for the full_run_spec *)
      iDestruct (big_sepM_delete _ _ (i, PC) with "Hreg_i") as "[HPC_i Hreg_i]".
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.
      iDestruct (big_sepM_delete _ _ (i, r_t0) with "Hreg_i") as "[Hadv_i Hreg_i]".
      rewrite lookup_delete_ne ; [|simplify_pair_eq] ; eauto.
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.

      (* Apply the specification *)
      iApply (buffer_full_run_spec _ _ _ _ _  _ (prog_end P) _ _ _ _ _
               with "[$HPC_i $Hadv_i Hreg_i Hprog Hadv1 Hpublic]") ; cycle -1.
      iDestruct (mkregion_sepM_to_sepL2 with "Hprog") as "Hprog".
      { apply (prog_size P). }

      rewrite /buffer_prog Hprog.
      iFrame "#∗".

      iAssert ([∗ map] r↦w ∈
                 (delete (i, r_t0) (delete (i, PC) (filter Pi reg)) )
                , r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
        with "[Hreg_i]" as "Hreg_i".
      { iApply (big_sepM_mono with "Hreg_i"). intros r w Hr. cbn.
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
      apply ExecPCPerm_RWX.
      { split ; [solve_addr |].
        split ; [|solve_addr ].
        pose proof (prog_size P) ; solve_addr. }
      { apply contiguous_between_region_addrs.
        pose proof (prog_size P) ; solve_addr. }
      { solve_addr' B Hsbuf b_buf e_buf. }
      { solve_addr' B Hsbuf b_buf e_buf. }
      assumption.
      apply (prog_size Adv1).
      { rewrite !dom_delete_L.
        set (X := set_map (λ r : RegName, (i, r)) all_registers_s).
        rewrite - !difference_difference_L.
        replace ( dom (gset (CoreN * RegName)) (filter Pi reg)) with X by set_solver.
        set_solver.
      }

      - (* We extracts the needed registers for the full_run_spec *)
        iSplitL ; [|done].
        iDestruct (big_sepM_delete _ _ (j, PC) with "Hreg_j") as "[HPC_j Hreg_j]".
        apply map_filter_lookup_Some_2.
        { subst regs_ni Pj Pi ; cbn.
          apply map_filter_lookup_Some_2 ; [eauto| cbn ; by apply not_eq_sym].
        }
        by subst Pj ; cbn.
        iApply (adversary_full_run_spec j _ b_buf e_buf (delete (j, PC) (filter Pj regs_ni))
                 with "[$HPC_j Hreg_j $Hadv2]").
        solve_addr' B Hsbuf b_buf e_buf.
        solve_addr' B Hsbuf b_buf e_buf.
        { rewrite !dom_delete_L.
          set (X := set_map (λ r : RegName, (j, r)) all_registers_s).
          replace ( dom (gset (CoreN * RegName)) (filter Pj regs_ni)) with X by set_solver.
          set_solver.
        }
        iFrame "#".

        iAssert ([∗ map] r↦w ∈
                   delete (j, PC) (filter Pj regs_ni)
                  , r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
          with "[Hreg_j]" as "Hreg_j".
        { iApply (big_sepM_mono with "Hreg_j"). intros r w Hr. cbn.
          apply lookup_delete_Some in Hr as [Hr_PC Hr].
          assert (Hr' := Hr).
          apply (map_filter_lookup_Some_1_2 Pj regs_ni r w) in Hr.
          do 2 (apply map_filter_lookup_Some_1_1 in Hr').
          subst Pj ; cbn in Hr.

          destruct r as [? r] ; inversion Hr ; subst.
          feed pose proof (Hreg2_valid r) as HH. clear -Hr_PC ; set_solver.
          destruct HH as [? (Hr_reg & Hcap)].
          clear -Hr_reg Hr' Hcap.
          iIntros ; iFrame ; iPureIntro.
          cbn in *.
          simplify_map_eq. auto.
        }
        iFrame.
    }

    (** The invariant holds on the resulting memory *)
    iIntros (es' t2) "%Hes %Hlength_es %Hstuck [Hreg' Hmem'] Hopt _".
    rewrite /mem_inv.
    iInv "Hinv_secret" as ">Hsecret" "_".
    iDestruct "Hsecret" as "[Hsecret | Hsecret ]"
    ; iDestruct (gen_heap_valid m' with "Hmem' Hsecret") as "#%secret"
    ; (iApply fupd_mask_intro_discard ; [set_solver|iPureIntro])
    ; [ left | right]
    ; assumption.

    Unshelve.
    apply gmap_fmap.
    apply gmap_omap.
    apply gmap_merge.
    solve_decision.
    apply gset_empty.
    apply gset_singleton.
    apply gset_union.
    apply gset_intersection.
    apply gset_difference.
    apply gset_dom_spec.
    apply gset_leibniz.
  Qed.

End adequacy.
