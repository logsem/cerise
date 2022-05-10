
From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine.examples Require Export mkregion_helpers
  disjoint_regions_tactics contiguous.
(* From cap_machine.examples Require Import template_adequacy. *)
Open Scope Z_scope.

Section shared_buffer.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Definition buffer_code1 (b_buf e_buf: Addr) : list Word :=
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

  Definition data1 (b_buf e_buf: Addr) : list Word  :=
      [ WCap RWX b_buf e_buf (b_buf ^+ 3)%a ].

  Definition buffer_prog1 a_first b_buf e_buf :=
    ([∗ list] a_i;w ∈ a_first;(buffer_code1 b_buf e_buf) ++ (data1 b_buf e_buf), a_i ↦ₐ w)%I.

  Definition buffer_code2 (b_buf e_buf: Addr) : list Word :=
    (* code: *)
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 7 ;
      Load r_t1 r_t1 ;
      Store r_t1 (-42) ;
      Lea r_t1 (-4);
      Subseg r_t1 b_buf (b_buf+3)%Z;
      Jmp r_t0
    ].

  Definition data2 (b_buf e_buf: Addr) : list Word  :=
      [ WCap RWX b_buf e_buf (b_buf ^+ 4)%a ].

  Definition buffer_prog2 a_first b_buf e_buf :=
    ([∗ list] a_i;w ∈ a_first;(buffer_code2 b_buf e_buf) ++ (data2 b_buf e_buf), a_i ↦ₐ w)%I.

  Definition secret_buffer := map WInt [ 0 ; 0].
  Definition public_buffer := map WInt [ 72 (* 'H' *); 105 (* 'i' *); 0].
  Definition shared_buffer : list Word :=
    public_buffer++secret_buffer.


  (** We define the invariants *)
  Definition Nsb : namespace := nroot .@ "Nshared_buffer".

  (* program 1 *)
  Definition prog1N := Nsb.@"prog1".
  Definition prog1_inv a b_buf e_buf :=
    inv prog1N (buffer_prog1 a b_buf e_buf).

  (* program 2 *)
  Definition prog2N := Nsb.@"prog2".
  Definition prog2_inv a b_buf e_buf :=
    inv prog2N (buffer_prog2 a b_buf e_buf).

  Definition bufferN := Nsb.@"buffer".
  Definition buffer_inv {Hinv} (b_buf e_buf : Addr) : iProp Σ :=
   ([∗ list] a ∈ (finz.seq_between b_buf (b_buf ^+3)%a ),
      (inv (invG0 := Hinv) (logN .@ a) (interp_ref_inv a (λne w, interp w))))%I
      ∗ inv (invG0 := Hinv) (Nsb .@ (b_buf ^+ 3)%a)
                 ((b_buf ^+ 3)%a ↦ₐ (WInt 0) ∨ (b_buf ^+ 3)%a ↦ₐ (WInt 42))%I
      ∗ inv (invG0 := Hinv) (Nsb .@ (b_buf ^+ 4)%a)
        ((b_buf ^+ 4)%a ↦ₐ (WInt 0) ∨ (b_buf ^+ 4)%a ↦ₐ (WInt (-42)))%I
  .

  Lemma buffer_spec1 (i: CoreN)
    p b e a a_first a_last
    (b_buf e_buf: Addr)
    wadv w1 φ :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length shared_buffer))%a ->
    (b_buf ^+ 3 < e_buf)%a →
    (b_buf ^+ 4 < e_buf)%a →

   ⊢ (( (i, PC) ↦ᵣ WCap p b e a_first
      ∗ (i, r_t0) ↦ᵣ wadv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ buffer_prog1 a b_buf e_buf
      ∗ buffer_inv b_buf e_buf
      ∗ ▷ ((i, PC) ↦ᵣ updatePcPerm wadv
           ∗ (i, r_t0) ↦ᵣ wadv
           ∗ (i, r_t1) ↦ᵣ WCap RWX b_buf (b_buf ^+ 3)%a b_buf%a
           ∗ buffer_prog1 a b_buf e_buf
           ∗ buffer_inv b_buf e_buf
           -∗ WP (i, Seq (Instr Executable)) {{ φ }}))
      -∗ WP (i, Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf Hsecret1 Hsecret2)
      "(HPC & Hr0 & Hr1 & Hprog & #(Hbuffer_pub & Hsecret1_inv & Hsecret2_inv) & Hφ)" .
    set (e_buf' := e_buf).
    rename e_buf into eb ; rename e_buf' into e_buf ; subst eb.
    rewrite {1}/buffer_prog1.

    iDestruct (contiguous_between_program_split with "Hprog") as
      (buffer_code data a_data) "(Hprog & Hdata & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont_code & Hcont_buffer & Heqapp1 & Ha_data).
    rewrite /data1.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_code.
    iDestruct (big_sepL2_length with "Hdata") as %Hlength_data.
    simpl in Hlength_data.
    inversion Hcont_buffer ; subst ; try discriminate.
    inversion H0 ; subst ; try discriminate.
    clear H0.
    iDestruct ((big_sepL2_singleton (λ _ a_i w_i, (a_i ↦ₐ w_i)%I)) with "Hdata")
      as "Hdata".

    iAssert (codefrag a_first (buffer_code1 b_buf e_buf)) with "[Hprog]" as "Hprog".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace buffer_code with (finz.seq_between a_first (a_first ^+ 7%nat)%a).
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

    rewrite /shared_buffer. rewrite /map.
    rewrite /buffer_code1.
    wp_instr.
    iInv "Hsecret1_inv" as ">Hsecret1" "Hcls".
    iDestruct "Hsecret1" as "[Hsecret1 | Hsecret1]".
    all: iInstr "Hprog" ; first (subst e_buf ; solve_addr).
    all: iMod ("Hcls" with "[Hsecret1]") as "_"
    ; [ iNext ; iRight ; iAssumption| iModIntro ; wp_pure].
    all: iInstr "Hprog"
    ; [ transitivity (Some b_buf); auto ; solve_addr |].
    all: iInstr "Hprog"
    ; [ transitivity (Some (b_buf ^+ 3)%a); auto ; solve_addr
      | subst e_buf ; solve_addr |].
    all: iInstr "Hprog" ; iApply "Hφ" ; iFrame.
    all: iSplitL "Hprog" ; [| iFrame "#"].
    all: rewrite /codefrag /region_mapsto /buffer_code1.
    all: replace buffer_code with (finz.seq_between a_first (a_first ^+ 7%nat)%a)
    ; [iFrame ; auto|].
    all: symmetry
    ; apply region_addrs_of_contiguous_between
    ; replace (a_first ^+ 7%nat)%a with a_data ; [done|].
    all: apply contiguous_between_length in Hcont_code
    ; rewrite Hlength_code in Hcont_code
    ; solve_addr.
  Qed.


  Lemma buffer_spec2 (i: CoreN)
    p b e a a_first a_last
    (b_buf e_buf: Addr)
    wadv w1 φ :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length shared_buffer))%a ->
    (b_buf ^+ 3 < e_buf)%a →
    (b_buf ^+ 4 < e_buf)%a →

   ⊢ (( (i, PC) ↦ᵣ WCap p b e a_first
      ∗ (i, r_t0) ↦ᵣ wadv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ buffer_prog2 a b_buf e_buf
      ∗ buffer_inv b_buf e_buf
      ∗ ▷ ((i, PC) ↦ᵣ updatePcPerm wadv
           ∗ (i, r_t0) ↦ᵣ wadv
           ∗ (i, r_t1) ↦ᵣ WCap RWX b_buf (b_buf ^+ 3)%a b_buf%a
           ∗ buffer_prog2 a b_buf e_buf
           ∗ buffer_inv b_buf e_buf
           -∗ WP (i, Seq (Instr Executable)) {{ φ }}))
      -∗ WP (i, Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf Hsecret1 Hsecret2)
      "(HPC & Hr0 & Hr1 & Hprog & #(Hbuffer_pub & Hsecret1_inv & Hsecret2_inv) & Hφ)" .
    set (e_buf' := e_buf).
    rename e_buf into eb ; rename e_buf' into e_buf ; subst eb.
    rewrite {1}/buffer_prog2.

    iDestruct (contiguous_between_program_split with "Hprog") as
      (buffer_code data a_data) "(Hprog & Hdata & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont_code & Hcont_buffer & Heqapp1 & Ha_data).
    rewrite /data2.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_code.
    iDestruct (big_sepL2_length with "Hdata") as %Hlength_data.
    simpl in Hlength_data.
    inversion Hcont_buffer ; subst ; try discriminate.
    inversion H0 ; subst ; try discriminate.
    clear H0.
    iDestruct ((big_sepL2_singleton (λ _ a_i w_i, (a_i ↦ₐ w_i)%I)) with "Hdata")
      as "Hdata".

    iAssert (codefrag a_first (buffer_code2 b_buf e_buf)) with "[Hprog]" as "Hprog".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace buffer_code with (finz.seq_between a_first (a_first ^+ 7%nat)%a).
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

    rewrite /shared_buffer. rewrite /map.
    rewrite /buffer_code2.
    wp_instr.
    iInv "Hsecret2_inv" as ">Hsecret2" "Hcls".
    iDestruct "Hsecret2" as "[Hsecret2 | Hsecret2]".
    all: iInstr "Hprog" ; first (subst e_buf ; solve_addr).
    all: iMod ("Hcls" with "[Hsecret2]") as "_"
    ; [ iNext ; iRight ; iAssumption| iModIntro ; wp_pure].
    all: iInstr "Hprog"
    ; [ transitivity (Some b_buf); auto ; solve_addr |].
    all: iInstr "Hprog"
    ; [ transitivity (Some (b_buf ^+ 3)%a); auto ; solve_addr
      | subst e_buf ; solve_addr |].
    all: iInstr "Hprog" ; iApply "Hφ" ; iFrame.
    all: iSplitL "Hprog" ; [| iFrame "#"].
    all: rewrite /codefrag /region_mapsto /buffer_code1.
    all: replace buffer_code with (finz.seq_between a_first (a_first ^+ 7%nat)%a)
    ; [iFrame ; auto|].
    all: symmetry
    ; apply region_addrs_of_contiguous_between
    ; replace (a_first ^+ 7%nat)%a with a_data ; [done|].
    all: apply contiguous_between_length in Hcont_code
    ; rewrite Hlength_code in Hcont_code
    ; solve_addr.
  Qed.


  Lemma buffer_full_run_spec1
    (i: CoreN)
    p b e a a_first a_last (* PC capabilities *)
    (b_buf e_buf: Addr) (* Shared buffer *)
    wadv (* Adversary *)
    rmap w1 :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length shared_buffer))%a ->
    (b_buf ^+ 3 < e_buf)%a →
    (b_buf ^+ 4 < e_buf)%a →

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0); (i, r_t1) ]} →

   ⊢ (  (i, PC) ↦ᵣ WCap p b e a_first
      ∗ (i, r_t0) ↦ᵣ wadv
      ∗ (i, r_t1) ↦ᵣ w1
      ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)

      ∗ buffer_prog1 a b_buf e_buf
      ∗ buffer_inv b_buf e_buf

      ∗ interp wadv

      -∗ WP (i, Seq (Instr Executable)) {{ λ _, True }})%I.

  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf Hsecret1 Hsecret2 Hrmap_dom)
      "(HPC & Hr0 & Hr1 & Hrmap & Hprog & #(Hbuffer_pub & Hsecret1_inv & Hsecret2_inv) & #Hadv)" .

    (* Continuation - executes completelety after the jump to the adversary *)
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iApply (buffer_spec1 with "[-]"); eauto. iFrame "∗#".
    iNext. iIntros "(HPC & Hr0 & Hr1 & _)".

    (* Show that the contents of r1 is safe *)
    iAssert ( interp (WCap RWX b_buf (b_buf ^+ 3 )%a b_buf)) as "HvR1".
    { rewrite (fixpoint_interp1_eq (WCap _ _ _ _)).
      cbn.
      iApply (big_sepL_mono with "Hbuffer_pub").
      cbn.
      intros.
      iIntros "#Hinv".
      iExists _.
      iFrame "#".
      iSplit; do 2 iModIntro ; iIntros (?) "?" ; iAssumption.
    }

    (* Show that the contents of unused registers is safe *)
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    (* put the other registers back into the register map *)
    iDestruct (big_sepM_insert _ _ (i, r_t1) with "[$Hrmap Hr1]") as "Hrmap".
      apply not_elem_of_dom. rewrite Hrmap_dom. set_solver+.
    { iFrame "∗#". }
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
  
  Lemma buffer_full_run_spec2
    (i: CoreN)
    p b e a a_first a_last (* PC capabilities *)
    (b_buf e_buf: Addr) (* Shared buffer *)
    wadv (* Adversary *)
    rmap w1 :

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    e_buf = (b_buf ^+ (length shared_buffer))%a ->
    (b_buf ^+ 3 < e_buf)%a →
    (b_buf ^+ 4 < e_buf)%a →

    dom (gset (CoreN*RegName)) rmap =
      (set_map (fun r => (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0); (i, r_t1) ]} →

    ⊢ (  (i, PC) ↦ᵣ WCap p b e a_first
         ∗ (i, r_t0) ↦ᵣ wadv
         ∗ (i, r_t1) ↦ᵣ w1
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)

         ∗ buffer_prog2 a b_buf e_buf
         ∗ buffer_inv b_buf e_buf

         ∗ interp wadv

         -∗ WP (i, Seq (Instr Executable)) {{ λ _, True }})%I.

  Proof.
    iIntros (HPCperm HPCbounds Hcont He_buf Hsecret1 Hsecret2 Hrmap_dom)
      "(HPC & Hr0 & Hr1 & Hrmap & Hprog & #(Hbuffer_pub & Hsecret1_inv & Hsecret2_inv) & #Hadv)" .

    (* Continuation - executes completelety after the jump to the adversary *)
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iApply (buffer_spec2 with "[-]"); eauto. iFrame "∗#".
    iNext. iIntros "(HPC & Hr0 & Hr1 & _)".

    (* Show that the contents of r1 is safe *)
    iAssert ( interp (WCap RWX b_buf (b_buf ^+ 3 )%a b_buf)) as "HvR1".
    { rewrite (fixpoint_interp1_eq (WCap _ _ _ _)).
      cbn.
      iApply (big_sepL_mono with "Hbuffer_pub").
      cbn.
      intros.
      iIntros "#Hinv".
      iExists _.
      iFrame "#".
      iSplit; do 2 iModIntro ; iIntros (?) "?" ; iAssumption.
    }

    (* Show that the contents of unused registers is safe *)
    iAssert ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    (* put the other registers back into the register map *)
    iDestruct (big_sepM_insert _ _ (i, r_t1) with "[$Hrmap Hr1]") as "Hrmap".
    apply not_elem_of_dom. rewrite Hrmap_dom. set_solver+.
    { iFrame "∗#". }
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





  Definition mem_inv (m : Mem) (b_buf : Addr ):=
    (m !! (b_buf^+3)%a = Some (WInt 0) \/ m !! (b_buf^+3)%a = Some (WInt 42) )
    /\ (m !! (b_buf^+4)%a = Some (WInt 0) \/ m !! (b_buf^+4)%a = Some (WInt (-42))
      ).


  Program Definition all_cores :=
    finz.seq
      (@finz.FinZ machine_base.CoreNum 0 _ _)
      (BinIntDef.Z.to_nat machine_base.CoreNum).
  Next Obligation.
    pose machine_base.CorePos. lia.
  Qed.
  Next Obligation. lia. Qed.

  Compute all_cores.
  Definition init_cores : list expr :=
    map (fun (i : CoreN) => (i, Seq (Instr Executable))) all_cores.

From iris.program_logic Require Import adequacy.

End shared_buffer.

Section adequacy.

  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG (CoreN * RegName) Word Σ}.
  Context `{MP: MachineParameters}.


  Instance filter_reg : Filter (CoreN * RegName) Reg.
  Proof.
    eapply map_filter ; eauto.
  Admitted.

  Record prog :=
    MkProg {
        prog_start: Addr;
        prog_end: Addr;
        prog_instrs: list Word;

        prog_size:
        (prog_start + length prog_instrs)%a = Some prog_end;
      }.



  (* All the registers of the core i points-to a valid word *)
  Definition is_initial_registers
    (* (b e a : Addr) (* PC Capability *) *)
    (P A : prog)
    (r_adv : RegName)
    (* (b_adv e_adv a_adv : Addr) (* Adversary capability *) *)
    (reg: gmap (CoreN * RegName) Word) (i:CoreN) :=
    reg !! (i, PC) = Some (WCap RWX (prog_start P) (prog_end P) (prog_start P))  (* PC *)
    /\ reg !! (i, r_adv) = Some (WCap RWX (prog_start A) (prog_end A) (prog_start A)) (* adversary *)
    /\ PC ≠ r_adv
    ∧ dom (gset (CoreN*RegName)) reg ⊆ (set_map (fun r => (i,r)) all_registers_s)
    /\ (∀ (r: RegName), (i, r) ∉ ({[ (i, PC) ]} : gset (CoreN * RegName)) →
                       ∃ (w:Word), reg !! (i, r) = Some w ∧ is_cap w = false).

  Definition prog_region (P: prog): gmap Addr Word :=
    mkregion (prog_start P) (prog_end P) (prog_instrs P).

  (* Definition is_initial_memory *)
  (*   (P1 P2 : prog) *)
  (*   (A1 A2 : prog) *)
  (*   b_buf e_buf buf *)
  (*   (m: gmap Addr Word) := *)
  (*   let p1 := prog_region P1 in *)
  (*   let p2 := prog_region P1 in *)
  (*   let a1 := prog_region A1 in *)
  (*   let a2 := prog_region A2 in *)
  (*   let B := (mkregion b_buf e_buf buf) in *)
  (*   ( p1 ∪ p2 ∪ B) ⊆ m *)
  (*   /\ (prog_region A1) ⊆ m *)
  (*   /\ (prog_region A2) ⊆ m *)
  (*   /\ ( p1 ##ₘ p2 ) *)
  (*   /\ ( p1 ##ₘ B ) *)
  (*   /\ ( p2 ##ₘ B ) *)
  (*   /\ ( p2 ##ₘ B ) *)
  (*   /\ ( a1 ##ₘ p1 ) *)
  (*   /\ ( a1 ##ₘ p2 ) *)
  (*   /\ ( a1 ##ₘ B ) *)
  (*   /\ ( a1 ##ₘ a2 ) *)
  (*   /\ ( a2 ##ₘ p1 ) *)
  (*   /\ ( a2 ##ₘ p2 ) *)
  (*   /\ ( a2 ##ₘ B ) *)
  (* . *)



  Definition is_initial_memory
    (P1 P2 : prog)
    b_buf e_buf buf
    (m: gmap Addr Word) :=
    let p1 := prog_region P1 in
    let p2 := prog_region P1 in
    let B := (mkregion b_buf e_buf buf) in
    ( p1 ∪ p2 ∪ B) ⊆ m
    /\ ( p1 ##ₘ p2 )
    /\ ( p1 ##ₘ B )
    /\ ( p2 ##ₘ B ).


  Lemma adequacy_shared_buffer
    (m m': Mem) (reg reg': Reg) (es : list cap_lang.expr)

    (P1 Adv1 P2 Adv2 : prog)

    b_buf e_buf (* shared buffer *)

    i j :
    i ≠ j ->
    
    (* Shared buffer addresses *)
    e_buf = (b_buf ^+ (length shared_buffer))%a ->
    (b_buf + 5)%a = Some (b_buf ^+ 5)%a →

    Forall (λ w, is_cap w = false) (prog_instrs Adv1) →
    Forall (λ w, is_cap w = false) (prog_instrs Adv2) →

    prog_instrs P1 = (buffer_code1 b_buf e_buf ++ data1 b_buf e_buf) ->
    prog_instrs P2 = (buffer_code2 b_buf e_buf ++ data2 b_buf e_buf) ->
    (* Initial state *)
    is_initial_registers P1 Adv1 r_t0 reg i ->
    is_initial_registers P2 Adv2 r_t0 reg j ->
    is_initial_memory P1 P2 b_buf e_buf shared_buffer m ->

    (* The invariant holds on the initial memory *)
    mem_inv m b_buf ->

    (* Final goal *)
    (* At all step of the execution *)
    rtc (@erased_step cap_lang) (init_cores, (reg, m)) (es, (reg', m')) →
    (* the invariant holds on the memory *)
    mem_inv m' b_buf.

  Proof.
    intros Hcores Hebuf HVbuffer Hadv1 Hadv2 Hprog1 Hprog2 Hreg1 Hreg2 Hmem Hmem_inv Hstep
    ; cbn in Hebuf.
    apply erased_steps_nsteps in Hstep as (n & κs & Hstep).

    apply (@wp_strong_adequacy Σ cap_lang _
             init_cores (reg,m) n κs es (reg', m')) ; last assumption.
    intros.
    (* iModIntro. *)

    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)" .

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.

    iExists NotStuck.
    iExists (fun σ κs _ => ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2)))%I.
    iExists (map (fun _ => (fun _ => True)%I) all_cores).
    iExists (fun _ => True)%I. cbn.

    iFrame.

    iDestruct (big_sepM_subseteq with "Hmem") as "Hmem". by eapply Hmem.
    iDestruct (big_sepM_union with "Hmem") as "[Hprogs Hbuffer]".
    { rewrite /is_initial_memory in Hmem.
      destruct Hmem as (_ & Hmem1 & Hmem2 & Hmem3).
      apply map_disjoint_union_l_2; set_solver. }
    iDestruct (big_sepM_union with "Hprogs") as "[Hprog1 Hprog2]".
    { rewrite /is_initial_memory in Hmem; set_solver. }

    (* Allocation invariant *)
    rewrite /buffer_inv.
    iDestruct (mkregion_sepM_to_sepL2 with "Hbuffer") as "Hbuffer".
    { cbn. subst e_buf. solve_addr. }
    rewrite /shared_buffer.
    rewrite ( finz_seq_between_split b_buf (b_buf ^+3)%a e_buf ).
    2: { solve_addr. }
    iDestruct (big_sepL2_app' _ _ _ _
                 (finz.seq_between b_buf (b_buf ^+ 3)%a)
                 (finz.seq_between (b_buf ^+ 3)%a e_buf)
                 public_buffer secret_buffer
                with "Hbuffer") as "[Hpublic Hsecret]".
    { cbn. rewrite finz_seq_between_length. apply finz_incr_iff_dist.
      solve_addr. }

    rewrite /secret_buffer ; simpl.
    rewrite (finz_seq_between_cons (b_buf ^+ 3)%a).
    2: { solve_addr. }
    replace ( ((b_buf ^+ 3) ^+ 1)%a ) with ( (b_buf ^+ 4)%a ) by solve_addr.
    replace (finz.seq_between (b_buf ^+ 4)%a e_buf)
      with ([(b_buf ^+ 4)%a]).
    2: { subst e_buf. rewrite finz_seq_between_singleton ; [done| solve_addr]. }
    simpl.
    iDestruct "Hsecret" as "(Hsecret1 & Hsecret2& _)".
    iMod (inv_alloc (invG0 := Hinv)
            (Nsb.@(b_buf ^+ 3)%a)
            ⊤ ((b_buf ^+ 3)%a ↦ₐ WInt 0 ∨ (b_buf ^+ 3)%a ↦ₐ WInt 42)
           with "[Hsecret1]") as "#Hinv_secret1".
    { iNext ; iLeft ; iFrame. }
    iMod (inv_alloc (Nsb.@(b_buf ^+ 4)%a)
            ⊤ ((b_buf ^+ 4)%a ↦ₐ WInt 0 ∨ (b_buf ^+ 4)%a ↦ₐ WInt (-42))
           with "[Hsecret2]") as "#Hinv_secret2".
    { iNext ; iLeft ; iFrame. }

    rewrite /public_buffer /=.
    do 3 (rewrite finz_seq_between_cons; last solve_addr).
    rewrite finz_seq_between_empty; last solve_addr.
    replace ( ((b_buf ^+ 1) ^+ 1)%a ) with (b_buf ^+ 2)%a by solve_addr.
    iDestruct "Hpublic" as "(Hp1 & Hp2 & Hp3 & _)".


    iMod (inv_alloc (invG0 := Hinv)
            (logN.@b_buf)
            ⊤ (∃ (w : leibnizO Word), b_buf ↦ₐ w ∗ interp w)
           with "[Hp1]") as "#Hinv_p1".
    { iNext ; iExists _ ; iFrame ; iApply interp_int. }

    iMod (inv_alloc (invG0 := Hinv)
            (logN.@(b_buf ^+1)%a)
            ⊤ (∃ (w : leibnizO Word), (b_buf ^+1)%a ↦ₐ w ∗ interp w)
           with "[Hp2]") as "#Hinv_p2".
    { iNext ; iExists _ ; iFrame ; iApply interp_int. }

    iMod (inv_alloc (invG0 := Hinv)
            (logN.@(b_buf ^+2)%a)
            ⊤ (∃ (w : leibnizO Word), (b_buf ^+2)%a ↦ₐ w ∗ interp w)
           with "[Hp3]") as "#Hinv_p3".
    { iNext ; iExists _ ; iFrame ; iApply interp_int. }

    iAssert (
        ([∗ list] a ∈ (finz.seq_between b_buf (b_buf ^+3)%a ),
          (inv (invG0 := Hinv) (logN .@ a) (@interp_ref_inv Σ (MemG Σ mem_invG  mem_heapg) a (λne w, interp w))))%I
      ) as "Hinv_public".
    {
    do 3 (rewrite finz_seq_between_cons; last solve_addr).
    rewrite finz_seq_between_empty; last solve_addr.
    replace ( ((b_buf ^+ 1) ^+ 1)%a ) with (b_buf ^+ 2)%a by solve_addr.
    rewrite /interp_ref_inv ; cbn.
    iFrame "#".
    }
    iClear "Hinv_p1 Hinv_p2 Hinv_p3".

    iModIntro.
    iSplitL.
    {
      (* TODO we assume some properties on the machine
         -> this is temporary. We want these admits to be parameter of the theorem.
       *)
      rewrite /init_cores /all_cores.
      replace (BinIntDef.Z.to_nat machine_base.CoreNum) with 2 by admit.
      cbn.
      replace (finz.FinZ 0 all_cores_obligation_1 all_cores_obligation_2) with
        i by admit.
      replace (i^+1)%f with j by admit.

      (* We separate the registers into two sets of registers:
         - the registers for i
         - the registers for j
       *)
      rewrite /is_initial_registers in Hreg1, Hreg2.
      destruct Hreg1 as (Hreg1_some & Hreg1_adv & Hneq1 & Hreg1_dom & Hreg1_valid).
      destruct Hreg2 as (Hreg2_some & Hreg2_adv & Hneq2 & Hreg2_dom & Hreg2_valid).
      set (rmap_i := @set_map _ _ _ _ _ _ _
                       (@gset_union (CoreN * RegName) _ _)
                       (fun r : RegName => (i,r)) all_registers_s).
      set (rmap_j := @set_map _ _ _ _ _ _ _
                       (@gset_union (CoreN * RegName) _ _)
                       (fun r : RegName => (j,r)) all_registers_s).
      set (Pi:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = i )).
      set (Pj:= (fun (v : (CoreN * RegName) * Word) => (fst (fst v)) = j )).
      replace reg with
        (filter Pi reg ∪
           filter (fun v => ~ Pi v) reg) by set_solver.
      assert (dom _ ( filter Pi reg ) = rmap_i).
      { set_solver. }
      set (regs_ni := filter (fun v => ~ Pi v) reg).
      replace regs_ni with
        (filter Pj regs_ni ∪
           filter (fun v => ~ Pj v) regs_ni)
      by (by rewrite map_union_filter).
      assert (dom _ ( filter Pj regs_ni ) = rmap_j).
      { subst rmap_j.
        subst regs_ni.
        erewrite <- dom_filter_L. reflexivity.
        intros.
        split; intros.
        { destruct i0.
          apply elem_of_map_1 in H0.
          destruct H0 as (? & ? & ?). inversion H0 ; subst.
          destruct (decide (x = PC)) as [->|Hx] ; subst.
          - eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst Pi ; cbn ; auto.
            cbn ; auto.
          - destruct (Hreg2_valid x) as (? & ? & _); eauto.
            { clear -Hx. set_solver. }
            eexists ; split.
            apply map_filter_lookup_Some_2.
            eassumption.
            subst Pi ; cbn ; auto.
            cbn ; auto.
        }
        { destruct H0 as (w & Hfilter & core_i0).
          destruct i0.
          cbn in core_i0. subst c.
          apply elem_of_map_2.
          apply all_registers_s_correct.
        }
      }
      set (regs_i := filter (fun v => Pi v) reg).
      set (regs_j := filter Pj regs_ni).
      set (regs := filter (λ v : CoreN * RegName * Word, (¬ Pj v)%type) regs_ni).
      iDestruct (big_sepM_union with "Hreg") as "[Hreg_i Hreg]".
      { subst regs_i regs_j regs regs_ni.
        subst Pi Pj.
        cbn.

        replace
          (filter (λ v : CoreN * RegName * Word, v.1.1 = j)
             (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ i) reg))
          with
          (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ i)
             (filter (λ v : CoreN * RegName * Word, v.1.1 = j) reg))
          by admit.

        replace
          (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ j)
             (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ i) reg))
          with
          (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ i)
             (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ j) reg))
          by admit.
        (set X := (filter (λ v : CoreN * RegName * Word, v.1.1 = j) reg)).
        (set Y := (filter (λ v : CoreN * RegName * Word, v.1.1 ≠ j) reg)).
        (set Pi := (λ v : CoreN * RegName * Word, v.1.1 ≠ i)).
        replace ( filter Pi X ∪ filter Pi Y ) with (filter Pi (X ∪ Y)) by admit.
        subst X Y Pi.
        replace ((filter (λ v : CoreN * RegName * Word, v.1.1 = j) reg
         ∪ filter (λ v : CoreN * RegName * Word, v.1.1 ≠ j) reg))
          with reg by (by rewrite map_union_filter).
        apply map_disjoint_filter.
      }
      iDestruct (big_sepM_union with "Hreg") as "[Hreg_j Hreg]".
      { apply map_disjoint_filter. }
      iClear "Hreg"; clear regs.

      (* We prove the WP for each core *)
      iSplitL "Hprog1 Hreg_i".
      - (* We extracts the needed registers for the full_run_spec *)
      iDestruct (big_sepM_delete _ _ (i, PC) with "Hreg_i") as "[HPC_i Hreg_i]".
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.
      iDestruct (big_sepM_delete _ _ (i, r_t0) with "Hreg_i") as "[Hadv_i Hreg_i]".
      rewrite lookup_delete_ne ; [|simplify_pair_eq] ; eauto.
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.
      destruct (Hreg1_valid r_t1) as (w1_i & Hr1_i & _); first (clear -i ; set_solver).
      iDestruct (big_sepM_delete _ _ (i, r_t1) with "Hreg_i") as "[Hr1_i Hreg_i]"; eauto.
      do 2 (rewrite lookup_delete_ne ; [|simplify_pair_eq]) ; eauto.
      apply map_filter_lookup_Some_2 ; [|by subst Pi ; cbn] ; eauto.

      iApply (buffer_full_run_spec1 _ _ _ _ _  _ (prog_end P1) _ _ _ _ _
               with "[$HPC_i $Hadv_i $Hr1_i Hreg_i Hprog1]") ; cycle -1.
      iDestruct (mkregion_sepM_to_sepL2 with "Hprog1") as "Hprog1".
      { apply (prog_size P1). }
      rewrite /buffer_prog1 Hprog1.
      iFrame "#∗".
      iSplitL ; last admit. (* TODO add hypothesis validity adversary --> only instructions ? *)

      iAssert ([∗ map] r↦w ∈
                 (delete (i, r_t1) (delete (i, r_t0) (delete (i, PC) regs_i) ))
                , r ↦ᵣ w ∗ ⌜is_cap w = false⌝)%I
        with "[Hreg_i]" as "Hreg_i".
      { iApply (big_sepM_mono with "Hreg_i"). intros r w Hr. cbn.
        apply lookup_delete_Some in Hr as [? Hr].
        apply lookup_delete_Some in Hr as [? Hr].
        apply lookup_delete_Some in Hr as [? Hr].
        subst regs_i.
        assert (Hr' := Hr).
        apply (map_filter_lookup_Some_1_2
                 (λ v : CoreN * RegName * Word, Pi v) reg r w) in Hr.
        subst Pi ; cbn in Hr.
        destruct r as [? r] ; inversion Hr ; subst.
        feed pose proof (Hreg1_valid r) as HH. clear -H3 ; set_solver.
        destruct HH as [? (? & ?)].
        iIntros ; iFrame ; iPureIntro.
        clear -H5 Hr' H6.
        cbn in *.
        apply map_filter_lookup_Some in Hr'.
        destruct Hr' as [? _].
        simplify_map_eq. auto.
      }
      iFrame.
      apply ExecPCPerm_RWX.
      { split ; [solve_addr |].
      split ; [|solve_addr ].
      pose proof (prog_size P1) ; solve_addr. }
      { apply contiguous_between_region_addrs.
        pose proof (prog_size P1) ; solve_addr. }
      solve_addr.
      solve_addr.
      solve_addr.
      { rewrite !dom_delete_L.
        set (X := set_map (λ r : RegName, (i, r)) all_registers_s).
        rewrite - !difference_difference_L.
        replace ( dom (gset (CoreN * RegName)) regs_i) with X by set_solver.
        set_solver.
      }
      - admit.
    }

    iIntros (es' t2) "%Hes %Hlength_es %Hstuck [Hreg' Hmem'] Hopt _".
    rewrite /mem_inv.
    iInv "Hinv_secret1" as ">Hsecret1" "_".
    iInv "Hinv_secret2" as ">Hsecret2" "_".
    assert (Hneq: (b_buf ^+ 4)%a ≠ (b_buf ^+ 3)%a ) by solve_addr
    ; solve_ndisj ; clear Hneq.
    iDestruct "Hsecret1" as "[Hsecret1 | Hsecret1 ]"
    ; iDestruct "Hsecret2" as "[Hsecret2 | Hsecret2 ]".

    - iDestruct (gen_heap_valid with "Hmem' Hsecret1") as "#%secret1".
      iDestruct (gen_heap_valid with "Hmem' Hsecret2") as "#%secret2".
      iApply fupd_mask_intro_discard; [set_solver|].
      iPureIntro.
      split ; left ; auto.

    - iDestruct (gen_heap_valid with "Hmem' Hsecret1") as "#%secret1".
      iDestruct (gen_heap_valid with "Hmem' Hsecret2") as "#%secret2".
      iApply fupd_mask_intro_discard; [set_solver|].
      iPureIntro.
      split ; [left|right] ; auto.


    - iDestruct (gen_heap_valid with "Hmem' Hsecret1") as "#%secret1".
      iDestruct (gen_heap_valid with "Hmem' Hsecret2") as "#%secret2".
      iApply fupd_mask_intro_discard; [set_solver|].
      iPureIntro.
      split ; [right|left] ; auto.


    - iDestruct (gen_heap_valid with "Hmem' Hsecret1") as "#%secret1".
      iDestruct (gen_heap_valid with "Hmem' Hsecret2") as "#%secret2".
      iApply fupd_mask_intro_discard; [set_solver|].
      iPureIntro.
      split ; right ; auto.

  Admitted.

End Adequacy.


  

End shared_buffer.
