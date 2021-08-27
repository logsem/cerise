From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import keylist_new dynamic_sealing_keys.
From cap_machine Require Import solve_pure proofmode map_simpl.

Notation "a ↪ₐ w" := (mapsto (L:=Addr) (V:=Word) a DfracDiscarded w) (at level 20) : bi_scope.

Section interval.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} (* `{intg: intervalG Σ} *)
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* interval := λ_, let (seal,unseal) = makeseal () in
                     let makeint = λ n1 n2, seal (if n1 ≤ n2 then (n1,n2) else (n2,n1)) in
                     let imin = λ i, fst (unseal i) in
                     let imax = λ i, snd (unseal i) in
                     (makeint, imin, imax)
   *)

  (* The following fst and snd are simplified here to work only on a capability that points to its lower bound *)
  (* A more general fst and snd operator could be created, but is for our use cases not necessary *)
  Definition fst_instrs r :=
    encodeInstrsW [ Load r_t1 r ].

  Definition snd_instrs r :=
    encodeInstrsW [ Lea r 1;
                  Load r_t1 r ].

  (* r_t1 ↦ WInt n1 ∗ r_t2 ↦ WInt n2 -> otherwise the program fails *)
  (* r_env ↦ (RWX, b, b + 2, b)
     ∗ b ↦ seal activation E cap
     ∗ b + 1 ↦ unseal activation E cap *)
  Definition makeint f_m :=
    encodeInstrsW [ Lea r_env 1
                    ; Load r_env r_env
                    ; Mov r_t6 r_t1
                    ; Mov r_t7 r_t2 (* move the n1 n2 parameters to make place for malloc *)
                  ] ++ malloc_instrs f_m 2%nat ++ (* allocate a region of size 2 for the interval pair *)
    encodeInstrsW [ Lt r_t2 r_t6 r_t7 (* check whether n1 < n2, this instruction fails if they are not ints *)
                    ; Mov r_t3 PC
                    ; Lea r_t3 6
                    ; Jnz r_t3 r_t2 (* if n2 ≤ n1, we must swap r6 and r7 *)
                    ; Mov r_t3 r_t6
                    ; Mov r_t6 r_t7
                    ; Mov r_t7 r_t3
                    ; Store r_t1 (inr r_t6) (* store min (n1 n2) into the lower bound, and max (n1 n2) into the upper bound *)
                    ; Lea r_t1 (1%Z)
                    ; Store r_t1 (inr r_t7)
                    ; Lea r_t1 (-1)%Z
                    ; Mov r_t8 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 3
                    ; Jmp r_env (* jmp to the seal function closure in r_env *)
                    (* the seal subroutine does most the clearing, however it will not clear r20, so we must do that now *)
                    ; Mov r_t20 0
                    ; Mov r_t0 r_t8
                    ; Mov r_t8 0
                    ; Jmp r_t0].

  (* r_t1 must be a sealed interval *)
  Definition imin :=
    encodeInstrsW [ Load r_env r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 3
                    ; Jmp r_env
                    ; Mov r_t0 r_t5
                    ; Mov r_t2 r_t1]
                  ++ fst_instrs r_t2 ++
    encodeInstrsW [Mov r_t2 0 ; Mov r_t5 0 ; Mov r_t20 0 ; Jmp r_t0].

  Definition imax :=
    encodeInstrsW [ Load r_env r_env
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 3
                    ; Jmp r_env
                    ; Mov r_t0 r_t5
                    ; Mov r_t2 r_t1]
                  ++ snd_instrs r_t2 ++
    encodeInstrsW [Mov r_t2 0 ; Mov r_t5 0 ; Mov r_t20 0 ; Jmp r_t0].



  Definition isInterval_int z1 z2 : Word → iProp Σ :=
    λ w, (∃ a1 a2 a3, ⌜w = WCap RWX a1 a3 a1 ∧ (a1 + 1 = Some a2)%a ∧ (a1 + 2 = Some a3)%a⌝
         ∗ a1 ↪ₐ WInt z1 ∗ a2 ↪ₐ WInt z2 ∗ ⌜(z1 <= z2)%Z⌝)%I.
  Definition isInterval : Word → iProp Σ := λ w, (∃ z1 z2, isInterval_int z1 z2 w)%I.

  Instance isInterval_timeless w : Timeless (isInterval w).
  Proof. apply _. Qed.
  Instance isInterval_persistent w : Persistent (isInterval w).
  Proof. apply _. Qed.

  (* the seal closure environment must contain:
     (1) the activation code the seal/unseal
     (2) the seal/unseal subroutines
     (3) a copy of a linking table containing the malloc enter capability at the bottom of its bounds
   To simplify things slightly, we are assuming that the linking table only contains the malloc capability,
   and that its size is 1 *)
  Definition seal_env (d d' : Addr) ll ll' p b e a b_m e_m b_r e_r : iProp Σ :=
    (∃ d1 b1 e1 b2 e2, ⌜(d + 1 = Some d1 ∧ d + 2 = Some d')%a⌝ ∗ d ↦ₐ WCap E b1 e1 b1 ∗ d1 ↦ₐ WCap E b2 e2 b2 ∗
                                let wvar := WCap RWX ll ll' ll in
                                let wcode1 := WCap p b e a in
                                let wcode2 := WCap p b e (a ^+ length (unseal_instrs))%a in
                                ⌜(b1 + 8)%a = Some e1⌝ ∗ ⌜(b2 + 8)%a = Some e2⌝ ∗ ⌜(ll + 1)%a = Some ll'⌝
                                 ∗ ⌜ExecPCPerm p ∧ SubBounds b e a (a ^+ length (unseal_instrs ++ seal_instrs 0 ++ make_seal_preamble_instrs 0))%a⌝
                                 ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
                                 ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
                                 ∗ codefrag a (unseal_instrs ++ seal_instrs 0 ++ make_seal_preamble_instrs 0)
                                 ∗ b ↦ₐ WCap RO b_r e_r b_r ∗ b_r ↦ₐ WCap E b_m e_m b_m
                                 ∗ ⌜(b_r + 1)%a = Some e_r⌝)%I.

  (* ---------------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------------- MAKEINT ------------------------------------------------ *)
  (* ---------------------------------------------------------------------------------------------------------- *)

  (* Allocating a new interval *)
  Lemma intervals_alloc ib ie a0 z1 z2 :
    (ib + 2)%a = Some ie →
    (ib + 1)%a = Some a0 →
    (z1 ≤ z2)%Z →
    ib ↦ₐ WInt z1 -∗
    a0 ↦ₐ WInt z2 ==∗ isInterval_int z1 z2 (WCap RWX ib ie ib).
  Proof.
    iIntros (Hcond1 Hcond2 Hle) "Hi Hi'".
    iMod (mapsto_persist with "Hi") as "#Hi".
    iMod (mapsto_persist with "Hi'") as "#Hi'".
    iModIntro. iExists _,_,_. iFrame "#". eauto.
  Qed.

  (* Two instances of the same interval agrees *)
  Lemma intervals_agree w z1 z2 z1' z2' :
    isInterval_int z1 z2 w -∗
    isInterval_int z1' z2' w -∗
    ⌜z1 = z1' ∧ z2 = z2'⌝.
  Proof.
    iIntros "#Hi #Hi'".
    iDestruct "Hi" as (b e a (Heq&He&Ha)) "(Hb & He & %Hle)".
    iDestruct "Hi'" as (b' e' a' (Heq'&He'&Ha')) "(Hb' & He' & %Hle')".
    simplify_eq.
    iDestruct (mapsto_agree with "Hb Hb'") as %Heq. inv Heq.
    iDestruct (mapsto_agree with "He He'") as %Heq. inv Heq.
    auto.
  Qed.

  (* TODO move to add sub lt rules file *)
  Lemma wp_add_sub_lt_fail_r_r_1 E ins dst r1 r2 w wdst p b e a w2 pc_p pc_b pc_e pc_a :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r1 ↦ᵣ WCap p b e a ∗ r2 ↦ᵣ w2 }}}
      Instr Executable
            @ E
    {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.
  Lemma wp_add_sub_lt_fail_r_r_2 E ins dst r1 r2 w wdst p b e a w2 pc_p pc_b pc_e pc_a :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r1 ↦ᵣ w2 ∗ r2 ↦ᵣ WCap p b e a }}}
      Instr Executable
            @ E
    {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_AddSubLt with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma makeint_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w1 w2 (* input words. If they are not ints, the program crashes *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 ι3 ι4 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m f_m b_r e_r a_r a_r' (* malloc offset *)
        b_t e_t (* seal/unseal closure table  *)
        rmap (* register map *)
        p b e a (* seal/unseal adresses *)
        Φ Ψ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (makeint f_m))%a →

    (* environment table: required by the seal and malloc spec *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t1; r_t2]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset)ι0 ⊆ ⊤ ∖ ↑ι1) ->
    (up_close (B:=coPset)ι4 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0) →
    (up_close (B:=coPset)ι2 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0) →
    (up_close (B:=coPset)ι3 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0 ∖ ↑ι2) →
    (up_close (B:=coPset)ι3 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0 ∖ ↑ι4) →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d d' d
       ∗ r_t1 ↦ᵣ w1
       ∗ r_t2 ↦ᵣ w2
       ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
       ∗ sealLL ι2 ll γ isInterval
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       ∗ interp wret
       (* malloc: required by the seal and malloc spec *)
       ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m)
       ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap RO b_r e_r a_r ∗ a_r' ↦ₐ WCap E b_m e_m b_m)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first (makeint f_m))
       (* the remaining registers are all valid: required for validity *)
       (* ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) *)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ b b' (z1 z2 : Z) pbvals (w : Word), ⌜(b',w) ∈ pbvals ∧ w1 = WInt z1 ∧ w2 = WInt z2 ∧ (b + 1)%a = Some b'⌝
                ∗ prefLL γ pbvals
                ∗ isInterval_int (Z.min z1 z2) (Z.max z1 z2) w
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WCap RWX b b' b'
                ∗ b ↦ₐ WInt 0
                ∗ r_env ↦ᵣ WInt 0
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤
                ∗ ([∗ map] r_i↦w_i ∈ <[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]>
                                (<[r_t8:=WInt 0%Z]> (<[r_t20:=WInt 0%Z]> rmap))))))), r_i ↦ᵣ w_i))
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hwb_r Hr Hdom Hdisj Hdisj2 Hdisj3 Hdisj4 Hdisj5) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hregs
    & #Hseal_env & #HsealLL & Hown & #Hretval & #Hmalloc & #Htable & #Hprog & Hfailed & HΨ & Hφ)".
    (* prepare registers *)
    set rmap2 := <[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]>
                                (<[r_t8:=WInt 0%Z]> (<[r_t20:=WInt 0%Z]> rmap))))))).
    assert (is_Some (rmap !! r_t6)) as [w6 Hw6];[apply elem_of_gmap_dom;rewrite Hdom;set_solver-|].
    assert (is_Some (rmap !! r_t7)) as [w7 Hw7];[apply elem_of_gmap_dom;rewrite Hdom;set_solver-|].
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]";[eauto|].
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]";[simplify_map_eq;eauto|].
    (* open the program and seal env invariants *)
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.
    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";auto.
    iMod (na_inv_acc with "Htable Hown") as "(>(Hpc_b & Ha_r') & Hown & Hcls'')";auto.
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag & Hb & Hb_t & %Hstable)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d1 = true) as Hwb;[solve_addr|].

    (* run code up until malloc *)
    do 4 iInstr "Hcode". rewrite /makeint.
    focus_block 1 "Hcode" as a_mid Ha_mid "Hblock" "Hcont".

    (* malloc *)
    iApply (wp_wand _ _ _ (λ v, (Ψ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[ [H1 | H1] | H1]";iApply "HΨ";iFrame; iSimplifyEq; iFrame. }
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne//].
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hregs $Hr_t6]") as "Hregs";[by simplify_map_eq|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
    iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
    iApply malloc_spec;iFrameCapSolve;[..|iFrame "Hmalloc Hown Hregs"];[|auto|clear;lia|..].
    { rewrite !dom_insert_L Hdom. pose proof (all_registers_s_correct r_t6) as Hin1. pose proof (all_registers_s_correct r_t7) as Hin2.
      pose proof (all_registers_s_correct r_t1) as Hin3. pose proof (all_registers_s_correct r_t2) as Hin4.
      pose proof (all_registers_s_correct r_env) as Hin5.
      clear -Hin1 Hin2 Hin3 Hin4 Hin5. rewrite !union_assoc_L.
      assert ({[PC; r_t0; r_env; r_t1; r_t2]} = {[PC; r_t0]} ∪ {[r_env; r_t1; r_t2]}) as ->;[set_solver|].
      assert ({[r_env; r_t1; r_t2; r_t6; r_t7]} = {[r_env; r_t1; r_t2]} ∪ {[r_t6; r_t7]}) as ->;[set_solver|].
      rewrite -(difference_difference_L _ {[PC; r_t0]}). rewrite union_comm_L union_assoc_L difference_union_L. set_solver. }

    (* malloc cleanup *)
    iNext. iIntros "(HPC & Hblock & Hpc_b & Ha_r' & Hres & Hr_t0 & Hown & Hregs)".
    iDestruct "Hres" as (ib ie Hibounds) "(Hr_t1 & Hie)".
    iMod ("Hcls''" with "[$Hown $Hpc_b $Ha_r']") as "Hown".
    rewrite delete_insert_ne// delete_insert;[|simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-].
    do 4 (rewrite (insert_commute _ _ r_t2)//). rewrite insert_insert.
    do 4 (rewrite (insert_commute _ _ r_env)//).
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_env Hregs]";[simplify_map_eq;eauto|rewrite delete_insert].
    2: simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-.
    do 4 (rewrite (insert_commute _ _ r_t6)//).
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t6 Hregs]";[simplify_map_eq;eauto|rewrite delete_insert_delete].
    do 4 (rewrite (insert_commute _ _ r_t7)//). rewrite delete_insert_ne//.
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t7 Hregs]";[simplify_map_eq;eauto|rewrite delete_insert_delete].
    unfocus_block "Hblock" "Hcont" as "Hcode".
    rewrite !delete_insert_ne//.
    iDestruct (big_sepM_insert with "Hregs") as "[Hr_t2 Hregs]";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].

    (* continue with the program *)
    focus_block 2 "Hcode" as a_mid1 Ha_mid1 "Hblock" "Hcont".
    destruct w1 as [z1|cap].
    2: { (* if w1 is not an int, program fails *)
      iInstr_lookup "Hblock" as "Hi" "Hcont2".
      wp_instr.
      iApplyCapAuto @wp_add_sub_lt_fail_r_r_1.
      wp_pure. iApply wp_value. by iRight. }
    destruct w2 as [z2|cap].
    2: { (* if w2 is not an int, program fails *)
      iInstr_lookup "Hblock" as "Hi" "Hcont2".
      wp_instr.
      iApplyCapAuto @wp_add_sub_lt_fail_r_r_2.
      wp_pure. iApply wp_value. by iRight. }

    (* at this point, we assume that the inputs were ints *)
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|rewrite delete_insert_delete].
    do 3 (iInstr "Hblock").

    (* we are about to do the conditional jump. this can only be done manually. In each case, we will have to store *)
    (* z1 and z2 into the newly allocated pair *)
    (* we begin by preparing the resources for that store *)
    rewrite /region_mapsto /region_addrs_zeroes.
    destruct (ib + 1)%a eqn:Hi;[|exfalso;solve_addr+Hibounds Hi].
    assert (region_addrs ib ie = [ib;a0]) as ->.
    { rewrite (region_addrs_split _ a0);[|solve_addr+Hi Hibounds].
      rewrite region_addrs_single// region_addrs_single;[|solve_addr+Hi Hibounds]. auto. }
    assert ((region_size ib ie) = 2) as ->;[rewrite /region_size;solve_addr+Hibounds|iSimpl in "Hie"].
    iDestruct "Hie" as "(Hi1 & Hi2 & _)".
    assert (withinBounds ib ie ib = true) as Hwbi;[solve_addr+Hi Hibounds|].
    assert (withinBounds ib ie a0 = true) as Hwbi2;[solve_addr+Hi Hibounds|].
    (* get the general purpose register to remember r_t0 *)
    assert (is_Some (rmap !! r_t8)) as [w8 Hw8];[apply elem_of_gmap_dom;rewrite Hdom;set_solver-|].
    iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq;eauto|].

    destruct (z1 <? z2)%Z eqn:Hz;iSimpl in "Hr_t2".
    - (* if z1 is less than z2 *)
      iInstr "Hblock".

      assert ((match pc_p with
             | E => WCap RX pc_b pc_e (a_mid1 ^+ 7)%a
             | _ => WCap pc_p pc_b pc_e (a_mid1 ^+ 7)%a
               end : Word)= WCap pc_p pc_b pc_e (a_mid1 ^+ 7)%a) as ->;[destruct pc_p;auto;by inversion Hexec|].
      assert ((a0 + -1)%a = Some ib) as Hi';[solve_addr+Hi|].
      iGo "Hblock".
      (* unfocus_block "Hblock" "Hcont" as "Hcode". *)

      (* activation code *)
      assert (is_Some (rmap !! r_t20)) as [w20 Hw20];[apply elem_of_gmap_dom;rewrite Hdom;set_solver-|].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[simplify_map_eq;eauto|].
      iApply closure_activation_spec; iFrameCapSolve. iFrame "Hseal".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hseal)".

      (* seal subroutine *)
      (* focus on the seal block *)
      rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
      focus_block 1 "Hunsealseal_codefrag" as a_mid2 Ha_mid2 "Hblock'" "Hcont'".
      (* first we must prepare the register map *)
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[by simplify_map_eq|rewrite insert_delete].
      repeat (rewrite -delete_insert_ne//).
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t8]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne// -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne// -delete_insert_ne// -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[by simplify_map_eq|rewrite insert_delete].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
      (* get the empty prefix resource *)
      iMod (na_inv_acc with "HsealLL Hown") as "(Hll & Hown & Hcls'')";auto.
      iMod (intervals_alloc with "Hi1 Hi2") as "#Hcond";eauto.
      { clear -Hz. apply Z.ltb_lt in Hz. lia. }
      iDestruct "Hll" as (hd) "[Hll Hex]". iDestruct "Hex" as (awvals) "[Hlist [>Hexact Hint] ]".
      iMod (get_partial_pref _ _ [] with "Hexact") as "[Hexact #Hpref]";[exists awvals;auto|].
      iMod ("Hcls''" with "[$Hown Hexact Hint Hlist Hll]") as "Hown";[iExists _; iFrame;iExists _;iFrame|].
      (* apply the seal spec *)
      codefrag_facts "Hblock'".
      iApply (seal_spec);
        [..|iFrame "Hregs Hpref Hown HsealLL Hmalloc Hb Hb_t Hblock' Hr_env Hr_t1 HPC Hr_t0"];[auto..|].
      { rewrite !dom_insert_L Hdom. clear. rewrite !union_assoc_L. rewrite -difference_difference_L.
        assert ({[r_t2; r_t6; r_t7; r_t3; r_t8; r_t20; r_t4; r_t5]} = {[r_t2]} ∪ {[r_t6; r_t7; r_t3; r_t8; r_t20; r_t4; r_t5]}) as ->;[set_solver|].
        rewrite union_comm_L union_assoc_L (difference_union_L).
        assert (∀ r, r ∈ all_registers_s);[apply all_registers_s_correct|]. set_solver. }
      { solve_addr+Hstable. }
      { solve_addr-. }
      iSplitL "Hcond".
      { iExists _,_. iFrame "Hcond". }
      iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hb & Hb_t & Hregs & Hres & Hblock' & Hown)".
      (* we will need r_t20 and r_t8 for the final cleanup*)
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[simplify_map_eq;eauto|].
      iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq;eauto|].
      unfocus_block "Hblock'" "Hcont'" as "Hunsealseal".
      rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].

      iGo "Hblock".

      (* we can finally finish by closing all invariants, cleanup the register map, and apply the continuation *)
      unfocus_block "Hblock" "Hcont" as "Hcode".
      iMod ("Hcls'" with "[$Hown Hseal Hunseal Hunsealseal Hb Hb_t Hd1 Hd]") as "Hown".
      { iExists _,_,_,_,_. iFrame. rewrite /incr_addr_default Ha_mid2. iSimpl. iFrame. auto. }
      iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
      iDestruct "Hres" as (a1 a2 pbvals Ha1) "(#Hpref' & Hr_t1 & Ha1)". rewrite app_nil_l.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t8]") as "Hregs";[by simplify_map_eq|].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[by simplify_map_eq|].
      map_simpl "Hregs".
      repeat (rewrite -(insert_commute _ _ r_t8);[|by auto]).
      repeat (rewrite -(insert_commute _ _ r_t20);[|by auto]).

      iApply "Hφ". iExists _,_,z1,z2,_,_. iFrame "∗ #".
      assert (z1 `min` z2 = z1)%Z as ->;[clear -Hz;apply Z.ltb_lt in Hz;lia|].
      assert (z1 `max` z2 = z2)%Z as ->;[clear -Hz;apply Z.ltb_lt in Hz;lia|]. iFrame "#".
      iSplit;auto. iPureIntro. apply elem_of_app. right. constructor.

    - (* if z2 is less than or equal to z1 *)
      iInstr "Hblock".
      assert ((a0 + -1)%a = Some ib) as Hi';[solve_addr+Hi|].
      iGo "Hblock".
      (* unfocus_block "Hblock" "Hcont" as "Hcode". *)

      (* activation code *)
      assert (is_Some (rmap !! r_t20)) as [w20 Hw20];[apply elem_of_gmap_dom;rewrite Hdom;set_solver-|].
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[simplify_map_eq;eauto|].
      iApply closure_activation_spec; iFrameCapSolve. iFrame "Hseal".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hseal)".

      (* seal subroutine *)
      (* focus on the seal block *)
      rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
      focus_block 1 "Hunsealseal_codefrag" as a_mid2 Ha_mid2 "Hblock'" "Hcont'".
      (* first we must prepare the register map *)
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[by simplify_map_eq|rewrite insert_delete].
      repeat (rewrite -delete_insert_ne//).
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t8]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne// -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs";[by simplify_map_eq|rewrite insert_delete -delete_insert_ne// -delete_insert_ne// -delete_insert_ne//].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[by simplify_map_eq|rewrite insert_delete].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
      (* get the empty prefix resource *)
      iMod (na_inv_acc with "HsealLL Hown") as "(Hll & Hown & Hcls'')";auto.
      iMod (intervals_alloc with "Hi1 Hi2") as "#Hcond";eauto.
      { clear -Hz. apply Z.ltb_ge in Hz. lia. }
      iDestruct "Hll" as (hd) "[Hll Hex]". iDestruct "Hex" as (awvals) "[Hlist [>Hexact Hint] ]".
      iMod (get_partial_pref _ _ [] with "Hexact") as "[Hexact #Hpref]";[exists awvals;auto|].
      iMod ("Hcls''" with "[$Hown Hexact Hint Hlist Hll]") as "Hown";[iExists _; iFrame;iExists _;iFrame|].
      (* apply the seal spec *)
      codefrag_facts "Hblock'".
      iApply (seal_spec );
        [..|iFrame "Hregs Hpref Hown HsealLL Hmalloc Hb Hb_t Hblock' Hr_env Hr_t1 HPC Hr_t0"];[auto..|].
      { rewrite !dom_insert_L Hdom. clear. rewrite !union_assoc_L. rewrite -difference_difference_L.
        assert ({[r_t2; r_t6; r_t7; r_t3; r_t8; r_t20; r_t4; r_t5]} = {[r_t2]} ∪ {[r_t6; r_t7; r_t3; r_t8; r_t20; r_t4; r_t5]}) as ->;[set_solver|].
        rewrite union_comm_L union_assoc_L (difference_union_L).
        assert (∀ r, r ∈ all_registers_s);[apply all_registers_s_correct|]. set_solver. }
      { solve_addr+Hstable. }
      { solve_addr-. }
      iSplitR.
      { iExists _,_. iFrame "Hcond". }
      iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hb & Hb_t & Hregs & Hres & Hblock' & Hown)".
      (* we will need r_t20 and r_t8 for the final cleanup*)
      iDestruct (big_sepM_delete _ _ r_t20 with "Hregs") as "[Hr_t20 Hregs]";[simplify_map_eq;eauto|].
      iDestruct (big_sepM_delete _ _ r_t8 with "Hregs") as "[Hr_t8 Hregs]";[simplify_map_eq;eauto|].
      unfocus_block "Hblock'" "Hcont'" as "Hunsealseal".
      rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].

      iGo "Hblock".

      (* we can finally finish by closing all invariants, cleanup the register map, and apply the continuation *)
      unfocus_block "Hblock" "Hcont" as "Hcode".
      iMod ("Hcls'" with "[$Hown Hseal Hunseal Hunsealseal Hb Hb_t Hd1 Hd]") as "Hown".
      { iExists _,_,_,_,_. iFrame. rewrite /(incr_addr_default a) Ha_mid2. iSimpl. iFrame. auto. }
      iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
      iDestruct "Hres" as (a1 a2 pbvals Ha1) "(#Hpref' & Hr_t1 & Ha1)". rewrite app_nil_l.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t8]") as "Hregs";[by simplify_map_eq|].
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[by simplify_map_eq|].
      map_simpl "Hregs".
      repeat (rewrite -(insert_commute _ _ r_t8);[|by auto]).
      repeat (rewrite -(insert_commute _ _ r_t20);[|by auto]).

      iApply "Hφ". iExists _,_,_,_,_,_. iFrame "∗ #".
      assert (z1 `min` z2 = z2)%Z as ->;[clear -Hz;apply Z.ltb_ge in Hz;lia|].
      assert (z1 `max` z2 = z1)%Z as ->;[clear -Hz;apply Z.ltb_ge in Hz;lia|]. iFrame "#".
      iSplit;auto. iPureIntro. apply elem_of_app. right. constructor.
  Qed.

  Lemma makint_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 ι3 ι4 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m b_t e_t (* malloc offset: needed by the seal_env *)
        b_r e_r a_r a_r' f_m (* environment table *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (makeint f_m))%a →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

    (* environment table: required by the seal and malloc spec *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →

    (* The two invariants have different names *)
    (up_close (B:=coPset)ι0 ⊆ ⊤ ∖ ↑ι1) ->
    (up_close (B:=coPset)ι4 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0) →
    (up_close (B:=coPset)ι2 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0) →
    (up_close (B:=coPset)ι3 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0 ∖ ↑ι2) →
    (up_close (B:=coPset)ι3 ⊆ ⊤ ∖ ↑ι1 ∖ ↑ι0 ∖ ↑ι4) →


    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX d d' d
      ∗ (∃ w, r_t20 ↦ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
      ∗ sealLL ι2 ll γ isInterval
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* malloc: only required by the seal spec *)
      ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m)
      ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap RO b_r e_r a_r ∗ a_r' ↦ₐ WCap E b_m e_m b_m)
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (codefrag a_first (makeint f_m))
      (* the remaining registers are all valid *)
      ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i)
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hexec Hsub Hdom Hwb Hf_m Hdisj Hdisj2 Hsidj3 Hdisj4 Hdisj5 φ)
            "(HPC & Hr_t0 & Hr_env & Hr_t20 & Hregs & #Hseal_env & #HsealLL & Hown
            & #Hretval & #Hmalloc & #Htable & #Hprog & #Hregs_val) Hφ".

    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[by simplify_map_eq|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[by simplify_map_eq|].
    iDestruct "Hr_t20" as (w20) "Hr_t20".
    iDestruct (big_sepM_insert _ _ r_t20 with "[$Hregs $Hr_t20]") as "Hregs";
      [simplify_map_eq; apply not_elem_of_dom; rewrite Hdom;set_solver+|].


    iApply makeint_spec;iFrameCapSolve;[..|iFrame "∗ #"];auto.
    { rewrite dom_insert_L !dom_delete_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH".
    iDestruct "HH" as (? ? ? ? ? ? (?&?&?&?))
                "(#Hpref & #Hi & HPC & Hr_t1 & Ha & Hr_env & Hr_t0 & Hown & Hregs)".

    (* we can then rebuild the register map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[by simplify_map_eq|].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs";
      [simplify_map_eq;apply not_elem_of_dom; rewrite Hdom; set_solver+|].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs";
      [simplify_map_eq;apply not_elem_of_dom; rewrite Hdom; set_solver+|].
    map_simpl "Hregs".

    (* we allocate the standard invariant for b0 *)
    iMod (inv_alloc (logN .@ b0) ⊤ (interp_ref_inv b0 interp) with "[Ha]") as "#Hb0".
    { iNext. iExists (WInt 0). iFrame. iApply fixpoint_interp1_eq. eauto. }

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. iSimpl. iApply fixpoint_interp1_eq. done. subst regs'.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply big_sepM_insert_2. iApply fixpoint_interp1_eq. iSimpl. rewrite region_addrs_single// /=.
    iSplit;auto. iExists interp. iFrame "Hb0". auto.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
  Qed.

  (* ---------------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------------- IMIN -------------------------------------------------- *)
  (* ---------------------------------------------------------------------------------------------------------- *)

  Lemma imin_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        iw (* input sealed interval *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m b_t e_t (* malloc offset: needed by the seal_env, but not important for this spec *)
        p b e a (* seal/unseal adresses *)
        Φ Ψ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imin))%a →

    (* environment table: only required by the seal spec *)
    (* withinBounds (RW, b_r, e_r, a_r') = true → *)
    (* (a_r + f_m)%a = Some a_r' → *)

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->


    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d d' d
       ∗ r_t1 ↦ᵣ iw
       (* ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t3 ↦ᵣ w)
       ∗ (∃ w, r_t4 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
       ∗ sealLL ι2 ll γ isInterval
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       (* ∗ interp wret *)
       (* malloc: only required by the seal spec *)
       (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
       (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ WCap (E, b_m, e_m, b_m)) *)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imin)
       (* the remaining registers are all valid *)
       (* ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) *)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ b b' e a (z1 z2 : Z) w pbvals, ⌜(b + 1)%a = Some b' ∧ iw = WCap RWX b e a ∧ (b',w) ∈ pbvals⌝
                ∗ prefLL γ pbvals
                ∗ isInterval_int z1 z2 w
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WInt z1
                ∗ r_t2 ↦ᵣ WInt 0%Z
                ∗ r_t3 ↦ᵣ WInt 0%Z
                ∗ r_t4 ↦ᵣ WInt 0%Z
                ∗ r_t5 ↦ᵣ WInt 0%Z
                ∗ r_t20 ↦ᵣ WInt 0%Z
                ∗ r_env ↦ᵣ WInt 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20
    & #Hseal_env & #HsealLL & Hown & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag & Hb & Hb_t & %)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d = true) as Hwb;[solve_addr|].
    iGo "Hcode".

    iApply closure_activation_spec; iFrameCapSolve. iFrame "Hunseal".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hunseal)".
    codefrag_facts "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
    focus_block_0 "Hunsealseal_codefrag" as "Hblock" "Hcont".
    iApply (wp_wand _ _ _ (λ v, ⌜v = FailedV⌝ ∨ Ψ v)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[H1 | H1]";iApply "HΨ";iFrame. iSimplifyEq. iFrame. }
    iApply unseal_spec;iFrameCapSolve;[|iFrame "∗ #"]. solve_ndisj.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|]. iSplitL "Hr_t4";[eauto|].
    iSplitR. iNext. iLeft. auto.
    iNext. iIntros "(HPC & Hr_t0 & Hr_t2 & Hres & Hr_t3 & Hr_t4 & Hblock & Hown)".
    unfocus_block "Hblock" "Hcont" as "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].
    iDestruct "Hres" as (b' b'' a' w pbvals [Heq [Hb' Hbw] ]) "(#Hpref & Hr_t1 & Hr_env & #Hint)". simplify_eq.
    iGo "Hcode".

    (* we must now extract from the sealLL invariant that w is indeed an interval element *)
    iMod (na_inv_acc with "HsealLL Hown") as "(Hw & Hown & Hcls'')";[auto|solve_ndisj|].
    iDestruct "Hw" as (hd) "(>Hll & Hawvals)".
    iDestruct "Hawvals" as (awvals) "(HisList & >Hexact & >#Hintervals)".
    iDestruct (know_pref with "Hexact Hpref") as %Hpref.
    assert (∃ k, awvals !! k = Some (b'', w)) as [k Hin].
    { apply elem_of_list_lookup in Hbw as [k Hk]. destruct Hpref;subst.
      exists k. by apply lookup_app_l_Some. }
    iDestruct "Hint" as (z1 z2) "Hint".
    iDestruct "Hint" as (bi ai ei [Heq [Hai Hei] ]) "(Hbi & Hei & %Hle)". subst w.
    (* iDestruct (big_sepL_lookup_acc with "Hintervals") as "[#Hw Hacc]";[eauto|]. *)
    (* iDestruct "Hw" as (a1 a2 a3 [Heq [Hincr Hincr'] ] z1 z2) "[Ha1 [Ha2 [%Hle #Hi]]]". simpl in Heq. rewrite Heq. *)

    iDestruct "Hbi" as "-#Hbi". iDestruct "Hei" as "-#Hei".
    iGo "Hcode".
    split;auto;solve_addr+Hai Hei.
    iGo "Hcode".
    iDestruct "Hbi" as "#Hbi". iDestruct "Hei" as "#Hei".

    (* lets begin by closing all our invariants *)
    iMod ("Hcls''" with "[Hll HisList Hexact $Hown]") as "Hown".
    { iNext. iExists _. iFrame. iExists _. iFrame. iFrame "#". }

    iMod ("Hcls'" with "[Hunseal Hseal Hunsealseal_codefrag Hd Hd1 Hb Hb_t $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame "Hd Hd1". iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_,_,_,_,_,_. iFrame "∗ #". repeat (iSplit;[|eauto]). auto.
    iExists _,_,_. iFrame "#". eauto.
  Qed.

  Lemma imin_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m b_t e_t (* malloc offset: needed by the seal_env, but not important for this spec *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imin))%a →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

    (* environment table: only required by the seal spec *)
    (* withinBounds (RW, b_r, e_r, a_r') = true → *)
    (* (a_r + f_m)%a = Some a_r' → *)

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->


    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX d d' d
      ∗ (∃ w, r_t20 ↦ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
      ∗ sealLL ι2 ll γ isInterval
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* malloc: only required by the seal spec *)
      (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
      (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ WCap (E, b_m, e_m, b_m)) *)
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (codefrag a_first imin)
      (* the remaining registers are all valid *)
      ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i)
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hexec Hsub Hdom Hdisj Hdisj2 Hsidj3 φ) "(HPC & Hr_t0 & Hr_env & Hr_t20 & Hregs & #Hseal_env & #HsealLL & Hown & #Hretval & #Hprog & #Hregs_val) Hφ".

    (* extract the registers used by the program *)
    assert (is_Some (rmap !! r_t5)) as [w5 Hw5];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]";[eauto|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iApply imin_spec;iFrameCapSolve;[..|iFrame "∗ #"];auto.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
    iSplitL "Hr_t4";[eauto|]. iSplitL "Hr_t5";[eauto|].
    iSplitL "Hr_t20";[eauto|]. iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ?) "HH".
    iDestruct "HH" as ((?&?)) "(#Hpref & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)".

    (* we can then rebuild the register map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[by simplify_map_eq|rewrite insert_delete; repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|repeat rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t5]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].

    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    (* iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|]. *)
    (* rewrite -(insert_insert _  PC _ (WInt 0%Z)). *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro. simpl.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. done. subst regs'.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
  Qed.


  (* ---------------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------------- IMAX -------------------------------------------------- *)
  (* ---------------------------------------------------------------------------------------------------------- *)

  Lemma imax_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        iw (* input sealed interval *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m b_t e_t (* malloc offset: needed by the seal_env, but not important for this spec *)
        p b e a (* seal/unseal adresses *)
        Φ Ψ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imax))%a →

    (* environment table: only required by the seal spec *)
    (* withinBounds (RW, b_r, e_r, a_r') = true → *)
    (* (a_r + f_m)%a = Some a_r' → *)

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->


    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d d' d
       ∗ r_t1 ↦ᵣ iw
       (* ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t3 ↦ᵣ w)
       ∗ (∃ w, r_t4 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
       ∗ sealLL ι2 ll γ isInterval
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       (* ∗ interp wret *)
       (* malloc: only required by the seal spec *)
       (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
       (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ WCap (E, b_m, e_m, b_m)) *)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imax)
       (* the remaining registers are all valid *)
       (* ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) *)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ b b' e a (z1 z2 : Z) w pbvals, ⌜iw = WCap RWX b e a ∧ (b + 1)%a = Some b' ∧ (b',w) ∈ pbvals⌝
                ∗ prefLL γ pbvals
                ∗ isInterval_int z1 z2 w
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WInt z2
                ∗ r_t2 ↦ᵣ WInt 0%Z
                ∗ r_t3 ↦ᵣ WInt 0%Z
                ∗ r_t4 ↦ᵣ WInt 0%Z
                ∗ r_t5 ↦ᵣ WInt 0%Z
                ∗ r_t20 ↦ᵣ WInt 0%Z
                ∗ r_env ↦ᵣ WInt 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20
    & #Hseal_env & #HsealLL & Hown & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag & Hb & Hb_t & %)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d = true) as Hwb;[solve_addr|].
    iGo "Hcode".

    iApply closure_activation_spec; iFrameCapSolve. iFrame "Hunseal".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hunseal)".
    codefrag_facts "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
    focus_block_0 "Hunsealseal_codefrag" as "Hblock" "Hcont".
    iApply (wp_wand _ _ _ (λ v, ⌜v = FailedV⌝ ∨ Ψ v)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[H1 | H1]";iApply "HΨ";iFrame. iSimplifyEq. iFrame. }
    iApply unseal_spec;iFrameCapSolve;[|iFrame "∗ #"]. solve_ndisj.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|]. iSplitL "Hr_t4";[eauto|].
    iSplitR. iNext. iLeft. auto.
    iNext. iIntros "(HPC & Hr_t0 & Hr_t2 & Hres & Hr_t3 & Hr_t4 & Hblock & Hown)".
    unfocus_block "Hblock" "Hcont" as "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].
    iDestruct "Hres" as (b' b'' a' w pbvals [Heq [Hb' Hbw] ]) "(#Hpref & Hr_t1 & Hr_env & #Hint)". simplify_eq.
    iGo "Hcode".

    (* we must now extract from the sealLL invariant that w is indeed an interval element *)
    iMod (na_inv_acc with "HsealLL Hown") as "(Hw & Hown & Hcls'')";[auto|solve_ndisj|].
    iDestruct "Hw" as (hd) "(>Hll & Hawvals)".
    iDestruct "Hawvals" as (awvals) "(HisList & >Hexact & >Hintervals)".
    iDestruct (know_pref with "Hexact Hpref") as %Hpref.
    assert (∃ k, awvals !! k = Some (b'', w)) as [k Hin].
    { apply elem_of_list_lookup in Hbw as [k Hk]. destruct Hpref;subst.
      exists k. by apply lookup_app_l_Some. }

    iDestruct "Hint" as (z1 z2) "Hint".
    iDestruct "Hint" as (bi ai ei [Heq [Hai Hei] ]) "(Hbi & Hei & %Hle)". subst w.
    iDestruct "Hbi" as "-#Hbi". iDestruct "Hei" as "-#Hei".

    iGo "Hcode". split;auto;solve_addr+Hai Hei.
    iGo "Hcode".

    (* lets begin by closing all our invariants *)
    iDestruct "Hbi" as "#Hbi". iDestruct "Hei" as "#Hei".
    iDestruct "Hintervals" as "#Hintervals".
    iMod ("Hcls''" with "[Hll HisList Hexact $Hown]") as "Hown".
    { iNext. iExists _. iFrame. iExists _. iFrame "∗ #". }

    iMod ("Hcls'" with "[Hunseal Hseal Hb Hb_t Hunsealseal_codefrag Hd Hd1 $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame "Hd Hd1". iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_,_,_,_,_,_. iFrame "∗ #". repeat (iSplit;[|eauto]). eauto. iExists bi,ai,_. iFrame "#". eauto.
  Qed.

  Lemma imax_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m b_t e_t (* malloc offset: needed by the seal_env, but not important for this spec *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imax))%a →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

    (* environment table: only required by the seal spec *)
    (* withinBounds (RW, b_r, e_r, a_r') = true → *)
    (* (a_r + f_m)%a = Some a_r' → *)

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->


    {{{ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX d d' d
      ∗ (∃ w, r_t20 ↦ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a b_m e_m b_t e_t)
      ∗ sealLL ι2 ll γ isInterval
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* malloc: only required by the seal spec *)
      (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
      (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ WCap (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ WCap (E, b_m, e_m, b_m)) *)
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (codefrag a_first imax)
      (* the remaining registers are all valid *)
      ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i)
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hexec Hsub Hdom Hdisj Hdisj2 Hsidj3 φ) "(HPC & Hr_t0 & Hr_env & Hr_t20 & Hregs & #Hseal_env & #HsealLL & Hown & #Hretval & #Hprog & #Hregs_val) Hφ".

    (* extract the registers used by the program *)
    assert (is_Some (rmap !! r_t5)) as [w5 Hw5];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]";[eauto|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iApply imax_spec;iFrameCapSolve;[..|iFrame "∗ #"];auto.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
    iSplitL "Hr_t4";[eauto|]. iSplitL "Hr_t5";[eauto|].
    iSplitL "Hr_t20";[eauto|]. iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ?) "HH".
    iDestruct "HH" as ((?&?)) "(#Hpref & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)".

    (* we can then rebuild the register map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[by simplify_map_eq|rewrite insert_delete; repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[by simplify_map_eq|repeat rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t5]") as "Hregs";[by simplify_map_eq|rewrite insert_delete;repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t20]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|repeat rewrite -delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].

    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    (* iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|]. *)
    (* rewrite -(insert_insert _  PC _ (WInt 0%Z)). *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro. simpl.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. done. subst regs'.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
  Qed.


End interval.
