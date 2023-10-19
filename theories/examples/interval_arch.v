From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import arch_sealing.
From cap_machine Require Import solve_pure proofmode map_simpl register_tactics.

Notation "a ↪ₐ w" := (mapsto (L:=Addr) (V:=Word) a DfracDiscarded w) (at level 20) : bi_scope.

Section interval.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {seals:sealStoreG Σ}
          {nainv: logrel_na_invs Σ} (* `{intg: intervalG Σ} *)
          `{MP: MachineParameters}.

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
     ∗ b ↦ unseal activation E cap
     ∗ b + 1 ↦ seal activation E cap *)
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
                    ; Mov r_t2 0
                    ; Mov r_t3 0
                    ; Mov r_t6 0
                    ; Mov r_t7 0
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
   *)
  Definition seal_env (d d' : Addr) ll ll' p b e a: iProp Σ :=
    (∃ d1 b1 e1 b2 e2, ⌜(d + 1 = Some d1 ∧ d + 2 = Some d')%a⌝ ∗ d ↦ₐ WCap E b1 e1 b1 ∗ d1 ↦ₐ WCap E b2 e2 b2 ∗
                                let wvar := WCap RWX ll ll' ll in
                                let wcode1 := WCap p b e a in
                                let wcode2 := WCap p b e (a ^+ length (unseal_instrs))%a in
                                ⌜(b1 + 8)%a = Some e1⌝ ∗ ⌜(b2 + 8)%a = Some e2⌝ ∗ ⌜(ll + 1)%a = Some ll'⌝
                                 ∗ ⌜ExecPCPerm p ∧ SubBounds b e a (a ^+ length (unseal_instrs ++ seal_instrs ++ make_seal_preamble_instrs 0 1))%a⌝
                                 ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
                                 ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
                                 ∗ codefrag a (unseal_instrs ++ seal_instrs ++ make_seal_preamble_instrs 0 1) (* NOTE: unlike OCPL, access to make_seal is lost! FIXME: consider exposing the sealing building blocks to adversary, or at least make a separate make_seal invariant with malloc/salloc access for better reuse *))%I.

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

  Lemma makeint_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w1 w2 (* input words. If they are not ints, the program crashes *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 ι3 ι4 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m f_m b_r e_r a_r a_r' (* malloc offset *)
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

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t1; r_t2]} →

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
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
       ∗ seal_state ι2 ll o isInterval
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
       ∗ ▷ ( (∃ (z1 z2 : Z) (w : Sealable), ⌜w1 = WInt z1 ∧ w2 = WInt z2⌝
                ∗ isInterval_int (Z.min z1 z2) (Z.max z1 z2) (WSealable w)
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WSealed o w
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
    iExtractList "Hregs" [r_t6;r_t7] as ["Hr_t6";"Hr_t7"].

    (* open the program and seal env invariants *)
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.
    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";auto.
    iMod (na_inv_acc with "Htable Hown") as "(>(Hpc_b & Ha_r') & Hown & Hcls'')";auto.
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d1 = true) as Hwb;[solve_addr|].

    (* run code up until malloc *)
    do 4 iInstr "Hcode". rewrite /makeint.
    focus_block 1 "Hcode" as a_mid Ha_mid "Hblock" "Hcont".

    (* malloc *)
    iApply (wp_wand _ _ _ (λ v, (Ψ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[ [H1 | H1] | H1]";iApply "HΨ";iFrame; iSimplifyEq; iFrame. }
    iInsertList "Hregs" [r_t7;r_t6;r_t2;r_t1;r_env].
    iApply malloc_spec;iFrameAutoSolve;[..|iFrame "Hmalloc Hown Hregs"];[|auto|clear;lia|..].
    { rewrite !dom_insert_L Hdom. pose proof (all_registers_s_correct r_t6) as Hin1. pose proof (all_registers_s_correct r_t7) as Hin2.
      pose proof (all_registers_s_correct r_t1) as Hin3. pose proof (all_registers_s_correct r_t2) as Hin4.
      pose proof (all_registers_s_correct r_env) as Hin5.
      clear -Hin1 Hin2 Hin3 Hin4 Hin5. rewrite !union_assoc_L.
      assert ({[PC; r_t0; r_env; r_t1; r_t2]} = {[PC; r_t0]} ∪ {[r_env; r_t1; r_t2]}) as ->;[set_solver|].
      assert ({[r_env; r_t1; r_t2; r_t6; r_t7]} = {[r_env; r_t1; r_t2]} ∪ {[r_t6; r_t7]}) as ->;[set_solver|].
      rewrite -(difference_difference_l_L _ {[PC; r_t0]}). rewrite union_comm_L union_assoc_L difference_union_L. set_solver. }

    (* malloc cleanup *)
    iNext. iIntros "(HPC & Hblock & Hpc_b & Ha_r' & Hres & Hr_t0 & Hown & Hregs)".
    iDestruct "Hres" as (ib ie Hibounds) "(Hr_t1 & Hie)".
    iMod ("Hcls''" with "[$Hown $Hpc_b $Ha_r']") as "Hown".
    iExtractList "Hregs" [r_env;r_t2;r_t6;r_t7] as ["Hr_env";"Hr_t2";"Hr_t6";"Hr_t7"].
    unfocus_block "Hblock" "Hcont" as "Hcode".
    rewrite !delete_insert_ne//.

    (* continue with the program *)
    focus_block 2 "Hcode" as a_mid1 Ha_mid1 "Hblock" "Hcont".
    destruct (is_z w1) eqn:Hisz1.
    2: { (* if w1 is not an int, program fails *)
      iInstr_lookup "Hblock" as "Hi" "Hcont2".
      wp_instr.
      iApplyCapAuto @wp_add_sub_lt_fail_r_r_1.
      wp_pure. iApply wp_value. by iRight. }
    destruct w1 as [z1 | |]; try inversion Hisz1. clear Hisz1.
    destruct (is_z w2) eqn:Hisz2.
    2: { (* if w2 is not an int, program fails *)
      iInstr_lookup "Hblock" as "Hi" "Hcont2".
      wp_instr.
      iApplyCapAuto @wp_add_sub_lt_fail_r_r_2.
      wp_pure. iApply wp_value. by iRight. }
    destruct w2 as [z2 | |]; try inversion Hisz2. clear Hisz2.

    (* at this point, we assume that the inputs were ints *)
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t3 Hregs]";[by simplify_map_eq|rewrite delete_insert_delete].
    do 3 (iInstr "Hblock").

    (* we are about to do the conditional jump. this can only be done manually. In each case, we will have to store *)
    (* z1 and z2 into the newly allocated pair *)
    (* we begin by preparing the resources for that store *)
    rewrite /region_mapsto /region_addrs_zeroes.
    destruct (ib + 1)%a eqn:Hi;[|exfalso;solve_addr+Hibounds Hi].
    assert (finz.seq_between ib ie = [ib;f]) as ->.
    { rewrite (finz_seq_between_split _ f);[|solve_addr+Hi Hibounds].
      rewrite finz_seq_between_singleton// finz_seq_between_singleton;[|solve_addr+Hi Hibounds]. auto. }
    assert ((finz.dist ib ie) = 2) as ->;[rewrite /finz.dist;solve_addr+Hibounds|iSimpl in "Hie"].
    iDestruct "Hie" as "(Hi1 & Hi2 & _)".
    assert (withinBounds ib ie ib = true) as Hwbi;[solve_addr+Hi Hibounds|].
    assert (withinBounds ib ie f = true) as Hwbi2;[solve_addr+Hi Hibounds|].
    (* get the general purpose register to remember r_t0 *)
    iExtract "Hregs" r_t8 as "Hr_t8".

    destruct (z1 <? z2)%Z eqn:Hz;iSimpl in "Hr_t2".
    - (* if z1 is less than z2 *)
      iInstr "Hblock".

      assert ((match pc_p with
             | E => WCap RX pc_b pc_e (a_mid1 ^+ 7)%a
             | _ => WCap pc_p pc_b pc_e (a_mid1 ^+ 7)%a
               end : Word)= WCap pc_p pc_b pc_e (a_mid1 ^+ 7)%a) as ->;[destruct pc_p;auto;by inversion Hexec|].
      assert ((f + -1)%a = Some ib) as Hi';[solve_addr+Hi|].
      iGo "Hblock".
      (* unfocus_block "Hblock" "Hcont" as "Hcode". *)

      (* activation code *)
      iExtract "Hregs" r_t20 as "Hr_t20".
      iApply closure_activation_spec; iFrameAutoSolve. iFrame "Hseal".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hseal)".

      (* seal subroutine *)
      (* focus on the seal block *)
      rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
      focus_block 1 "Hunsealseal_codefrag" as a_mid2 Ha_mid2 "Hblock'" "Hcont'".
      (* first we must prepare the register map *)
      iInsertList "Hregs" [r_t20;r_t8;r_t3;r_t7;r_t6;r_t2].
      iMod (intervals_alloc with "Hi1 Hi2") as "#Hcond";eauto.
      { clear -Hz. apply Z.ltb_lt in Hz. lia. }
      (* apply the seal spec *)
      codefrag_facts "Hblock'".
      iApply (seal_spec);
        [..|iFrame "Hown HsealLL Hblock' Hr_env Hr_t1 HPC Hr_t0"];[auto..|].
      iSplitL "Hcond".
      { iExists _,_. iFrame "Hcond". }
      iSplitR; [auto|].
      iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hres & Hblock' & Hown)".
      iDestruct "Hres" as (?) "(%Heq & Hr_t1 & _)". inversion Heq as [Hinv]; clear Heq. subst sb.
      (* we will need some regs for the final cleanup*)
      iExtractList "Hregs" [r_t20;r_t8;r_t2;r_t3;r_t6;r_t7] as ["Hr_t20";"Hr_t8";"Hr_t2";"Hr_t3";"Hr_t6";"Hr_t7"].
      unfocus_block "Hblock'" "Hcont'" as "Hunsealseal".
      rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].

      iGo "Hblock".

      (* we can finally finish by closing all invariants, cleanup the register map, and apply the continuation *)
      unfocus_block "Hblock" "Hcont" as "Hcode".
      iMod ("Hcls'" with "[$Hown Hseal Hunseal Hunsealseal Hd1 Hd]") as "Hown".
      { iExists _,_,_,_,_. iFrame. rewrite (addr_incr_eq Ha_mid2). iSimpl. iFrame. auto. }
      iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
      iInsertList "Hregs" [r_t20;r_t8;r_t7;r_t6;r_t3;r_t2].
      do 4 (rewrite (insert_commute _ _ r_t4);[|by auto]).
      do 4 (rewrite (insert_commute _ _ r_t5);[|by auto]).
      rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hdom; set_solver].
      rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hdom; set_solver].

      iApply (wp_wand with "[-]").
      iApply "Hφ". 2: {auto. }
      iExists z1,z2,_. iFrame "∗ #".
      assert (z1 `min` z2 = z1)%Z as ->;[clear -Hz;apply Z.ltb_lt in Hz;lia|].
      assert (z1 `max` z2 = z2)%Z as ->;[clear -Hz;apply Z.ltb_lt in Hz;lia|]. iFrame "#".
      iSplit;auto.

    - (* if z2 is less than or equal to z1 *)
      iInstr "Hblock".
      assert ((f + -1)%a = Some ib) as Hi';[solve_addr+Hi|].
      iGo "Hblock".
      (* unfocus_block "Hblock" "Hcont" as "Hcode". *)

      (* activation code *)
      iExtract "Hregs" r_t20 as "Hr_t20".
      iApply closure_activation_spec; iFrameAutoSolve. iFrame "Hseal".
      iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hseal)".

      (* seal subroutine *)
      (* focus on the seal block *)
      rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
      focus_block 1 "Hunsealseal_codefrag" as a_mid2 Ha_mid2 "Hblock'" "Hcont'".
      (* first we must prepare the register map *)
      iInsertList "Hregs" [r_t20;r_t8;r_t3;r_t7;r_t6;r_t2].
      iMod (intervals_alloc with "Hi1 Hi2") as "#Hcond";eauto.
      { clear -Hz. apply Z.ltb_ge in Hz. lia. }
      (* apply the seal spec *)
      codefrag_facts "Hblock'".
      iApply (seal_spec);
        [..|iFrame "Hown HsealLL Hblock' Hr_env Hr_t1 HPC Hr_t0"];[auto..|].
      iSplitL "Hcond".
      { iExists _,_. iFrame "Hcond". }
      iSplitR; [auto|].
      iNext. iIntros "(HPC & Hr_env & Hr_t0 & Hres & Hblock' & Hown)".
      iDestruct "Hres" as (?) "(%Heq & Hr_t1 & _)". inversion Heq as [Hinv]; clear Heq. subst sb.
      (* we will need some regs for the final cleanup*)
      iExtractList "Hregs" [r_t20;r_t8;r_t2;r_t3;r_t6;r_t7] as ["Hr_t20";"Hr_t8";"Hr_t2";"Hr_t3";"Hr_t6";"Hr_t7"].
      unfocus_block "Hblock'" "Hcont'" as "Hunsealseal".
      rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].

      iGo "Hblock".

      (* we can finally finish by closing all invariants, cleanup the register map, and apply the continuation *)
      unfocus_block "Hblock" "Hcont" as "Hcode".
      iMod ("Hcls'" with "[$Hown Hseal Hunseal Hunsealseal Hd1 Hd]") as "Hown".
      { iExists _,_,_,_,_. iFrame. rewrite (addr_incr_eq Ha_mid2). iSimpl. iFrame. auto. }
      iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".
      iInsertList "Hregs" [r_t20;r_t8;r_t7;r_t6;r_t3;r_t2].
      do 4 (rewrite (insert_commute _ _ r_t4);[|by auto]).
      do 4 (rewrite (insert_commute _ _ r_t5);[|by auto]).
      rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hdom; set_solver].
      rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hdom; set_solver].

      iApply (wp_wand with "[-]").
      iApply "Hφ". 2: {auto. }
      iExists z1,z2,_. iFrame "∗ #".
      assert (z1 `min` z2 = z2)%Z as ->;[clear -Hz;apply Z.ltb_ge in Hz;lia|].
      assert (z1 `max` z2 = z1)%Z as ->;[clear -Hz;apply Z.ltb_ge in Hz;lia|]. iFrame "#".
      iSplit;auto.
  Qed.

  Lemma makint_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 ι3 ι4 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        b_m e_m (* malloc offset: needed by the seal_env *)
        b_r e_r a_r a_r' f_m (* environment table *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (makeint f_m))%a →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

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
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
      ∗ seal_state ι2 ll o isInterval
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

    iExtractList "Hregs" [r_t1;r_t2] as ["Hr_t1";"Hr_t2"].
    iDestruct "Hr_t20" as (w20) "Hr_t20".
    iInsert "Hregs" r_t20.

    iApply makeint_spec;iFrameAutoSolve;[..|iFrame "∗ #"];auto.
    { rewrite dom_insert_L !dom_delete_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH".
    iDestruct "HH" as (? ? ? (?&?)) "(#Hi & HPC & Hr_t1 & Hr_env & Hr_t0 & Hown & Hregs)".

    iInsertList "Hregs" [r_env;r_t1;r_t0].

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. auto.
    iApply big_sepM_insert_2. cbn beta. iApply (sealLL_pred_interp with "HsealLL [Hi]"). by iExists _,_.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
  Qed.

  (* ---------------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------------- IMIN -------------------------------------------------- *)
  (* ---------------------------------------------------------------------------------------------------------- *)

  Local Existing Instance interp_weakening.if_persistent.
  Lemma imin_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        iw (* input sealed interval *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        p b e a (* seal/unseal adresses *)
        Φ Φs Ψ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imin))%a →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d d' d
       ∗ r_t1 ↦ᵣ iw
       (* proof that the provided value has been validly sealed *)
       ∗ ▷ (if is_sealed_with_o iw o then valid_sealed iw o Φs else True)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
       ∗ seal_state ι2 ll o isInterval
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imin)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ (z1 z2 : Z) w, ⌜iw = WSealed o w⌝
                ∗ isInterval_int z1 z2 (WSealable w)
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WInt z1
                ∗ r_t2 ↦ᵣ WInt 0%Z
                ∗ r_t5 ↦ᵣ WInt 0%Z
                ∗ r_t20 ↦ᵣ WInt 0%Z
                ∗ r_env ↦ᵣ WInt 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & #Hseal_valid & Hr_t2 & Hr_t5 & Hr_t20 & #Hseal_env & #HsealLL & Hown & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d = true) as Hwb;[solve_addr|].
    iGo "Hcode".

    iApply closure_activation_spec; iFrameAutoSolve. iFrame "Hunseal".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hunseal)".
    codefrag_facts "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
    focus_block_0 "Hunsealseal_codefrag" as "Hblock" "Hcont".
    iApply (wp_wand _ _ _ (λ v, ⌜v = FailedV⌝ ∨ Ψ v)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[H1 | H1]";iApply "HΨ";iFrame. iSimplifyEq. iFrame. }
    iApply unseal_spec;iFrameAutoSolve;[|iFrame "∗ #"]. solve_ndisj.
    iSplitR. iNext. iLeft. auto.
    iNext. iIntros "(HPC & Hr_t0 & Hres & Hr_t1 & Hblock & Hown)".
    iDestruct "Hr_t1" as (sb) "[%Hiw [Hr_t1 #Hint]]".
    unfocus_block "Hblock" "Hcont" as "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].
    iGo "Hcode".

    iDestruct "Hint" as (z1 z2) "Hint".
    iDestruct "Hint" as (bi ai ei [Heq [Hai Hei] ]) "(Hbi & Hei & %Hle)". rewrite Heq.

    iDestruct "Hbi" as "-#Hbi". iDestruct "Hei" as "-#Hei".
    iGo "Hcode".
    split;auto;solve_addr+Hai Hei.
    iGo "Hcode".
    iDestruct "Hbi" as "#Hbi". iDestruct "Hei" as "#Hei".

    (* lets begin by closing all our invariants *)
    iMod ("Hcls'" with "[Hunseal Hseal Hunsealseal_codefrag Hd Hd1 $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame "Hd Hd1". iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_. iFrame "∗ #". repeat (iSplit;[|eauto]). auto.
    iExists _,_,_. iFrame "#". eauto.
  Qed.

  Lemma imin_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imin))%a →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

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
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
      ∗ seal_state ι2 ll o isInterval
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
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
    (* We need this value later; create an equality for it now *)
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_dom;rewrite Hdom;set_solver|].
    iExtractList "Hregs" [r_t5;r_t2;r_t1] as ["Hr_t5";"Hr_t2";"Hr_t3";"Hr_t4";"Hr_t1"].
    iDestruct "Hr_t20" as (w20) "Hr_t20".


    (* interp vr_t1 holds, so also validly sealed *)
    iAssert (∃ Φs, ▷ if is_sealed_with_o w1 o then valid_sealed w1 o Φs else True )%I as (Φs) "Hv_t1".
    { iDestruct "Hregs_val" as "-#Hregs_val".
    iExtract "Hregs_val" r_t1 as "Hv_t1". (* Reuses the above value for r_t1 *)
    destruct (is_sealed_with_o _ _) eqn:Heq; last auto.
    destruct_word w1; try by inversion Heq.
    assert (sd = o) as ->. { clear -Heq. rewrite /is_sealed_with_o in Heq. solve_addr. }
    iDestruct (interp_valid_sealed with "Hv_t1") as "Hv_t1". iFrame.
    }

    iApply imin_spec;iFrameAutoSolve;[..|iFrame "∗ #"];auto.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t5";[eauto|].
    iSplitL "Hr_t20";[eauto|]. iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH". iDestruct "HH" as (? ? ?) "HH".
    iDestruct "HH" as "(%Hw1eq & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)". subst w1.

    (* we can then rebuild the register map *)
    iInsertList "Hregs" [r_t1;r_t2;r_t5;r_t20;r_env;r_t0].

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro. simpl.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. done. subst regs'.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
    Unshelve. intros. apply φ. constructor.
  Qed.


  (* ---------------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------------- IMAX -------------------------------------------------- *)
  (* ---------------------------------------------------------------------------------------------------------- *)

  Lemma imax_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        iw (* input sealed interval *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        ι0 ι1 ι2 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        p b e a (* seal/unseal adresses *)
        Φ Φs Ψ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imax))%a →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι0 ## ↑ι1) ->
    (up_close (B:=coPset) ι2 ## ↑ι0) ->
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ WCap RWX d d' d
       ∗ r_t1 ↦ᵣ iw
       (* proof that the provided value has been validly sealed *)
       ∗ ▷ (if is_sealed_with_o iw o then valid_sealed iw o Φs else True)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
       ∗ seal_state ι2 ll o isInterval
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imax)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ (z1 z2 : Z) w, ⌜iw = WSealed o w⌝
                ∗ isInterval_int z1 z2 (WSealable w)
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ WInt z2
                ∗ r_t2 ↦ᵣ WInt 0%Z
                ∗ r_t5 ↦ᵣ WInt 0%Z
                ∗ r_t20 ↦ᵣ WInt 0%Z
                ∗ r_env ↦ᵣ WInt 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & #Hseal_valid & Hr_t2 & Hr_t5 & Hr_t20 & #Hseal_env & #HsealLL & Hown & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag)".
    codefrag_facts "Hcode".
    assert (withinBounds d d' d = true) as Hwb;[solve_addr|].
    iGo "Hcode".

    iApply closure_activation_spec; iFrameAutoSolve. iFrame "Hunseal".
    iNext. iIntros "(HPC & Hr_t20 & Hr_env & Hunseal)".
    codefrag_facts "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion H2;subst;auto].
    focus_block_0 "Hunsealseal_codefrag" as "Hblock" "Hcont".
    iApply (wp_wand _ _ _ (λ v, ⌜v = FailedV⌝ ∨ Ψ v)%I with "[- Hfailed HΨ]").
    2: { iIntros (v) "[H1 | H1]";iApply "HΨ";iFrame. iSimplifyEq. iFrame. }
    iApply unseal_spec;iFrameAutoSolve;[|iFrame "∗ #"]. solve_ndisj.
    iSplitR. iNext. iLeft. auto.
    iNext. iIntros "(HPC & Hr_t0 & Hres & Hr_t1 & Hblock & Hown)".
    iDestruct "Hr_t1" as (sb) "[%Hiw [Hr_t1 #Hint]]".
    unfocus_block "Hblock" "Hcont" as "Hunsealseal_codefrag".

    rewrite updatePcPerm_cap_non_E;[|inversion Hexec;subst;auto].
    iGo "Hcode".

    iDestruct "Hint" as (z1 z2) "Hint".
    iDestruct "Hint" as (bi ai ei [Heq [Hai Hei] ]) "(Hbi & Hei & %Hle)". rewrite Heq.

    iDestruct "Hbi" as "-#Hbi". iDestruct "Hei" as "-#Hei".
    iGo "Hcode".
    split;auto;solve_addr+Hai Hei.
    iGo "Hcode".
    iDestruct "Hbi" as "#Hbi". iDestruct "Hei" as "#Hei".

    (* lets begin by closing all our invariants *)
    iMod ("Hcls'" with "[Hunseal Hseal Hunsealseal_codefrag Hd Hd1 $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame "Hd Hd1". iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_. iFrame "∗ #". repeat (iSplit;[|eauto]). auto.
    iExists _,_,_. iSplit; first auto. iFrame "#". eauto.
  Qed.


  Lemma imax_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 o (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        p b e a (* seal/unseal adresses *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (imax))%a →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_env; r_t20]} →

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
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a)
      ∗ seal_state ι2 ll o isInterval
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
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
    (* We need this value later; create an equality for it now *)
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_dom;rewrite Hdom;set_solver|].
    iExtractList "Hregs" [r_t5;r_t2;r_t1] as ["Hr_t5";"Hr_t2";"Hr_t3";"Hr_t4";"Hr_t1"].
    iDestruct "Hr_t20" as (w20) "Hr_t20".


    (* interp vr_t1 holds, so also validly sealed *)
    iAssert (∃ Φs, ▷ if is_sealed_with_o w1 o then valid_sealed w1 o Φs else True )%I as (Φs) "Hv_t1".
    { iDestruct "Hregs_val" as "-#Hregs_val".
    iExtract "Hregs_val" r_t1 as "Hv_t1". (* Reuses the above value for r_t1 *)
    destruct (is_sealed_with_o _ _) eqn:Heq; last auto.
    destruct_word w1; try by inversion Heq.
    assert (sd = o) as ->. { clear -Heq. rewrite /is_sealed_with_o in Heq. solve_addr. }
    iDestruct (interp_valid_sealed with "Hv_t1") as "Hv_t1". iFrame.
    }

    iApply imax_spec;iFrameAutoSolve;[..|iFrame "∗ #"];auto.
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t5";[eauto|].
    iSplitL "Hr_t20";[eauto|]. iSplitR.
    { iNext. iIntros (Hcontr). done. }

    iDestruct (jmp_to_unknown _ with "Hretval") as "Hcallback_now".
    iNext. iIntros "HH". iDestruct "HH" as (? ? ?) "HH".
    iDestruct "HH" as "(%Hw1eq & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)". subst w1.

    (* we can then rebuild the register map *)
    iInsertList "Hregs" [r_t1;r_t2;r_t5;r_t20;r_env;r_t0].

    (* finally we now apply the ftlr to conclude that the rest of the program does not get stuck *)
    set regs' := <[_:=_]> _.
    iApply ("Hcallback_now" $! regs' with "[] [$HPC Hregs $Hown]").
    { iPureIntro. simpl.
      rewrite !dom_insert_L Hdom. rewrite !singleton_union_difference_L. set_solver+. }
    iApply (big_sepM_sep with "[$Hregs Hregs_val]"). cbn beta.
    iApply big_sepM_insert_2. done. subst regs'.
    repeat (iApply big_sepM_insert_2; first by rewrite /= !fixpoint_interp1_eq //).
    iApply "Hregs_val".
    Unshelve. intros. apply φ. constructor.
  Qed.


End interval.
