From iris.algebra Require Import agree auth gmap.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous fundamental.
From cap_machine Require Import list_new dynamic_sealing.
From cap_machine Require Import solve_pure proofmode map_simpl.

Definition intervalUR := gmapUR (leibnizO Addr) (agreeR (prodO ZO ZO)).
Class intervalG Σ := IntervalG { intervalg_inG :> inG Σ (authUR intervalUR); interval_name : gname }.

Section interval_RA.
  Context `{intervalG}.
  Definition int_def (a : Addr) (z1 z2 : Z) : iProp Σ :=
    own interval_name (◯ {[ a := to_agree (z1,z2) ]}).
  Definition int_aux : seal (@int_def). Proof. by eexists. Qed.
  Definition int := int_aux.(unseal).
  Definition int_eq : @int = @int_def := int_aux.(seal_eq).

  Definition intervals_def m : iProp Σ :=
    own interval_name (● m).
  Definition intervals_aux : seal (@intervals_def). Proof. by eexists. Qed.
  Definition intervals := intervals_aux.(unseal).
  Definition intervals_eq : @intervals = @intervals_def := intervals_aux.(seal_eq).

  Notation "a ↪ ( z1 , z2 )" := (int a z1 z2) (at level 20, format "a  ↪ ( z1 , z2 )") : bi_scope.

  Lemma int_agree a (z1 z2 t1 t2 : Z) :
    a ↪ (z1,z2) -∗ a ↪ (t1,t2) -∗ ⌜z1 = t1 ∧ z2 = t2⌝.
  Proof.
    iIntros "Ha Ha'".
    rewrite int_eq /int_def.
    iCombine "Ha Ha'" as "Ha".
    iDestruct (own_valid with "Ha") as %Hval%auth_frag_valid_1%singleton_valid%to_agree_op_valid_L.
    simplify_eq. done.
  Qed.

  Global Instance int_timeless : Timeless (int a z1 z2).
  Proof. rewrite int_eq. apply _. Qed.

  Global Instance int_Persistent : Persistent (int a z1 z2).
  Proof. rewrite int_eq. apply _. Qed.

  Global Instance intervals_timeless : Timeless (intervals m).
  Proof. rewrite intervals_eq. apply _. Qed.
  

  Lemma allocate_inv a z1 z2 m :
    m !! a = None →
    intervals m ==∗ intervals (<[a:=to_agree (z1,z2)]> m) ∗ a ↪ (z1,z2).
  Proof.
    rewrite intervals_eq int_eq /intervals_def /int_def.
    iIntros (Hnone) "Hm".
    iMod (own_update with "Hm") as "Hm".
    apply auth_update_alloc. 2: by iDestruct "Hm" as "[$ $]".
    apply alloc_singleton_local_update;[auto|done].
  Qed.

End interval_RA.
Notation "a ↪ ( z1 , z2 )" := (int a z1 z2) (at level 20, format "a  ↪ ( z1 , z2 )") : bi_scope.

Section interval.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} `{intg: intervalG Σ}
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* interval := λ_, let (seal,unseal) = makeseal () in
                     let makeint = λ n1 n2, seal (if n1 ≤ n2 then (n1,n2) else (n2,n1)) in
                     let imin = λ i, fst (unseal i) in
                     let imax = λ i, snd (unseal i) in
                     let isum = λ i, let x = unseal i in
                                     λ j, let y = unseal j in
                                          seal (fst x + fst y, snd x + snd y) in
                     (makeint, imin, imax, isum)
   *)

  (* The following fst and snd are simplified here to work only on a capability that points to its lower bound *)
  (* A more general fst and snd operator could be created, but is for our use cases not necessary *)
  Definition fst_instrs r :=
    encodeInstrsW [ Load r_t1 r ].

  Definition snd_instrs r :=
    encodeInstrsW [ Lea r 1;
                  Load r_t1 r ].

  (* r_t1 ↦ inl n1 ∗ r_t2 ↦ inl n2 -> otherwise the program fails *)
  (* r_env ↦ (RWX, b, b + 2, b)
     ∗ b ↦ seal activation E cap
     ∗ b + 1 ↦ unseal activation E cap *)
  Definition makeint f_m :=
    encodeInstrsW [ Load r_env r_env
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
                    ; Jmp r_env (* jmp to the seal function closure in r_env *)].
  (* the seal subroutine does the clearing, and will jump to r_t0 when done *)

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

  Definition isum f_m :=
    encodeInstrsW [ Mov r_t6 r_env
                    ; Mov r_t7 r_t2
                    ; Lea r_t6 1
                    ; Load r_env r_t6
                    ; Mov r_t5 r_t0
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t8 r_t1 (* r_t8 contains the first interval i *)
                    ; Mov r_t1 r_t7
                    ; Load r_env r_t6
                    ; Mov r_t0 PC
                    ; Lea r_t0 (unseal_instrs_length + 2)
                    ; Jmp r_env
                    ; Mov r_t0 r_t5
                    ; Mov r_t9 r_t1] (* r_t9 contains the second interval j *)
                  ++ fst_instrs r_t8 ++ encodeInstrsW [Mov r_t2 r_t1] ++ fst_instrs r_t9
                  ++ encodeInstrsW [Add r_t3 r_t1 r_t2]
                  ++ snd_instrs r_t8 ++ encodeInstrsW [Mov r_t2 r_t1] ++ snd_instrs r_t9 ++
    encodeInstrsW [ Add r_t2 r_t1 r_t2
                    ; Mov r_t1 r_t3
                    ; Mov r_env r_t6]
                  ++ makeint f_m.


  Definition isInterval : (Addr * Word) → iProp Σ :=
    λ aw, (∃ a1 a2 a3, ⌜aw.2 = inr (RWX,a1,a3,a1) ∧ (a1 + 1 = Some a2)%a ∧ (a1 + 2 = Some a3)%a⌝
         ∗ ∃ z1 z2, a1 ↦ₐ inl z1 ∗ a2 ↦ₐ inl z2 ∗ ⌜(z1 <= z2)%Z⌝ ∗ aw.1 ↪ (z1,z2))%I.

  Definition isIntervals : list (Addr * Word) -> iProp Σ :=
    (λ bvals, ([∗ list] aw ∈ bvals, isInterval aw) ∗ ∃ m, intervals m ∗ ⌜dom (gset Addr) m = list_to_set bvals.*1⌝)%I.

  Instance isInterval_timeless : Timeless (isInterval w).
  Proof. apply _. Qed.

  Instance isIntervals_timeless : Timeless (isIntervals bvals).
  Proof. apply _. Qed.

  Definition seal_env (d d' : Addr) ll ll' p b e a f_m : iProp Σ :=
    (∃ d1 b1 e1 b2 e2, ⌜(d + 1 = Some d1 ∧ d + 2 = Some d')%a⌝ ∗ d ↦ₐ inr (E, b1, e1, b1) ∗ d1 ↦ₐ inr (E, b2, e2, b2) ∗
                                let wvar := inr (RWX, ll, ll', ll) in
                                let wcode1 := inr (p,b,e,a)%a in
                                let wcode2 := inr (p,b,e,a ^+ length (unseal_instrs))%a in
                                ⌜(b1 + 8)%a = Some e1⌝ ∗ ⌜(b2 + 8)%a = Some e2⌝ ∗ ⌜(ll + 1)%a = Some ll'⌝
                                 ∗ ⌜ExecPCPerm p ∧ SubBounds b e a (a ^+ length (unseal_instrs ++ seal_instrs f_m))%a⌝
                                 ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
                                 ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
                                 ∗ codefrag a (unseal_instrs ++ seal_instrs f_m))%I.

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
        f_m (* malloc offset: needed by the seal_env, but not important for this spec *)
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


    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ inr (RWX,d,d',d)
       ∗ r_t1 ↦ᵣ iw
       (* ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t3 ↦ᵣ w)
       ∗ (∃ w, r_t4 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a f_m)
       ∗ sealLL ι2 ll γ isIntervals
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       ∗ interp wret
       (* malloc: only required by the seal spec *)
       (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
       (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ inr (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)) *)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imin)
       (* the remaining registers are all valid *)
       (* ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) *)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ p b e a (z1 z2 : Z) w pbvals p' b' e' a', ⌜iw = inr (p,b,e,a) ∧ w = inr (p',b',e',a') ∧ (b,w) ∈ pbvals ∧ (z1 <= z2)%Z⌝
                ∗ prefLL γ pbvals
                ∗ b ↪ (z1,z2)
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ inl z1
                ∗ r_t2 ↦ᵣ inl 0%Z
                ∗ r_t3 ↦ᵣ inl 0%Z
                ∗ r_t4 ↦ᵣ inl 0%Z
                ∗ r_t5 ↦ᵣ inl 0%Z
                ∗ r_t20 ↦ᵣ inl 0%Z
                ∗ r_env ↦ᵣ inl 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20
    & #Hseal_env & #HsealLL & Hown & #Hretval & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag)".
    codefrag_facts "Hcode".
    assert (withinBounds (RWX, d, d', d) = true) as Hwb;[solve_addr|].
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
    iDestruct "Hres" as (p' b' e' a' b1' w pbvals [Heq [Hb Hbw] ]) "(#Hpref & Hr_t1 & Hr_env)". simplify_eq.
    iGo "Hcode".

    (* we must now extract from the sealLL invariant that w is indeed an interval element *)
    iMod (na_inv_acc with "HsealLL Hown") as "(Hw & Hown & Hcls'')";[auto|solve_ndisj|].
    iDestruct "Hw" as (hd) "(>Hll & Hawvals)".
    iDestruct "Hawvals" as (awvals) "(HisList & >Hexact & >Hintervals)".
    iDestruct (know_pref with "Hexact Hpref") as %Hpref.
    assert (∃ k, awvals !! k = Some (b', w)) as [k Hin].
    { apply elem_of_list_lookup in Hbw as [k Hk]. destruct Hpref;subst.
      exists k. by apply lookup_app_l_Some. }
    iDestruct "Hintervals" as "[Hintervals Hm]".
    iDestruct (big_sepL_lookup_acc with "Hintervals") as "[Hw Hacc]";[eauto|].
    iDestruct "Hw" as (a1 a2 a3 [Heq [Hincr Hincr'] ] z1 z2) "[Ha1 [Ha2 [%Hle #Hi]]]". simpl in Heq. rewrite Heq.

    iGo "Hcode". split;auto;solve_addr+Hincr Hincr'.
    iGo "Hcode".

    (* lets begin by closing all our invariants *)
    iMod ("Hcls''" with "[Hacc Ha1 Ha2 Hll HisList Hexact $Hown Hm]") as "Hown".
    { iNext. iExists _. iFrame. iExists _. iFrame. iApply "Hacc". iExists _,_,_. repeat iSplit;eauto. iExists _,_. iFrame "∗ #". auto. }

    iMod ("Hcls'" with "[Hunseal Hseal Hunsealseal_codefrag Hd Hd1 $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_,_,_,_,_. iFrame. iExists _,_,_,_,_. iFrame "#". eauto.
  Qed.

  Lemma imin_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        f_m (* malloc offset: needed by the seal_env, but not important for this spec *)
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


    {{{ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,d,d',d)
      ∗ (∃ w, r_t20 ↦ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a f_m)
      ∗ sealLL ι2 ll γ isIntervals
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* malloc: only required by the seal spec *)
      (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
      (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ inr (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)) *)
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

    iDestruct (jmp_or_fail_spec with "Hretval") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm wret))).
    2: { iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ? ? ?) "HH".
         iDestruct "HH" as (? ? ?) "(_ & _ & HPC & _)".
         iApply "Hcont". iFrame "HPC". iIntros (Hcond). done. }
    iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ? ? ?) "HH".
    iDestruct "HH" as (? ? (?&?&?)) "(#Hpref & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)".
    iDestruct "Hcont" as (? ? ? ? Heq') "Hcont";simplify_eq.

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
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
    rewrite -(insert_insert _  PC _ (inl 0%Z)).
    iDestruct ("Hcont" with "[$Hregs $Hown]") as "[_ $]". iClear "Hcont".
    iSplit.
    - iPureIntro. simpl. intros y. apply elem_of_gmap_dom.
      rewrite !dom_insert_L Hdom. pose proof (all_registers_s_correct y) as Hx. set_solver+Hx.
    - iIntros (r Hne). rewrite /RegLocate. consider_next_reg r PC. done.
      consider_next_reg r r_t0. consider_next_reg r r_env. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t20. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t5. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t2. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t3. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t4. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t1. by rewrite !fixpoint_interp1_eq.
      destruct (rmap !! r) eqn:Hr;rewrite Hr;[|by rewrite !fixpoint_interp1_eq].
      iDestruct (big_sepM_lookup with "Hregs_val") as "$";eauto.
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
        f_m (* malloc offset: needed by the seal_env, but not important for this spec *)
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


    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r_t0 ↦ᵣ wret
       ∗ r_env ↦ᵣ inr (RWX,d,d',d)
       ∗ r_t1 ↦ᵣ iw
       (* ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
       ∗ (∃ w, r_t2 ↦ᵣ w)
       ∗ (∃ w, r_t3 ↦ᵣ w)
       ∗ (∃ w, r_t4 ↦ᵣ w)
       ∗ (∃ w, r_t5 ↦ᵣ w)
       ∗ (∃ w, r_t20 ↦ᵣ w)
       (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
       ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a f_m)
       ∗ sealLL ι2 ll γ isIntervals
       (* token which states all non atomic invariants are closed *)
       ∗ na_own logrel_nais ⊤
       (* callback validity *)
       ∗ interp wret
       (* malloc: only required by the seal spec *)
       (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
       (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ inr (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)) *)
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (codefrag a_first imax)
       (* the remaining registers are all valid *)
       (* ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i) *)
       ∗ ▷ Ψ FailedV
       ∗ ▷ (∀ v, Ψ v -∗ Φ v)
       ∗ ▷ ( (∃ p b e a (z1 z2 : Z) w pbvals p' b' e' a', ⌜iw = inr (p,b,e,a) ∧ w = inr (p',b',e',a') ∧ (b,w) ∈ pbvals ∧ (z1 <= z2)%Z⌝
                ∗ prefLL γ pbvals
                ∗ b ↪ (z1,z2)
                ∗ PC ↦ᵣ updatePcPerm wret
                ∗ r_t1 ↦ᵣ inl z2
                ∗ r_t2 ↦ᵣ inl 0%Z
                ∗ r_t3 ↦ᵣ inl 0%Z
                ∗ r_t4 ↦ᵣ inl 0%Z
                ∗ r_t5 ↦ᵣ inl 0%Z
                ∗ r_t20 ↦ᵣ inl 0%Z
                ∗ r_env ↦ᵣ inl 0%Z
                ∗ r_t0 ↦ᵣ wret
                ∗ na_own logrel_nais ⊤)
               -∗ WP Seq (Instr Executable) {{ Ψ }} )
    ⊢
      WP Seq (Instr Executable) {{ Φ }}.
  Proof.
    iIntros (Hexec Hsub Hdisj Hdisj2 Hsidj3) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20
    & #Hseal_env & #HsealLL & Hown & #Hretval & #Hprog & Hfailed & HΨ & Hφ)".
    iMod (na_inv_acc with "Hprog Hown") as "(>Hcode & Hown & Hcls)";auto.

    (* extract the registers used by the program *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".
    iDestruct "Hr_t4" as (w4) "Hr_t4".
    iDestruct "Hr_t5" as (w5) "Hr_t5".
    iDestruct "Hr_t20" as (w20) "Hr_t20".

    iMod (na_inv_acc with "Hseal_env Hown") as "(>Henv & Hown & Hcls')";[solve_ndisj..|].
    iDestruct "Henv" as (d1 b1 e1 b2 e2 [Hd Hd']) "(Hd & Hd1 & % & % & % & (%&%) & Hunseal & Hseal & Hunsealseal_codefrag)".
    codefrag_facts "Hcode".
    assert (withinBounds (RWX, d, d', d) = true) as Hwb;[solve_addr|].
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
    iDestruct "Hres" as (p' b' e' a' b1' w pbvals [Heq [Hb Hbw] ]) "(#Hpref & Hr_t1 & Hr_env)". simplify_eq.
    iGo "Hcode".

    (* we must now extract from the sealLL invariant that w is indeed an interval element *)
    iMod (na_inv_acc with "HsealLL Hown") as "(Hw & Hown & Hcls'')";[auto|solve_ndisj|].
    iDestruct "Hw" as (hd) "(>Hll & Hawvals)".
    iDestruct "Hawvals" as (awvals) "(HisList & >Hexact & >Hintervals)".
    iDestruct (know_pref with "Hexact Hpref") as %Hpref.
    assert (∃ k, awvals !! k = Some (b', w)) as [k Hin].
    { apply elem_of_list_lookup in Hbw as [k Hk]. destruct Hpref;subst.
      exists k. by apply lookup_app_l_Some. }
    iDestruct "Hintervals" as "[Hintervals Hm]".
    iDestruct (big_sepL_lookup_acc with "Hintervals") as "[Hw Hacc]";[eauto|].
    iDestruct "Hw" as (a1 a2 a3 [Heq [Hincr Hincr'] ] z1 z2) "[Ha1 [Ha2 [%Hle #Hi]]]". simpl in Heq. rewrite Heq.

    iGo "Hcode". split;auto;solve_addr+Hincr Hincr'.
    iGo "Hcode".

    (* lets begin by closing all our invariants *)
    iMod ("Hcls''" with "[Hacc Ha1 Ha2 Hll HisList Hexact $Hown Hm]") as "Hown".
    { iNext. iExists _. iFrame. iExists _. iFrame. iApply "Hacc". iExists _,_,_. repeat iSplit;eauto. iExists _,_. iFrame "∗ #". auto. }

    iMod ("Hcls'" with "[Hunseal Hseal Hunsealseal_codefrag Hd Hd1 $Hown]") as "Hown".
    { iExists _,_,_,_,_. iFrame. iNext. eauto. }

    iMod ("Hcls" with "[$Hown $Hcode]") as "Hown".

    iApply (wp_wand _ _ _ (λ v, Ψ v) with "[-]").
    2: { iIntros (v) "Hφ". iRight. iFrame. }
    iApply "Hφ".
    iExists _,_,_,_,_,_,_. iFrame. iExists _,_,_,_,_. iFrame "#". eauto.
  Qed.

  Lemma imax_valid pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        d d' (* dynamically allocated seal/unseal environment *)
        a_first (* special adresses *)
        rmap (* registers *)
        ι0 ι1 ι2 γ (* invariant/gname names *)
        ll ll' (* seal env adresses *)
        f_m (* malloc offset: needed by the seal_env, but not important for this spec *)
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


    {{{ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,d,d',d)
      ∗ (∃ w, r_t20 ↦ᵣ w)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for the seal (must be an isInterval seal) and the seal/unseal pair environment *)
      ∗ na_inv logrel_nais ι0 (seal_env d d' ll ll' p b e a f_m)
      ∗ sealLL ι2 ll γ isIntervals
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* malloc: only required by the seal spec *)
      (* ∗ na_inv logrel_nais ι3 (malloc_inv b_m e_m) *)
      (* ∗ na_inv logrel_nais ι4 (pc_b ↦ₐ inr (RO, b_r, e_r, a_r) ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)) *)
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

    iDestruct (jmp_or_fail_spec with "Hretval") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm wret))).
    2: { iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ? ? ?) "HH".
         iDestruct "HH" as (? ? ?) "(_ & _ & HPC & _)".
         iApply "Hcont". iFrame "HPC". iIntros (Hcond). done. }
    iNext. iIntros "HH". iDestruct "HH" as (? ? ? ? ? ? ? ? ? ?) "HH".
    iDestruct "HH" as (? ? (?&?&?)) "(#Hpref & #Hi & HPC & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t20 & Hr_env & Hr_t0 & Hown)".
    iDestruct "Hcont" as (? ? ? ? Heq') "Hcont";simplify_eq.

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
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";[simplify_map_eq;apply not_elem_of_dom;rewrite Hdom;set_solver-|].
    rewrite -(insert_insert _  PC _ (inl 0%Z)).
    iDestruct ("Hcont" with "[$Hregs $Hown]") as "[_ $]". iClear "Hcont".
    iSplit.
    - iPureIntro. simpl. intros y. apply elem_of_gmap_dom.
      rewrite !dom_insert_L Hdom. pose proof (all_registers_s_correct y) as Hx. set_solver+Hx.
    - iIntros (r Hne). rewrite /RegLocate. consider_next_reg r PC. done.
      consider_next_reg r r_t0. consider_next_reg r r_env. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t20. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t5. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t2. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t3. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t4. by rewrite !fixpoint_interp1_eq.
      consider_next_reg r r_t1. by rewrite !fixpoint_interp1_eq.
      destruct (rmap !! r) eqn:Hr;rewrite Hr;[|by rewrite !fixpoint_interp1_eq].
      iDestruct (big_sepM_lookup with "Hregs_val") as "$";eauto.
  Qed.


End interval.
