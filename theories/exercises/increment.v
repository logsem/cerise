From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import malloc macros.
From cap_machine Require Import rules.
From cap_machine.proofmode Require Import tactics_helpers proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine.exercises Require Import subseg_buffer.
Open Scope Z_scope.


Ltac iHide0 irisH coqH :=
  let coqH := fresh coqH in
  match goal with
  | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
      set (coqH := prop)
  end.

Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
  iHide0 irisH coqH.


Section program_call.
  From cap_machine Require Import call callback.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.

  (* - r_t7 := r_cnt
     - r_t8 := r_pc
     - r_t9 := r_param *)

  Definition init_incr_instrs :=
    encodeInstrsW [
        Mov r_t7 0 ;
        Mov r_t9 0 ;
        Mov r_t8 PC ;
        Lea r_t8 2 ].

  Definition add_incr_instrs' : list Word :=
    restore_locals_instrs r_t2 (rev [r_t7 ; r_t8])
    ++ encodeInstrsW [
        Add r_t7 r_t7 1 ;
        Mov r_t9 r_t7 ;
        Jmp r_t8 ].

  Definition add_incr_instrs r_adv f_m :=
    call_instrs f_m (offset_to_cont_call [r_t9]) r_adv [r_t7 ; r_t8] [r_t9]
    ++ add_incr_instrs'.


  Definition prog_incr_instrs r_adv f_m : list Word :=
    init_incr_instrs ++ add_incr_instrs r_adv f_m.

  Definition prog_incr_code addrs_prog r_adv f_m :=
    ([∗ list] a_i;w ∈ addrs_prog;(prog_incr_instrs r_adv f_m), a_i ↦ₐ w)%I.

  Lemma init_incr_spec
        p_pc b_pc e_pc s_prog (* pc *)
        w7 w8 w9
        φ :

    let e_prog := (s_prog ^+ length init_incr_instrs)%a in

    (* Validity pc *)
    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_prog e_prog ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap p_pc b_pc e_pc s_prog
         ∗ r_t7 ↦ᵣ w7
         ∗ r_t8 ↦ᵣ w8
         ∗ r_t9 ↦ᵣ w9
         ∗ codefrag s_prog init_incr_instrs
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r_t7 ↦ᵣ WInt 0
               ∗ r_t8 ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r_t9 ↦ᵣ WInt 0
               ∗ codefrag s_prog init_incr_instrs
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intro e_prog ; subst e_prog.
    iIntros (Hpc_perm Hpc_bounds) "(HPC & Hr7 & Hr8 & Hr9 & Hprog & Cont)".
    codefrag_facts "Hprog".
    iGo "Hprog".
    iApply "Cont" ; iFrame.
  Qed.

  Definition length_call := 89%nat.
  Lemma length_call_instrs f_m :
    length
      (call_instrs f_m (offset_to_cont_call [r_t9]) r_t30 [r_t7; r_t8] [r_t9])
    = length_call.
    Proof.
      rewrite /call_instrs !length_app.
      set (l_fetch := length (fetch_instrs f_m)).
      set (l_clear := length (rclear_instrs (list_difference
                                               all_registers ([PC; r_t30; r_t30]
                                                                ++ [r_t9])))).
      simpl in l_fetch.
      subst l_fetch l_clear.
      rewrite rclear_length.
      rewrite list_difference_length ; auto ; simpl.
      apply all_registers_NoDup.
      repeat (apply NoDup_cons_2 ; first set_solver); apply NoDup_nil_2.
      apply all_registers_correct_sub.
      repeat (apply NoDup_cons_2 ; first set_solver)
      ; apply NoDup_nil_2.
    Qed.

    Lemma length_add_incr f_m :
      length (add_incr_instrs r_t30 f_m) = 96%nat.
    Proof.
      rewrite /add_incr_instrs.
      rewrite length_app.
      rewrite length_call_instrs.
      done.
    Qed.



  Lemma add_incr'_spec
        p_pc b_pc e_pc s_prog (* pc *)
        b_l e_l (* locals *)
        n7 w9 a_call
        φ :

    let e_prog := (s_prog ^+ length add_incr_instrs')%a in
    let rmap := ( <[r_t7 := WInt n7]> {[r_t8 := WCap p_pc b_pc e_pc a_call]}) in

    (* Validity pc *)
    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_prog e_prog ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap p_pc b_pc e_pc s_prog
         ∗ r_t2 ↦ᵣ WCap RWX b_l e_l e_l
         ∗ r_t9 ↦ᵣ w9
         ∗ ([∗ map] r_i↦_ ∈ rmap , ∃ w_i, r_i ↦ᵣ w_i)
         ∗ [[b_l,e_l]]↦ₐ[[ [WInt n7 ; (WCap p_pc b_pc e_pc a_call)] ]]
         ∗ codefrag s_prog add_incr_instrs'
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_call
               ∗ r_t7 ↦ᵣ WInt (n7+1)
               ∗ r_t8 ↦ᵣ WCap p_pc b_pc e_pc a_call
               ∗ r_t9 ↦ᵣ WInt (n7+1)
               ∗ codefrag s_prog add_incr_instrs'
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intro e_prog  ; subst e_prog; simpl.
    iIntros (Hpc_perm Hpc_bounds)
            "(HPC & Hr2 & Hr9 & Hrmap & Hlocals & Hprog & Post)".
    iHide "Post" as Post.

    focus_block_0 "Hprog" as "Hprog" "Hcont".
    rewrite {1}/codefrag {2}/region_pointsto.
    iHide "Hcont" as Hcont.
    rewrite -/(restore_locals _ _ _).
    iDestruct (big_sepL2_length with "Hlocals") as %Hlength_locals
    ; rewrite /= finz_seq_between_length in Hlength_locals.
    iApply (restore_locals_spec _ _ _ _ _ _ _ _ _ _
                                (s_prog ^+ length (restore_locals_instrs r_t2 [r_t7; r_t8]))%a
             with "[- $HPC $Hr2 $Hrmap $Hprog $Hlocals]").
    { split ; auto. split ; solve_addr. }
    { apply contiguous_between_region_addrs; solve_addr. }
    { auto. }
    { simpl ; lia. }
    { reflexivity. }
    { simpl.
      rewrite map_to_list_insert ; last by simplify_map_eq.
      rewrite map_to_list_singleton.
      reflexivity.
    }
    { reflexivity. }
    iNext ; iIntros "(HPC & Hr2 & Hrmap & Hlocals & Hprog)" ; simpl.
    iAssert (codefrag s_prog (restore_locals_instrs r_t2 [r_t8; r_t7]))
      with "Hprog" as "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 1%nat "Hprog" as a_mid Ha_mid "Hprog" "Hcont".
    clear Post ;
    iHide "Post" as Post; iHide "Hcont" as Hcont.
    extract_register r_t7 with "Hrmap" as "[Hr7 Hrmap]".
    extract_register r_t8 with "Hrmap" as "[Hr8 Hrmap]".
    iClear "Hrmap".
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    inversion Hpc_perm; subst.
    all: unfocus_block "Hprog" "Hcont" as "Hprog".
    all: iApply "Post" ; iFrame.
  Qed.


  Definition incrN : namespace := nroot .@ "incrN".
  Definition incrN_link : namespace := incrN .@ "link".
  Definition incrN_act : namespace := incrN .@ "act".
  Definition incrN_locals : namespace := incrN .@ "locals".
  Definition incrN_prog : namespace := incrN .@ "prog".


  Definition locals_inv w7 w8 : iProp Σ :=
    ∃ b_local e_local,
      ([[b_local,e_local]]↦ₐ[[ [w7; w8] ]])%I.

  Definition act_inv  pc_p pc_b pc_e a_end : iProp Σ :=
    ∃ b_act e_act b_local e_local,
      ([[b_act,e_act]]↦ₐ[[[WInt hw_1;
                           WInt hw_2;
                           WInt hw_3;
                           WInt hw_4;
                           WInt hw_5;
                           WCap RWX b_local e_local e_local;
                           WCap pc_p pc_b pc_e a_end] ]])%I.

    Definition link_inv table_addr b_link e_link a_link
               malloc_entry b_m e_m : iProp Σ :=
      (table_addr ↦ₐ WCap RO b_link e_link a_link
       ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m)%I.


    Ltac solve_addr' :=
      repeat
        ( match goal with
          | h: contiguous_between _ _ _ |- _ =>
              apply contiguous_between_bounds in h
          end)
      ; solve_addr.

  Lemma malloc_incrN mallocN :
    (up_close (B:=coPset)mallocN ⊆ ⊤ ∖ ↑incrN) ->
    (up_close (B:=coPset)mallocN ⊆ ⊤ ∖ ↑incrN_prog ∖ ↑incrN_link).
  Proof.
    intros.
    assert (up_close (B:=coPset)incrN_prog ⊆ ↑incrN) by apply nclose_subseteq.
    assert (up_close (B:=coPset)incrN_link ⊆ ↑incrN) by apply nclose_subseteq.
    set_solver.
  Qed.

  Lemma add_incr_spec
        (* call *) n7
        (* remaining registers *) (rmap : gmap RegName Word)
        (* pc *) a pc_p pc_b pc_e a_first a_last
        (* malloc *) f_m b_m e_m mallocN
        (* linking *) b_link a_link e_link malloc_entry :

    (* Validity pc *)
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last →
    (* LT *)
    withinBounds b_link e_link malloc_entry = true →
    (a_link + f_m)%a = Some malloc_entry →
    (up_close (B:=coPset)mallocN ⊆ ⊤ ∖ ↑incrN) ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap pc_p pc_b pc_e a_first
         ∗ (∃ w0, r_t0 ↦ᵣ w0 ∗ interp w0)
         ∗ r_t7 ↦ᵣ WInt n7
         ∗ r_t8 ↦ᵣ WCap pc_p pc_b pc_e a_first
         ∗ r_t9 ↦ᵣ WInt n7
         ∗ (∃ wadv, r_t30 ↦ᵣ wadv ∗ interp wadv)
         ∗ (([∗ map] r_i↦w_i ∈ rmap , r_i ↦ᵣ w_i) ∗ ⌜ dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t30 ; r_t7 ; r_t8 ; r_t9]} ⌝)
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
         ∗ na_inv logrel_nais incrN_link
                  (link_inv pc_b b_link e_link a_link malloc_entry b_m e_m)
         ∗ na_inv logrel_nais incrN_prog
                  ([∗ list] a_i;w ∈ a;(add_incr_instrs r_t30 f_m), a_i ↦ₐ w)%I
         -∗ WP Seq (Instr Executable) {{λ v,
                 (⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_pointsto r ∗ na_own logrel_nais ⊤)%I
                 ∨ ⌜v = FailedV⌝ }}))%I.
  Proof with (try solve_addr').
    iIntros
      (Hpc_perm Hpc_bounds Hcont Hwb Hlink Hnamespace)
      "(HPC & Hr0 & Hr7 & Hr8 & Hr9 & Hr30 & Hrmap & Hna
        & #Hmalloc_inv & #Hlink_inv & #Hprog_inv)".
    iHide "Hprog_inv" as Hprog_inv.

    iLöb as "IH" forall ( n7 rmap ).
    iHide "IH" as IH.
    iDestruct "Hr0" as (w0) "[Hr0 #Hinterp_w0]"
    ; iDestruct "Hr30" as (wadv) "[Hr30 #Hinterp_adv]"
    ; iDestruct "Hrmap" as "[Hrmap %Hdom]".

    iDestruct (jmp_to_unknown with "Hinterp_adv") as "Cont".
    iHide "Cont" as cont.


    iMod (na_inv_acc with "Hprog_inv Hna") as "(>Hprog & Hna & Hcls)" ; auto.
    iMod (na_inv_acc with "Hlink_inv Hna") as
      "(>[Hpcb Hmalloc_entry] & Hna & Hcls') "; [auto|solve_ndisj|].
    iHide "Hcls" as Hcls; iHide "Hcls'" as Hcls'.

    (* 1 - prepare the ressources for the call specification *)
    (* We split the program in 2 parts: the call and the callback *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    iDestruct (contiguous_between_program_split with "Hprog") as
      (call_addrs add_incr_addrs a_add) "(Hcall_prog & Hadd_prog & #Hcont1)"
    ;[apply Hcont|]
    ;iDestruct "Hcont1" as %(Hcont_call & Hcont_prog & Heqapp1 & Ha_prog).
    iDestruct (big_sepL2_length with "Hcall_prog") as %Hlength_call.

    iAssert ( call _ f_m r_t30 [r_t7 ; r_t8] [r_t9])
      with "Hcall_prog"
      as "Hcall".
    set (w7 := WInt n7).
    set (w8 := WCap pc_p pc_b pc_e a_first).
    set (rmap_call' :=  <[r_t7:=w7]> (<[r_t8 := w8 ]> rmap)).
    set (mlocals := (@list_to_map _ _ (@gmap RegName reg_eq_dec reg_countable
                                             Word) _ _ [ (r_t7, w7) ; (r_t8, w8) ])).
    iApply (call_spec
              r_t30 mlocals ({[r_t9 := w7]})
              wadv _ rmap_call'
              _ _ _ _ _ a_add
             with "[- $HPC $Hna $Hr30 $Hrmap $Hpcb $Hmalloc_entry $Hmalloc_inv]"
           ) ; simpl ; eauto.
    { split; auto... }
    { rewrite map_to_list_insert ; last by simplify_map_eq.
      simpl ; lia. }
    1,3: ( rewrite Hdom; set_solver+ ).
    {
      subst rmap_call'.
      rewrite dom_singleton_L.
      rewrite <- !difference_difference_l_L.
      rewrite !dom_insert_L Hdom.
      replace (all_registers_s ∖ {[PC; r_t0; r_t30; r_t7; r_t8; r_t9]})
        with (all_registers_s ∖ {[PC]} ∖ {[r_t0]} ∖ {[r_t30]}  ∖ {[r_t9]} ∖ {[r_t8]} ∖ {[r_t7]})
             by (rewrite <- !difference_difference_l_L ; set_solver+).
      replace
        ( {[r_t7]}
            ∪ ({[r_t8]}
                 ∪ (all_registers_s ∖ {[PC]} ∖ {[r_t0]} ∖ {[r_t30]}  ∖ {[r_t9]} ∖
                                    {[r_t8]} ∖ {[r_t7]})))
        with (all_registers_s ∖ {[PC]} ∖ {[r_t0]} ∖ {[r_t30]}  ∖ {[r_t9]})
      ; first reflexivity.
      match goal with
      |h: _ |- ?x = _ => set (rmaps := x)
      end.
      replace ({[r_t7]} ∪ ({[r_t8]} ∪ rmaps ∖ {[r_t8]} ∖ {[r_t7]}))
        with
        ({[r_t7 ; r_t8]} ∪ (rmaps ∖ {[r_t7 ; r_t8]})) by set_solver+.
      rewrite -union_difference_L; set_solver+.
    }
    { apply malloc_incrN ; solve_ndisj. }

    iSplitL "Hcall".
    { iNext.
      rewrite !map_to_list_singleton /=. admit.
    }
    iSplitL "Hr9"; first (iApply big_sepM_singleton; iFrame).
    iSplitL "Hr0"; first (iNext ; iExists _ ; iFrame).
    iSplitL "Hr7 Hr8".
    { iNext. iFrame.
      iApply (big_sepM_insert with "[-]") ; first by simplify_map_eq.
      simpl. iFrame.
      (iApply big_sepM_singleton; iFrame).
    }
    iNext.
    clear IH ; iHide "IH" as IH.
    iIntros "H" ; iDestruct "H" as
      (b_act e_act b_local e_local a_end_call)
        "( %Hnext & HPC & Hrmap & Hr9 & Hpcb & Haentry & Hr30 & Hr0 & Hact & Hlocals & Hcall & Hna )".


    (* Cleaning *)
    iMod ("Hcls'" with "[$Hna $Haentry $Hpcb]") as "Hna".
    iHide "Hact" as Hact.
    clear cont ; iHide "Cont" as cont.
    subst rmap_call'.
    replace (map_to_list mlocals)
      with [(r_t7,w7) ; (r_t8,w8)] ; [simpl|].
    2:{ clear. admit. }
    replace ((map_to_list {[r_t9 := w7]}).*1)
      with [r_t9] by (by rewrite map_to_list_singleton /=).
    iDestruct (big_sepM_singleton (fun r w => r ↦ᵣ w)%I r_t9 w7 with "Hr9") as
      "Hr9".

    (* Re -insert the registers into the map *)
    iDestruct (big_sepM_to_create_gmap_default _ _ (λ k i, k ↦ᵣ i)%I (WInt 0%Z) with "Hrmap")  as "Hrmap";[apply Permutation_refl|reflexivity|].
    (* r0 *)
    iDestruct (big_sepM_insert with "[$Hrmap $Hr0]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_insert_L Hdom.
      clear; set_solver.
    }
    (* r30 *)
    iDestruct (big_sepM_insert with "[$Hrmap $Hr30]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_insert_L Hdom.
      clear; set_solver. }
    (* r7 *)
    iDestruct (big_sepM_insert with "[$Hrmap $Hr9]") as "Hrmap".
    { apply not_elem_of_dom.
      rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_insert_L Hdom.
      clear; set_solver. }
    set rmap2 := (<[r_t9:=w7]> _).

    (* we are now ready to call the unknown adversary *)
    (* we first need to prepare the invariants needed *)
    iMod (na_inv_alloc logrel_nais _ incrN_act with "Hact") as "#Hact_inv".
    iMod (na_inv_alloc logrel_nais _ incrN_locals with "Hlocals") as "#Hlocals_inv".
    iMod ("Hcls" with "[Hcall Hadd_prog $Hna]") as "Hna".
    { iNext.
      rewrite /call.
      iDestruct (big_sepL2_app with "Hcall Hadd_prog") as "Hprog".
      rewrite <- Heqapp1.
      by rewrite /add_incr_instrs. }

    (* Apply the continuation - ie. jump to the adversary code using
       the fact that it is safe to execute *)
    iSpecialize ("Cont" $! rmap2).
    iApply "Cont".
    { iPureIntro.
      subst rmap2.
      rewrite !dom_insert_L create_gmap_default_dom list_to_set_map_to_list.
      rewrite !dom_insert_L Hdom.
      rewrite !singleton_union_difference_L. set_solver+. }
    iFrame.
    subst rmap2.
    iApply big_sepM_sep. iFrame.
    iApply big_sepM_insert_2 ; first (subst w7 ; iApply interp_int).
    iApply big_sepM_insert_2 ; first iFrame "#".
    iApply big_sepM_insert_2 ; cycle 1.
    (* The remaining registers contains WInt*)
    { iApply big_sepM_intuitionistically_forall. iIntros "!>" (r ?).
      (set rmap' := <[r_t7:=w7]> _ ).
      destruct ((create_gmap_default (map_to_list rmap').*1 (WInt 0%Z : Word)) !! r) eqn:Hsome.
      apply create_gmap_default_lookup_is_Some in Hsome as [Hsome ->]. rewrite !fixpoint_interp1_eq.
      iIntros (?); simplify_eq; done. iIntros (?); done. }

    (* The activation code is safe to share - ie. safe to execute *)
    { cbn beta. rewrite !fixpoint_interp1_eq.
      iIntros (r). iNext; iModIntro.
      iIntros "([%Hrmap_full #Hrmap_safe] & Hrmap & Hna)".
      iClear "Cont".
      rewrite /interp_conf {1}/registers_pointsto.

      (* get the registers we need *)
      extract_register PC with "Hrmap" as "[HPC Hrmap]".
      some_register r_t1 with r as w1 Hw1
      ; extract_register r_t1 with "Hrmap" as "[Hr1 Hrmap]".
      some_register r_t2 with r as w2 Hw2
      ; extract_register r_t2 with "Hrmap" as "[Hr2 Hrmap]".
      some_register r_t7 with r as w7 Hw7
      ; extract_register r_t7 with "Hrmap" as "[Hr7 Hrmap]".
      some_register r_t8 with r as w8 Hw8
      ; extract_register r_t8 with "Hrmap" as "[Hr8 Hrmap]".
      some_register r_t9 with r as w9 Hw9
      ; extract_register r_t9 with "Hrmap" as "[Hr9 Hrmap]".
      some_register r_t0 with r as w0 Hw0
      ; extract_register r_t0 with "Hrmap" as "[Hr0 Hrmap]".
      some_register r_t30 with r as w30 Hw30
      ; extract_register r_t30 with "Hrmap" as "[Hr30 Hrmap]".

      (* 1 - step through the activation record *)
      iMod (na_inv_acc with "Hprog_inv Hna") as "[>Hprog [Hna Hcls] ]"
      ;[solve_ndisj|solve_ndisj|].
      clear Hcls ; iHide "Hcls" as Hcls.
      iMod (na_inv_acc with "Hact_inv Hna") as "[Hact [Hna Hcls'] ]";[solve_ndisj|solve_ndisj|].
      iApply (scall_epilogue_spec with "[- $HPC $Hact $Hr1 $Hr2]") ;[|apply Hnext|].
      { split;auto. }
      iNext; iIntros "(HPC & Hr1 & Hr2 & Hact)".
      iMod ("Hcls'" with "[$Hact $Hna]") as "Hna".
      iDestruct "Hr1" as (w1') "Hr1".

      (* 1 - prepare ressurces for restore locals *)
      iDestruct (contiguous_between_program_split with "Hprog") as
        (call_addrs' add_incr_addrs' a_add') "(Hcall_prog' & Hadd_prog' & #Hcont1)"
      ;[apply Hcont|]
      ;iDestruct "Hcont1" as %(Hcont_call' & Hcont_prog' & Heqapp1' & Ha_prog').
      iDestruct (big_sepL2_length with "Hcall_prog'") as %Hlength_call'.
      assert (a_add = a_add') as -> ; [|clear Hlength_call'].
      { rewrite Heqapp1 in Heqapp1'.
        apply app_inj_1 in Heqapp1' as [ -> -> ].
        rewrite Ha_prog in Ha_prog'.
        by injection Ha_prog'.
        by rewrite <- Hlength_call in Hlength_call'.
      }

      rewrite /add_incr_instrs'.
      iMod (na_inv_acc with "Hlocals_inv Hna") as "[>Hlocals [Hna Hcls'] ]"
      ;[solve_ndisj|solve_ndisj|].
      iHide "Hinterp_w0" as Hinterp_w0.
      iHide "Hinterp_adv" as Hinterp_adv.
      iHide "Hrmap_safe" as Hrmap_safe.
      clear Hcls' ; iHide "Hcls'" as Hcls'.

      (* Extract instructions *)
      iDestruct (contiguous_between_program_split with "Hadd_prog'") as
        (restore_addrs incr_addrs' a_incr) "(Hrestore_prog & Hincr_prog & #Hcont)"
      ;[apply Hcont_prog'|]
      ;iDestruct "Hcont" as %(Hcont_restore & Hcont_incr & Heqapp2 & Ha_incr).
      iDestruct (big_sepL2_length with "Hlocals") as %Hlength_locals
      ; rewrite finz_seq_between_length /= in Hlength_locals.

      iApply (restore_locals_spec _ _ ( <[r_t7 := w7 ]> {[ r_t8 := w8]} )
                                  _ _ _ _ _ _ _ a_incr
               with "[- $HPC $Hr2 $Hlocals $Hrestore_prog]").
      { split ; try eauto... }
      { eassumption. }
      { auto. }
      { simpl ; lia. }
      { auto. }
      { rewrite /= map_to_list_insert ; last by simplify_map_eq.
        by rewrite map_to_list_singleton. }
      { simpl ; lia. }
      iSplitL "Hr7 Hr8".
      { iNext.
        iApply (big_sepM_insert_2 with "[Hr7]"); first by iExists _.
        iApply (big_sepM_insert_2 with "[Hr8]"); first by iExists _.
        done.
      }
      iNext ; iIntros "(HPC & Hr2 & Hregs_locals & Hlocals & Hrestore_prog)".
      extract_register r_t7 with "Hregs_locals" as "[Hr7 Hregs_locals]".
      extract_register r_t8 with "Hregs_locals" as "[Hr8 _]".
      iHide "Hrmap" as Hrmap.
      iHide "Hcall_prog'" as Hcall_prog.

      iDestruct (big_sepL2_length with "Hincr_prog") as %Hlength_incr.
      destruct incr_addrs';[inversion Hlength_incr|]. apply contiguous_between_cons_inv_first in Hcont_incr as Heq;subst f.
      destruct incr_addrs' as [|a_incr2 incr_addrs'];[inversion Hlength_incr|].
      destruct incr_addrs' as [|a_incr3 incr_addrs'];[inversion Hlength_incr|].
      destruct incr_addrs' as [|? ?];inversion Hlength_incr.

      (* add rt7 1 *)
      iDestruct "Hincr_prog" as "(Hincr_prog1 & Hincr_prog2 & Hincr_prog3 & _)".
      wp_instr.
      iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hincr_prog1 $Hr7]");
        [apply decode_encode_instrW_inv
        |auto
        |iContiguous_next Hcont_incr 0%nat
        |..].
      { eapply isCorrectPC_contiguous_range ; eauto. split ; solve_addr.
        cbn; solve [ repeat constructor ].
      }
      iEpilogue "(HPC & Hincr_prog1 & Hr7)".

      (* mov rt9 rt7 *)
      wp_instr.
      iApply (wp_move_success_reg with "[$HPC $Hincr_prog2 $Hr9 $Hr7]");
        [apply decode_encode_instrW_inv
        | auto
        |iContiguous_next Hcont_incr 1%nat
        |..].
      { eapply isCorrectPC_contiguous_range ; eauto. split ; solve_addr.
        cbn; solve [ repeat constructor ].
      }
      iEpilogue "(HPC & Hincr_prog2 & Hr9 & Hr7)".

      (* jmp r8 *)
      wp_instr.
      iApply (wp_jmp_success with "[$HPC $Hincr_prog3 $Hr8]");
        [apply decode_encode_instrW_inv
        | auto
        |..].
      { eapply isCorrectPC_contiguous_range ; eauto. split ; solve_addr.
        cbn; solve [ repeat constructor ].
      }
       iEpilogue "(HPC & Hincr_prog3 & Hr8)".
      iCombine "Hincr_prog1" "Hincr_prog2" as "Hprog_done".
      iCombine "Hprog_done" "Hincr_prog3" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E ; last by apply ExecPCPerm_not_E.

      subst Hrmap.
      insert_register r_t1 with "[Hr1 $Hrmap]" as "Hrmap".
      insert_register r_t2 with "[Hr2 $Hrmap]" as "Hrmap".

      (* We have jumped at the call instruction, we are at the same point
         as the beginning - use the induction hypothesis *)
      iApply (wp_wand with "[-]").
      iMod ("Hcls'" with "[$Hlocals $Hna]") as "Hna".
      iMod ("Hcls" with "[Hcall_prog' Hrestore_prog Hprog_done $Hna]") as "Hna".
      { iNext.
        rewrite /add_incr_instrs Heqapp1'.
        iApply (big_sepL2_app with "[$Hcall_prog']") ; simpl.
        rewrite /add_incr_instrs' Heqapp2.
        iApply (big_sepL2_app with "[$Hrestore_prog]") ; simpl.
        iDestruct "Hprog_done" as "(?&?&?)" ; iFrame. }

      subst IH.
      iApply ("IH" with
               "[$HPC] [Hr0] [$Hr7] [$Hr8] [$Hr9] [Hr30] [Hrmap] [$Hna]").
      { iExists w5 ; iFrame. iApply "Hrmap_safe" ; eauto ; eauto. }
      { iExists _ ; iFrame. iApply "Hrmap_safe" ; eauto ; eauto. }
      { iClear "IH"; iFrame. iPureIntro.
        apply regmap_full_dom in Hrmap_full.
        rewrite !dom_delete_L !dom_insert_L dom_delete_L Hrmap_full.
        set_solver+. }
      { iIntros (v) "[H|->]" ; auto. iIntros "%contra" ; done. }.
      (* TODO: it remains the technical stuff about the  map_to_list *)
  Admitted.

  Lemma prog_incr_code_spec
        (* remaining registers *) (rmap : gmap RegName Word)
        (* pc *) a pc_p pc_b pc_e a_first a_last
        (* malloc *) f_m b_m e_m mallocN
        (* linking *) b_link a_link e_link malloc_entry :

    (* Validity pc *)
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last →
    (* LT *)
    withinBounds b_link e_link malloc_entry = true →
    (a_link + f_m)%a = Some malloc_entry →

    (up_close (B:=coPset)mallocN ⊆ ⊤ ∖ ↑incrN) ->

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC ]} ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap pc_p pc_b pc_e a_first
         ∗ ([∗ map] r_i↦w_i ∈ rmap , r_i ↦ᵣ w_i ∗ interp w_i)
         ∗ prog_incr_code a r_t30 f_m
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
         -∗ WP Seq (Instr Executable) {{λ v,
                 (⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_pointsto r ∗ na_own logrel_nais ⊤)%I
                 ∨ ⌜v = FailedV⌝ }}))%I.
  Proof.
    iIntros (Hpc_perm Hpc_bounds Hcont Hwb Hlink Hna Hdom)
            "(HPC & Hrmap & Hprog & Hpcb & Hmalloc_entry & Hna & #Hinv_malloc)".
    rewrite /prog_incr_code /prog_incr_instrs.

    (* Split the program to get each parts *)
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iDestruct (contiguous_between_program_split with "Hprog") as
      (init_addrs add_addrs a_add) "(Hinit_prog & Hadd_prog & #Hcont)"
    ;[apply Hcont|]
    ;iDestruct "Hcont" as %(Hcont_init & Hcont_add & Heqapp1 & Ha_add).
    iDestruct (big_sepL2_length with "Hinit_prog") as %Hlength_init.

    (* 1 - prepare the ressources for init_spec *)
    (* 1.1 - extract the registers from the map (r7 r8 r9) *)
    extract_register r_t7 with "Hrmap" as ( w7 Hw7 ) "[[Hr7 _] Hrmap]".
    extract_register r_t8 with "Hrmap" as ( w8 Hw8 ) "[[Hr8 _] Hrmap]".
    extract_register r_t9 with "Hrmap" as ( w9 Hw9 ) "[[Hr9 _] Hrmap]".
    (* 1.2 - transform Hinit_prog into a codefrag predicate *)
    iAssert (codefrag a_first init_incr_instrs)
      with "[Hinit_prog]"
      as "Hinit_prog".
    {clear - Hcont_init Heqapp1 Hlength_init Ha_add.
      rewrite /codefrag /region_pointsto /=.
      replace init_addrs with (finz.seq_between a_first (a_first ^+ 4%nat)%a).
      done.
      apply region_addrs_of_contiguous_between in Hcont_init as ->.
      replace a_add with (a_first ^+ 4%nat)%a by solve_addr.
      done.
    }
    (* 1.3 - apply the spec *)
    iApply (init_incr_spec with "[- $HPC $Hr7 $Hr8 $Hr9 $Hinit_prog]")
    ; eauto
    ;[solve_addr'|].
    iNext ; iIntros "(HPC & Hr7 & Hr8 & Hr9 & Hinit_prog)".
    replace (a_first ^+ length init_incr_instrs)%a with a_add by solve_addr.

    (* 2 - prepare the ressources for add_incr_spec *)
    (* 2.1 - extract registers *)
    extract_register r_t30 with "Hrmap" as ( wadv Hwadv ) "[[Hr30 #Hinterp_adv] Hrmap]".
    extract_register r_t0 with "Hrmap" as ( w0 Hw0 ) "[[Hr0 #Hinterp_w0] Hrmap]".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hrmap_interp]".
    (* 2.2 - prepare the invariants *)
    iCombine "Hpcb" "Hmalloc_entry" as "Hlink".
    iMod (na_inv_alloc logrel_nais _ incrN_link with "Hlink") as "#Hinv_link".
    iMod (na_inv_alloc logrel_nais _ incrN_prog with "Hadd_prog") as "#Hinv_prog".
    (* 2.3 - apply the spec *)
    iApply (add_incr_spec with "[- $HPC $Hr7 $Hr8 $Hr9 $Hrmap]")
    ; eauto
    ;[solve_addr'|].
    iSplitL "Hr0" ; first iExists _ ; iFrame ; iFrame "#".
    iSplitL "Hr30" ; first iExists _ ; iFrame ; iFrame "#".
    iPureIntro; rewrite !dom_delete_L Hdom ; set_solver+.
  Qed.



  (* Lemma prog_incr_code_spec *)
  (*       (* remaining registers *) (rmap : gmap RegName Word) *)
  (*       (* pc *) a pc_p pc_b pc_e a_first a_last *)
  (*       (* malloc *) f_m b_m e_m mallocN *)
  (*       (* linking *) b_link a_link e_link malloc_entry : *)



  (* Lemma prog_incr_code_safe_to_share *)
  (*       pc_b pc_e a a_first a_last *)
  (*       f_m b_m e_m mallocN *)
  (*       b_link e_link a_link malloc_entry : *)

  (*   (* Validity pc *) *)
  (*   SubBounds pc_b pc_e a_first a_last -> *)
  (*   contiguous_between a a_first a_last → *)
  (*   (* LT *) *)
  (*   withinBounds b_link e_link malloc_entry = true → *)
  (*   (a_link + f_m)%a = Some malloc_entry → *)

  (*   (up_close (B:=coPset)mallocN ⊆ ⊤ ∖ ↑incrN) -> *)

  (*   ⊢ na_inv logrel_nais incrN_prog (prog_incr_code a r_t30 f_m) *)
  (*     ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m) *)
  (*     ∗ na_inv logrel_nais incrN_link *)
  (*             (link_inv pc_b b_link e_link a_link malloc_entry b_m e_m) *)
  (*   -∗ interp (WCap E pc_b pc_e a_first). *)
  (* Proof. *)
  (*   iIntros (Hpc_bounds Hcont Hwb HlinkE Hna) *)
  (*         "(#Hinv_prog& #Hinv_malloc& #Hinv_link)". *)
  (*   rewrite fixpoint_interp1_eq ; simpl. *)
  (*   iIntros (r). iNext; iModIntro. *)
  (*   iIntros "([%Hrmap_full #Hrmap_safe] & Hrmap & Hna)". *)
  (*   rewrite /interp_conf {1}/registers_pointsto. *)

  (*   extract_register PC with "Hrmap" as "[HPC Hrmap]". *)
  (*   iApply (wp_wand with "[-]"). *)
  (*   - iApply (prog_incr_code_spec with "[- $HPC]") *)
  (*     ; try eauto *)
  (*     ; try apply ExecPCPerm_RX. *)
