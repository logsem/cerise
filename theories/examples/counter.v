From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers macros fundamental.

Section counter.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* -------------------------------- LTACS -------------------------------------- *)
  
  (* Tactic for destructing a list into elements *)
  Ltac destruct_list l :=
    match goal with
    | H : strings.length l = _ |- _ =>
      let a := fresh "a" in
      let l' := fresh "l" in
      destruct l as [|a l']; [inversion H|];
      repeat (let a' := fresh "a" in
              destruct l' as [|a' l'];[by inversion H|]);
      destruct l'; [|by inversion H]
    end.

  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
    end.

  Ltac iPrologue prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  (* ----------------------------------------------------------------------------- *)
  (* TODO: move to addr_reg_sample *)
  Definition lt_r_z r1 r2 z := encodeInstrW (Lt r1 (inr r2) (inl z)).
  

  Definition incr_instrs :=
    [load_r r_t1 r_env;
    add_r_z r_t1 r_t1 1;
    store_r r_env r_t1;
    move_z r_env 0;
    jmp r_t0]. 

  Definition read_instrs f_a :=
    [load_r r_t1 r_env;
    lt_r_z r_t2 r_t1 0] ++
    assert_r_z_instrs f_a r_t1 0 ++
    [move_z r_env 0;
    jmp r_t0]. 

  Definition reset_instrs :=
    [store_z r_env 0;
    move_z r_env 0;
    jmp r_t0].

  Definition incr a :=
    ([∗ list] a_i;w ∈ a;incr_instrs, a_i ↦ₐ w)%I.
  Definition read a f_a :=
    ([∗ list] a_i;w ∈ a;read_instrs f_a, a_i ↦ₐ w)%I. 
  Definition reset a :=
    ([∗ list] a_i;w ∈ a;reset_instrs, a_i ↦ₐ w)%I. 

  Definition pos_word (w : Word) : iProp Σ :=
    (match w with
    | inl z => ⌜(0 < z)%Z⌝
    | inr _ => False
    end)%I. 
  Definition counter_inv d : iProp Σ :=
    (∃ w, d ↦ₐ w ∗ pos_word w)%I.
  
  Instance pos_word_Timeless : Timeless (pos_word w).
  Proof. intros d. destruct d; apply _. Qed. 
  Instance pos_word_Persistent : Persistent (pos_word w).
  Proof. intros w. destruct w; apply _. Qed.


  (* ----------------------------------- INCR -------------------------------------- *)
  
  Lemma incr_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        incr_addrs (* program addresses *)
        d d' (* dynamically allocated memory given by preamble *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between incr_addrs a_first a_last ->
    
    (* Linking table assumptions *)
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption for the counter *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_t0;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->
    
    {{{ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (counter_inv d))
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (incr incr_addrs)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ inr (RO,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap)
      (* the remaining registers are all valid *)
      ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i)
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hlink Hd Hdom Hclose φ) "(HPC & Hr_t0 & Hr_env & Hregs & Hinv & Hown & #Hcallback & #Hincr & #Hlink & #Hregs_val) Hφ". 
    iDestruct "Hinv" as (ι) "#Hinv".
    iMod (na_inv_open with "Hincr Hown") as "(>Hprog & Hown & Hcls)";auto.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct_list incr_addrs.
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a. 
    (* Get a general purpose register *)
    assert (is_Some (rmap !! r_t1)) as [w1 Hrt1].
    { apply elem_of_gmap_dom. rewrite Hdom. apply elem_of_difference.
      split;[apply all_registers_s_correct|clear;set_solver]. }
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[eauto|]. 
    (* load r_t1 r_env *)
    iPrologue "Hprog". rewrite /counter_inv. 
    iInv ι as (w) "[>Hd >#Hcond]" "Hcls'".
    iAssert (⌜(d =? a_first)%a = false⌝)%I as %Hfalse.
    { destruct (d =? a_first)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq as ->. iDestruct (mapsto_valid_2 with "Hi Hd") as %?. done. }
    iApply (wp_load_success with "[$HPC $Hi $Hr_t1 $Hr_env Hd]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 0|..]. 
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
    { rewrite Hfalse. iFrame. }
    rewrite Hfalse. 
    iNext. iIntros "(HPC & Hr_t1 & Ha_first & Hr_env & Hd)".
    iMod ("Hcls'" with "[Hd]") as "_". 
    { iNext. iExists w. iFrame "∗ #". }
    iModIntro. iApply wp_pure_step_later;auto;iNext.
    (* add r_t1 r_t1 1 *)
    destruct w;[|done]. 
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|]. 
    iEpilogue "(HPC & Hi & Hr_t1) /=". iCombine "Hi Ha_first" as "Hprog_done". 
    (* store r_env r_t1 *)
    iPrologue "Hprog".
    iInv ι as (w) "[>Hd _]" "Hcls'". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_env $Hd]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|..]. 
    { split;auto. simpl. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_t1 & Hr_env & Hd)".
    iMod ("Hcls'" with "[Hd]") as "_". 
    { iNext. iExists (inl (z + 1)%Z). iFrame. iDestruct "Hcond" as %Hcond. iPureIntro. revert Hcond;clear;lia. }
    iModIntro. iApply wp_pure_step_later;auto;iNext. iCombine "Hi Hprog_done" as "Hprog_done". 
    (* move r_env 0 *)
    iPrologue "Hprog". 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|]. 
    iEpilogue "(HPC & Hi & Hr_env)". iCombine "Hi Hprog_done" as "Hprog_done".
    (* jmp r_t0 *)
    iPrologue "Hprog". 
    apply (contiguous_between_last _ _ _ a3) in Hcont as Hlast;auto. 
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|]. 
    iDestruct (jmp_or_fail_spec with "Hcallback") as "Hcallback_now". 
    (* close program invariant *)
    
    (* reassemble registers *)
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|]. 
    iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne;auto. rewrite !lookup_delete_ne;auto. apply elem_of_gmap_dom_none. rewrite Hdom. clear; set_solver. }
    (* now we are ready to apply the jump or fail pattern *)
    destruct (decide (isCorrectPC (updatePcPerm wret))). 
    - iDestruct "Hcallback_now" as (p b e a Heq) "Hcallback'". 
      simplify_eq.
      iEpilogue "(HPC & Hi & Hr_t0)".
      iMod ("Hcls" with "[Hprog_done Hi $Hown]") as "Hown".
      { iNext. iFrame. iDestruct "Hprog_done" as "($&$&$&$&$)". done. }
      iDestruct (big_sepM_insert _ _ r_t0 with "[$Hregs $Hr_t0]") as "Hregs".
      { rewrite !lookup_insert_ne;auto. rewrite !lookup_delete_ne;auto. apply elem_of_gmap_dom_none. rewrite Hdom. clear; set_solver. }
      set (regs' := <[PC:=inl 0%Z]> (<[r_t0:=inr (p, b, e, a)]> (<[r_env:=inl 0%Z]> (<[r_t1:=inl (z + 1)%Z]> (delete r_t1 rmap))))). 
      iDestruct ("Hcallback'" $! regs' with "[Hregs $Hown HPC]") as "[_ Hexpr]". 
      { rewrite /registers_mapsto /regs'.
        iSplit.
        - iClear "Hcallback' Hregs HPC". rewrite /interp_reg /=. iSplit.
          + iPureIntro.
            intros r'. simpl.
            destruct (decide (r' = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r' = r_t0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            destruct (decide (r' = r_env));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto]. rewrite insert_delete. 
            destruct (decide (r' = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
            apply elem_of_gmap_dom. rewrite Hdom. assert (r' ∈ all_registers_s) as Hin;[apply all_registers_s_correct|].
            revert n n0 n1 Hin;clear. set_solver.
          + iIntros (r Hne).
            rewrite /RegLocate. 
            destruct (decide (r = PC));[subst;rewrite lookup_insert|rewrite lookup_insert_ne;auto]. done.
            destruct (decide (r = r_t0));[subst;rewrite lookup_insert|rewrite lookup_insert_ne;auto]. done.
            destruct (decide (r = r_env));[subst;rewrite lookup_insert|rewrite lookup_insert_ne;auto]. rewrite !fixpoint_interp1_eq. done.
            destruct (decide (r = r_t1));[subst;rewrite lookup_insert|rewrite lookup_insert_ne;auto]. rewrite !fixpoint_interp1_eq. done.
            rewrite lookup_delete_ne;auto. destruct (rmap !! r) eqn:Hsome;rewrite Hsome;[|rewrite !fixpoint_interp1_eq;done].
            iDestruct (big_sepM_delete _ _ r with "Hregs_val") as "[Hr _]";[eauto|]. iFrame "Hr".
        - rewrite insert_insert. iApply (big_sepM_delete _ _ PC);[apply lookup_insert|]. iFrame.
          rewrite delete_insert. iFrame.
          repeat (rewrite lookup_insert_ne;auto). rewrite lookup_delete_ne;auto.
          apply elem_of_gmap_dom_none. rewrite Hdom. clear;set_solver.
      }
      rewrite /interp_conf. iApply wp_wand_l. iFrame "Hexpr". 
      iIntros (v). iApply "Hφ".
    - iEpilogue "(HPC & Hi & Hr_t0)".
      iApply "Hcallback_now". iFrame.
      iApply "Hφ". iIntros (Hcontr); inversion Hcontr. 
  Qed.


  (* ----------------------------------- READ -------------------------------------- *)

  Lemma incr_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        incr_addrs (* program addresses *)
        d d' (* dynamically allocated memory given by preamble *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between read_addrs a_first a_last ->
    
    (* Linking table assumptions *)
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption for the counter *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_t0;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->
    
    {{{ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (counter_inv d))
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp wret
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (incr incr_addrs)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ inr (RO,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap)
      (* the remaining registers are all valid *)
      ∗ ([∗ map] _↦w_i ∈ rmap, interp w_i)
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r, full_map r ∧ registers_mapsto r
                         ∗ na_own logrel_nais ⊤ }}}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hlink Hd Hdom Hclose φ) "(HPC & Hr_t0 & Hr_env & Hregs & Hinv & Hown & #Hcallback & #Hincr & #Hlink & #Hregs_val) Hφ". 
    iDestruct "Hinv" as (ι) "#Hinv".
    iMod (na_inv_open with "Hincr Hown") as "(>Hprog & Hown & Hcls)";auto.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct_list incr_addrs.
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a. 
    (* Get a general purpose register *)
    assert (is_Some (rmap !! r_t1)) as [w1 Hrt1].
    { apply elem_of_gmap_dom. rewrite Hdom. apply elem_of_difference.
      split;[apply all_registers_s_correct|clear;set_solver]. }
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[eauto|]. 

  
