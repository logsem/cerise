From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel macros_helpers map_simpl.
From cap_machine Require Export iris_extra addr_reg_sample contiguous safe_malloc assert.

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{static_spinlock.lockG Σ, MP: MachineParameters}.


  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) :=
    [move_r r_t1 PC;
    getb r_t2 r_t1;
    geta r_t3 r_t1;
    sub_r_r r_t2 r_t2 r_t3;
    lea_r r_t1 r_t2;
    load_r r_t1 r_t1;
    lea_z r_t1 f;
    move_z r_t2 0;
    move_z r_t3 0;
    load_r r_t1 r_t1].

  Definition fetch f a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(fetch_instrs f), a_i ↦ₐ w_i)%I.

  (* fetch spec *)
  Lemma fetch_spec i f a pc_p pc_b pc_e a_first a_last b_link e_link a_link
    entry_a wentry φ w1 w2 w3 EN:
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ fetch f a
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ entry_a ↦ₐ wentry
    ∗ ▷ (i,r_t1) ↦ᵣ w1
    ∗ ▷ (i,r_t2) ↦ᵣ w2
    ∗ ▷ (i,r_t3) ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ fetch f a
            (* the newly allocated region *)
            ∗ (i,r_t1) ↦ᵣ wentry ∗ (i,r_t2) ↦ᵣ WInt 0%Z ∗ (i, r_t3) ↦ᵣ WInt 0%Z
            ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
            ∗ entry_a ↦ₐ wentry
            -∗ WP (i, Seq (Instr Executable)) @ EN {{ φ }})
    ⊢
      WP (i, Seq (Instr Executable)) @ EN {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t1 PC *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t1)".
    (* getb r_t2 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t3 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t2 r_t3 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t3 $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 3|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 r_t2 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    assert ((a_first + (pc_b - a_first))%a = Some pc_b) as Hlea;[solve_addr|].
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | ->]; auto. }
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iAssert (⌜(pc_b ≠ f4)%Z⌝)%I as %Hneq.
    { iIntros (Hcontr);subst. iApply (addr_dupl_false with "Hi Hpc_b"). }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Hpc_b]");
      [|apply decode_encode_instrW_inv|iCorrectPC a_first a_last| | |iContiguous_next Hcont 5|..].
    { exact (WCap RW b_link e_link a_link). }
    { apply contiguous_between_length in Hcont as Hlen.
      assert (pc_b < pc_e)%Z as Hle.
      { eapply isCorrectPC_contiguous_range in Hvpc as Hwb';[|eauto|apply elem_of_cons;left;eauto].
        inversion Hwb'. solve_addr. }
      apply isCorrectPC_range_perm in Hvpc as Heq; [|revert Hlen; clear; solve_addr].
      destruct Heq as [-> | ->]; auto. }
    { apply andb_true_intro. split;[apply Z.leb_le;solve_addr|apply Z.ltb_lt;auto].
      assert (pc_b < pc_e)%Z as Hle.
      { eapply isCorrectPC_contiguous_range in Hvpc as Hwb';[|eauto|apply elem_of_cons;left;eauto].
        inversion Hwb'. solve_addr. } auto. }
    { destruct (pc_b =? f4)%a; [done|iFrame]. }
    destruct ((pc_b =? f4)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply finz_to_z_eq in Hcontr;congruence|clear Hcontr].
    iEpilogue "(HPC & Hr_t1 & Hi & Hpc_b)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 f *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hentry|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[|inversion Hlength].
    apply contiguous_between_last with (ai:=f8) in Hcont as Hlink;[|auto].
    iPrologue "Hprog".
    iAssert (⌜(entry_a ≠ f8)%Z⌝)%I as %Hneq'.
    { iIntros (Hcontr);subst. iApply (addr_dupl_false with "Hi Ha_entry"). }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Ha_entry]");
      [exact wentry|apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|auto|apply Hlink|..].
    { destruct (entry_a =? f8)%a; auto. }
    destruct ((entry_a =? f8)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply finz_to_z_eq in Hcontr;congruence|clear Hcontr].
    iEpilogue "(HPC & Hr_t1 & Hi & Hentry_a)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame.
    do 9 iDestruct "Hprog_done" as "[$ Hprog_done]".
    iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_instrs f_a :=
    fetch_instrs f_a ++
    [move_r r_t2 r_t0;
     move_r r_t0 PC;
     lea_z r_t0 3;
     jmp r_t1;
     move_r r_t0 r_t2;
     move_z r_t1 0;
     move_z r_t2 0].

  Definition assert a f_a :=
    ([∗ list] a_i;w_i ∈ a;(assert_instrs f_a), a_i ↦ₐ w_i)%I.

  (* Spec for assertion success *)
  (* Since we are not jumping to the failure subroutine, we do not need any assumptions
     about the failure subroutine *)
  Lemma assert_success i a f_a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link a_entry w0 w1 w2 w3 n1 n2
        ba a_flag ea assertN EN φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry →
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ assert a f_a
    ∗ inv assertN (assert_inv ba a_flag ea)
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E ba ea ba
    ∗ ▷ (i,r_t0) ↦ᵣ w0
    ∗ ▷ (i,r_t1) ↦ᵣ w1
    ∗ ▷ (i,r_t2) ↦ᵣ w2
    ∗ ▷ (i,r_t3) ↦ᵣ w3
    ∗ ▷ (i,r_t4) ↦ᵣ WInt n1
    ∗ ▷ (i,r_t5) ↦ᵣ WInt n2
    ∗ ▷ ((i,r_t0) ↦ᵣ w0 ∗
         (i,r_t1) ↦ᵣ WInt 0%Z ∗ (i,r_t2) ↦ᵣ WInt 0%Z ∗ (i,r_t3) ↦ᵣ WInt 0%Z
         ∗ (i,r_t4) ↦ᵣ WInt 0%Z ∗ (i,r_t5) ↦ᵣ WInt 0%Z
         ∗ (i, PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ assert a f_a
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry ↦ₐ WCap E ba ea ba
         -∗ WP (i, Seq (Instr Executable)) @EN {{ φ }})
    ⊢
    WP (i, Seq (Instr Executable)) @EN {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & >HPC & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & Hφ)".
     (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Htable|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* move r_t2 r_t0 *)
    destruct l';[inversion Hlength_rest|]. subst n2.
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t2 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t0)"; iCombine "Hfetch" "Hi" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|].
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert (pc_p ≠ E).
    { assert (isCorrectPC (WCap pc_p pc_b pc_e a_first)) as HH.
      { apply Hvpc. split. solve_addr.
        apply contiguous_between_length in Hcont.
        rewrite Heqapp app_length /= in Hcont. solve_addr. }
      destruct pc_p; inversion HH; destruct_or?; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|..].
    { iContiguous_next Hcont_rest 2. }
    { eapply (contiguous_between_incr_addr_middle' _ _ _ 1%nat 3).
      apply Hcont_rest. 2: done. 2: done. cbn. lia. } auto.
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t1 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* assert routine *)
    iApply (assert_success_spec with "[- $Hinv $HPC $Hr_t0 $Hr_t4 $Hr_t5]"); auto.
    iNext. iIntros "(HPC & Hr_t0 & Hr_t4 & Hr_t5)".
    rewrite updatePcPerm_cap_non_E//.
    (* move r_t0 r_t2 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 5|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=f4) in Hcont_rest as Hlink';[|auto].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlink'|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Continuation *)
    iApply "Hφ". iFrame.
    rewrite Heqapp /=. iDestruct "Hprog_done" as "(?&?&?&?&?&?&?&?)". iFrame. done.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m size :=
    fetch_instrs f_m ++
    [move_r r_t5 r_t0;
    move_r r_t3 r_t1;
    move_z r_t1 size;
    move_r r_t0 PC;
    lea_z r_t0 3;
    jmp r_t3;
    move_r r_t0 r_t5;
    move_z r_t5 0].

  Definition malloc f_m size a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(malloc_instrs f_m size), a_i ↦ₐ w_i)%I.


  (* malloc spec *)
  Lemma malloc_spec i (φ : language.val cap_lang → iProp Σ) size cont a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link f_m a_entry mallocN b_m e_m γ EN rmap :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset (CoreN * RegName)) rmap =
      ((set_map (fun r=> (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0) ]}) →
    ↑mallocN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a
    ∗ inv mallocN (malloc_inv b_m e_m γ)
    (* (* we need to assume that the malloc capability is in the linking table at offset f_m *) *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ (i,r_t0) ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ malloc f_m size a
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ (i, r_t1) ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ (i,r_t0) ↦ᵣ cont
         ∗ ([∗ map] r_i↦w_i ∈ (<[(i,r_t2) :=WInt 0%Z]>
                                 (<[(i,r_t3) :=WInt 0%Z]>
                                    (<[(i,r_t4) :=WInt 0%Z]>
                                       (<[(i,r_t5) :=WInt 0%Z]>
                                          (<[(i,r_t6) :=WInt 0%Z]>
                                             (<[(i,r_t7) :=WInt 0%Z]>
                                                (<[(i,r_t8) :=WInt 0%Z]>
                                                   (<[(i,r_t9) :=WInt 0%Z]>
                                                      (delete (i, r_t1) rmap))))))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP (i, Seq (Instr Executable)) @ EN {{ φ }})
    ⊢
      WP (i, Seq (Instr Executable)) @ EN {{ λ v, φ v ∨ ⌜v = (i, FailedV)⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! (i, r_t1))) as [rv1 ?].
    by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t1) with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! (i,r_t2))) as [rv2 ?].
    by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t2) with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! (i,r_t3))) as [rv3 ?].
    by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t3) with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! (i,r_t5))) as [rv5 ?].
    by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Ha_entry|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* move r_t5 r_t0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t5 & Hr_t0)". iCombine "Hprog_done" "Hfetch" as "Hprog_done".
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert ((f1 + 3)%a = Some f4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f1 f4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
   [apply decode_encode_instrW_inv|iCorrectPC link a_last
   |iContiguous_next Hcont_rest 4|apply Hlea| idtac| auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | -> ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ (i, r_t3) with "[$Hregs $Hr_t3]") as "Hregs".
    rewrite lookup_delete_ne ; last simplify_pair_eq.
    by rewrite lookup_delete.
    iDestruct (big_sepM_insert _ _ (i, r_t2) with "[$Hregs $Hr_t2]") as "Hregs".
    rewrite lookup_insert_ne ; last simplify_pair_eq.
    do 2 (rewrite lookup_delete_ne ; last simplify_pair_eq).
    by rewrite lookup_delete.
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ (i, r_t5) with "[$Hregs $Hr_t5]") as "Hregs".
    { clear -i; by simplify_map_eq by simplify_pair_eq.  }
    map_simpl "Hregs".
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec with
             "[- $Hmalloc $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite difference_difference_L.
      set_solver+. }
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    iIntros "(Hregs & Hr_t0 & HPC & Hbe)".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize'; subst size'.
    iDestruct (big_sepM_delete _ _ (i, r_t3) with "Hregs") as "[Hr_t3 Hregs]".
    rewrite lookup_insert_ne ; last simplify_pair_eq.
    rewrite lookup_insert //. 
    rewrite delete_insert_ne ; last simplify_pair_eq.
    rewrite delete_insert_delete.
    do 7 (rewrite delete_insert_ne ; last simplify_pair_eq) ; [].
    rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hregs") as "[Hr_t5 Hregs]".
    do 6 (rewrite lookup_insert_ne ; last simplify_pair_eq).
    rewrite lookup_insert //. 
    do 6 (rewrite delete_insert_ne ; last simplify_pair_eq) ; [].
    rewrite delete_insert_delete.
    rewrite delete_insert_ne ; last simplify_pair_eq ; [].
    (* move r_t0 r_t5 *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t5 0 *)
    destruct l';[| by inversion Hlength_rest].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=f5) in Hcont_rest as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ (i, r_t5) with "[$Hregs $Hr_t5]") as "Hregs".
    do 7 (rewrite lookup_insert_ne ; last simplify_pair_eq ;[]).
    apply lookup_delete.
    iDestruct (big_sepM_insert _ _ (i, r_t3) with "[$Hregs $Hr_t3]") as "Hregs".
    do 8 (rewrite lookup_insert_ne ; last simplify_pair_eq ;[]).
    rewrite lookup_delete_ne ; last simplify_pair_eq.
    apply lookup_delete.
    do 3 (rewrite (insert_commute _ (i, r_t5)) ; last simplify_pair_eq ;[]).
    do 4 (rewrite (insert_commute _ (i, r_t9)) ; last simplify_pair_eq ;[]).
    map_simpl "Hregs". rewrite (insert_commute _ (i, r_t2) (i, r_t3)); auto.
    iFrame.
    iExists b,e. iFrame. auto.
    auto.
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec_alt i φ ψ size cont a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link f_m a_entry mallocN b_m e_m γ EN rmap :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset (CoreN * RegName)) rmap =
      ((set_map (fun r=> (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0) ]}) →
    ↑mallocN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a
    ∗ inv mallocN (malloc_inv b_m e_m γ)
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ (i,r_t0) ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (ψ (i, FailedV))
    ∗ ▷ ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ malloc f_m size a
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ (i,r_t1) ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ (i, r_t0) ↦ᵣ cont
         ∗ ([∗ map] r_i↦w_i ∈ (<[(i,r_t2) :=WInt 0%Z]>
                                 (<[(i,r_t3) :=WInt 0%Z]>
                                    (<[(i,r_t4) :=WInt 0%Z]>
                                       (<[(i,r_t5) :=WInt 0%Z]>
                                          (<[(i,r_t6) :=WInt 0%Z]>
                                             (<[(i,r_t7) :=WInt 0%Z]>
                                                (<[(i,r_t8) :=WInt 0%Z]>
                                                   (<[(i,r_t9) :=WInt 0%Z]>
                                                      (delete (i, r_t1) rmap))))))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP (i, Seq (Instr Executable)) @ EN {{ ψ }})
    ⊢
      WP (i, Seq (Instr Executable)) @ EN {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! (i,r_t1))) as [rv1 ?].
    by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t1) with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! (i,r_t2))) as [rv2 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t2) with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! (i,r_t3))) as [rv3 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t3) with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! (i,r_t5))) as [rv5 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+.
    iDestruct (big_sepM_delete _ _ (i,r_t5) with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Ha_entry|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* move r_t5 r_t0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t5 & Hr_t0)". iCombine "Hprog_done" "Hfetch" as "Hprog_done".
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert ((f1 + 3)%a = Some f4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f1 f4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
   [apply decode_encode_instrW_inv|iCorrectPC link a_last
   |iContiguous_next Hcont_rest 4|apply Hlea| idtac| auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | -> ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ (i, r_t3) with "[$Hregs $Hr_t3]") as "Hregs".
    rewrite lookup_delete_ne ; last simplify_pair_eq.
    by rewrite lookup_delete.
    iDestruct (big_sepM_insert _ _ (i, r_t2) with "[$Hregs $Hr_t2]") as "Hregs".
    rewrite lookup_insert_ne ; last simplify_pair_eq.
    do 2 (rewrite lookup_delete_ne ; last simplify_pair_eq).
    by rewrite lookup_delete.
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ (i, r_t5) with "[$Hregs $Hr_t5]") as "Hregs".
    { clear -i; by simplify_map_eq by simplify_pair_eq.  }
    map_simpl "Hregs".
    iApply (wp_wand with "[- Hφfailed Hψ]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite difference_difference_L.
      set_solver+. }
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    iIntros "(Hregs & Hr_t0 & HPC & Hbe)".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize';subst size'.
    iDestruct (big_sepM_delete _ _ (i, r_t3) with "Hregs") as "[Hr_t3 Hregs]".
    rewrite lookup_insert_ne ; last simplify_pair_eq.
    rewrite lookup_insert //.
    rewrite delete_insert_ne ; last simplify_pair_eq.
    rewrite delete_insert_delete.
    do 7 (rewrite delete_insert_ne ; last simplify_pair_eq) ; [].
    rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ (i, r_t5) with "Hregs") as "[Hr_t5 Hregs]".
    do 6 (rewrite lookup_insert_ne ; last simplify_pair_eq).
    rewrite lookup_insert //. 
    do 6 (rewrite delete_insert_ne ; last simplify_pair_eq) ; [].
    rewrite delete_insert_delete.
    rewrite delete_insert_ne ; last simplify_pair_eq ; [].
    (* move r_t0 r_t5 *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t5 0 *)
    destruct l';[| by inversion Hlength_rest].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=f5) in Hcont_rest as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ (i, r_t5) with "[$Hregs $Hr_t5]") as "Hregs".
    do 7 (rewrite lookup_insert_ne ; last simplify_pair_eq ;[]).
    apply lookup_delete.
    iDestruct (big_sepM_insert _ _ (i, r_t3) with "[$Hregs $Hr_t3]") as "Hregs".
    do 8 (rewrite lookup_insert_ne ; last simplify_pair_eq ;[]).
    rewrite lookup_delete_ne ; last simplify_pair_eq.
    apply lookup_delete.
    do 3 (rewrite (insert_commute _ (i, r_t5)) ; last simplify_pair_eq ;[]).
    do 4 (rewrite (insert_commute _ (i, r_t9)) ; last simplify_pair_eq ;[]).
    map_simpl "Hregs". rewrite (insert_commute _ (i, r_t2) (i, r_t3)); auto.
    iFrame.
    iExists b,e. iFrame. auto. iIntros (v) "[Hφ|Hφ] /=". iApply "Hψ". iFrame.
    iDestruct "Hφ" as %->. iApply "Hψ". iFrame.
  Qed.


  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) := map (λ r_i, move_z r_i 0) r.

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = move_z rr 0 :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Definition rclear (a : list Addr) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↦ₐ w_i)%I.

  Lemma rclear_spec (i : CoreN) (a : list Addr) (r: list RegName)
    (rmap : gmap (CoreN*RegName) Word) p b e a1 an φ :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p b e a1 an →
    (set_map (fun (r' : RegName) => (i,r'))
       (@list_to_set RegName (gset RegName) _ _ _ r))
    = dom (gset (CoreN * RegName)) rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ (i,PC) ↦ᵣ WCap p b e a1
    ∗ ▷ rclear a r
    ∗ ▷ ((i, PC) ↦ᵣ WCap p b e an
         ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ WInt 0%Z)
         ∗ rclear a r
         -∗ WP (i, Seq (Instr Executable)) {{ φ }})
    ⊢  WP (i, Seq (Instr Executable)) {{ φ }}.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
    rewrite /rclear /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! (i,r))) as [rv ?].
    { rewrite elem_of_gmap_dom -Hrdom. set_solver+. }
    iDestruct (big_sepM_delete _ _ (i, r) with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iApply (wp_move_success_z with "[$HPC $Hr $Ha1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|..].
    iNext. iIntros "(HPC & Ha1 & Hr)". iApply wp_pure_step_later; auto. iNext.
    destruct a.
    { iApply "Hφ". iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ (i,r)). eauto.
      rewrite (_: delete (i,r) rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset (CoreN*RegName))).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete.
      iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1]"); eauto.
      { iNext. iIntros "(? & Hreg & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ (i,r)). eauto.
        iDestruct (big_sepM_delete _ _ (i,r) with "Hreg") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. } }
    { iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1 Hr]"); eauto.
      { iNext. iIntros "(? & ? & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ (i,r)). eauto. iFrame. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. } }
  Qed.

  (* -------------------------------------- MCLEAR ----------------------------------- *)
   (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 23 *)

  Definition mclear_off_end := 10%Z.
  Definition mclear_off_iter := 2%Z.

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_instrs r_stk :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4;
      geta r_t2 r_t4;
      sub_r_r r_t2 r_t1 r_t2;
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      sub_r_z r_t5 r_t5 1; (* we subtract the bound by one so that the lt check becomes a le check *)
      move_r r_t2 PC;
      lea_z r_t2 mclear_off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 mclear_off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1;
      jnz r_t2 r_t6;
      store_z r_t4 0;
      lea_z r_t4 1;
      add_r_z r_t1 r_t1 1;
      jmp r_t3;
    (* end: *)
      move_z r_t4 0;
      move_z r_t1 0;
      move_z r_t2 0;
      move_z r_t3 0;
      move_z r_t5 0;
      move_z r_t6 0].

  (* Next we define mclear in memory, using a list of addresses of size 23 *)
  Definition mclear (a : list Addr) (r : RegName) : iProp Σ :=
    if ((length a) =? (length (mclear_instrs r)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_instrs r), a_i ↦ₐ w_i)%I
    else
      False%I.

  Lemma mclear_iter_spec i (a1 a2 a3 a4 a5 a6 b_r e_r a_r (* e_r' *) : Addr) ws (z : nat)
        p b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r : Perm) φ :
        isCorrectPC (WCap p b e a1)
      ∧ isCorrectPC (WCap p b e a2)
      ∧ isCorrectPC (WCap p b e a3)
      ∧ isCorrectPC (WCap p b e a4)
      ∧ isCorrectPC (WCap p b e a5)
      ∧ isCorrectPC (WCap p b e a6) →
        (a1 + 1)%a = Some a2
      ∧ (a2 + 1)%a = Some a3
      ∧ (a3 + 1)%a = Some a4
      ∧ (a4 + 1)%a = Some a5
      ∧ (a5 + 1)%a = Some a6 →
        ((b_r + z < e_r)%Z → withinBounds b_r e_r a_r = true) →
        writeAllowed p_r = true →
        (* (e_r + 1)%a = Some e_r' → *)
        (b_r + z)%a = Some a_r →
      ([[a_r,e_r]] ↦ₐ [[ws]]
     ∗ ▷ (i,PC) ↦ᵣ WCap p b e a1
     ∗ ▷ (i,rt) ↦ᵣ WCap p_r b_r e_r a_r
     ∗ ▷ (i,rt1) ↦ᵣ WInt (b_r + z)%Z
     ∗ ▷ (i,rt2) ↦ᵣ WInt ((z_of e_r) - 1)%Z
     ∗ ▷ (∃ w, (i,rt3) ↦ᵣ w)
     ∗ ▷ (i,rt4) ↦ᵣ WCap p b e a_end
     ∗ ▷ (i,rt5) ↦ᵣ WCap p b e a1
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5;a6];[lt_r_r rt3 rt2 rt1;
                                                  jnz rt4 rt3;
                                                  store_z rt 0;
                                                  lea_z rt 1;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ w_i)
     ∗ ▷ ((i,PC) ↦ᵣ updatePcPerm (WCap p b e a_end)
             ∗ [[ a_r , e_r ]] ↦ₐ [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, (i,rt) ↦ᵣ WCap p_r b_r e_r a_r)
             ∗ (i,rt5) ↦ᵣ WCap p b e a1
             ∗ a3 ↦ₐ store_z rt 0
             ∗ a4 ↦ₐ lea_z rt 1
             ∗ a5 ↦ₐ add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ jmp rt5
             ∗ a1 ↦ₐ lt_r_r rt3 rt2 rt1
             ∗ (i,rt2) ↦ᵣ WInt ((z_of e_r) - 1)%Z
             ∗ (∃ z, (i,rt1) ↦ᵣ WInt (b_r + z)%Z)
             ∗ a2 ↦ₐ jnz rt4 rt3
             ∗ (i,rt4) ↦ᵣ WCap p b e a_end
             ∗ (i,rt3) ↦ᵣ WInt 1%Z
              -∗ WP (i, Seq (Instr Executable)) {{ φ }})
     ⊢ WP (i, Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hwa (* Her' *) Hprogress)
            "(Hbe & >HPC & >Hrt & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hprog & Hφ)".
    iRevert (Hwb Hprogress).
    iLöb as "IH" forall (a_r ws z).
    iIntros (Hwb Hprogress).
    iDestruct "Hr_t3" as (w) "Hr_t3".
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5 & Hvpc6).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4 & Hnext5).
    iAssert (⌜rt1 ≠ PC⌝)%I as %Hne1.
    { destruct (reg_eq_dec rt1 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 HPC") as "Hfalse". }
    iAssert (⌜rt3 ≠ PC⌝)%I as %Hne2.
    { destruct (reg_eq_dec rt3 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t3 HPC") as "Hfalse". }
    iAssert (⌜rt ≠ PC⌝)%I as %Hne3.
    { destruct (reg_eq_dec rt PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hrt HPC") as "Hfalse". }
    iAssert (⌜rt2 ≠ rt3⌝)%I as %Hne4.
    { destruct (reg_eq_dec rt2 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t2 Hr_t3") as "Hfalse". }
    iAssert (⌜rt1 ≠ rt3⌝)%I as %Hne5.
    { destruct (reg_eq_dec rt1 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 Hr_t3") as "Hfalse". }
    (* lt rt3 rt2 rt1 *)
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
    iApply (wp_add_sub_lt_success_r_r _ i rt3 _ _ _ a1 _ _ _ rt2 _ rt1 _ _
      with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); [apply decode_encode_instrW_inv | | | ..]; eauto.
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t1 & Hr_t3)".
    rewrite /region_mapsto /finz.seq_between.
    destruct (Z_le_dec (b_r + z) (e_r - 1))%Z; simpl.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_lt in HH. lia. }
      rewrite Heq0.
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_jnz_success_next _ i rt4 rt3 _ _ _ a2 a3 with "[HPC Hi Hr_t3 Hr_t4]");
        first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      (* store rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b%Z.leb_le Hwb_e%Z.ltb_lt].
      rewrite {1}finz_dist_S /=.
      destruct ws as [| w1 ws]; simpl; [by iApply bi.False_elim|].
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_store_success_z _ i _ _ _ a3 a4 _ rt 0 _ p_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply decode_encode_instrW_inv; eauto.
      { rewrite /withinBounds andb_true_iff; split;[auto|].
          by apply Z.leb_le. by apply Z.ltb_lt. }
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r'].
      { apply addr_next_lt with e_r. apply incr_addr_of_z_i in Hprogress. lia. }
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_lea_success_z _ i _ _ _ a4 a5 _ rt p_r _ _ a_r 1 a_r' with "[HPC Hi Hrt]"); first apply decode_encode_instrW_inv; eauto.
      { destruct p_r; auto. }
      iFrame. iEpilogue "(HPC & Ha4 & Hrt)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_add_sub_lt_success_dst_z _ i rt1 _ _ _ a5 _ _ _ with "[HPC Hi Hr_t1]"); try iFrame;
        [ apply decode_encode_instrW_inv | | |..]; eauto.
      iEpilogue "(HPC & Ha5 & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_jmp_success _ i _ _ _ a6 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%nat with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. all: auto.
      + by rewrite (addr_incr_eq Ha_r').
      + assert (updatePcPerm (WCap p b e a1) = (WCap p b e a1)).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H5 as [Hc | Hc ]; inversion Hc. }
        rewrite H0. iFrame.
      + cbn. assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
      + iNext.
        iIntros "(HPC & Hregion & Hrt & Hrt5 & Ha3 & Ha4 & Ha5 & Ha6 & Ha1 & Hrt2 & Hrt1 & Ha2 & Hrt4 & Hrt3)".
        iApply "Hφ".
        iFrame.
        rewrite /region_addrs_zeroes.
        rewrite (finz_dist_S a_r e_r) //= (_: (a_r^+1)%a = a_r'); [| solve_addr].
        iFrame.
      + iPureIntro. intro.
        rewrite andb_true_iff -Zle_is_le_bool -Zlt_is_lt_bool. solve_addr.
      + iPureIntro. solve_addr.
      + solve_addr.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_nlt in HH. lia. }
      rewrite Heq0.
      assert (e_r <= a_r)%Z by solve_addr.
      (* destruct (Z_le_dec a_r e_r). *)
      rewrite finz_dist_0 //=.
      destruct ws;[|by iApply bi.False_elim].
      (* jnz *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx]) _ _ (_, _) _).
      iApply (wp_jnz_success_jmp _ i rt4 rt3 _ _ _ a2 _ _ (WInt 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      iApply "Hφ". iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & _)".
      rewrite /region_addrs_zeroes finz_dist_0 //=. iFrame.
      iSplitL "Hrt"; eauto.
  Qed.

  Lemma mclear_spec i (a : list Addr) (r : RegName)
        (a_first a6' a_end : Addr) p b e p_r (b_r e_r a_r : Addr) a'
        w1 w2 w3 w4 w5 w6 ws φ :
    contiguous_between a a_first a' →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 17 = Some a_end) →

    isCorrectPC_range p b e a_first a' →

    (* We will also assume the region to clear is non empty *)
    (b_r ≤ e_r)%Z →

     (mclear a r
    ∗ ▷ (i,PC) ↦ᵣ WCap p b e a_first
    ∗ ▷ (i,r) ↦ᵣ WCap p_r b_r e_r a_r
    ∗ ▷ (i,r_t4) ↦ᵣ w4
    ∗ ▷ (i,r_t1) ↦ᵣ w1
    ∗ ▷ (i,r_t2) ↦ᵣ w2
    ∗ ▷ (i,r_t3) ↦ᵣ w3
    ∗ ▷ (i,r_t5) ↦ᵣ w5
    ∗ ▷ (i,r_t6) ↦ᵣ w6
    ∗ ▷ ([[ b_r , e_r ]] ↦ₐ [[ ws ]])
    ∗ ▷ ((i,PC) ↦ᵣ WCap p b e a'
            ∗ (i,r_t1) ↦ᵣ WInt 0%Z
            ∗ (i,r_t2) ↦ᵣ WInt 0%Z
            ∗ (i,r_t3) ↦ᵣ WInt 0%Z
            ∗ (i,r_t4) ↦ᵣ WInt 0%Z
            ∗ (i,r_t5) ↦ᵣ WInt 0%Z
            ∗ (i,r_t6) ↦ᵣ WInt 0%Z
            ∗ (i,r) ↦ᵣ WCap p_r b_r e_r a_r
            ∗ [[ b_r , e_r ]] ↦ₐ [[region_addrs_zeroes b_r e_r]]
            ∗ mclear a r -∗
            WP (i,Seq (Instr Executable)) {{ φ }})
    ⊢ WP (i,Seq (Instr Executable)) {{ φ }})%I.
  Proof.
    iIntros (Hnext [Hne Hwa] Hjnz_off Hvpc Hle)
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iAssert (⌜((length a) =? (length (mclear_instrs r)) = true)%nat⌝)%I as %Hlen.
    { destruct (((length a) =? (length (mclear_instrs r)))%nat) eqn:Hlen; auto.
      rewrite /mclear Hlen. by iApply bi.False_elim. }
    rewrite /mclear Hlen /mclear_instrs; simpl in Hlen. apply beq_nat_true in Hlen.
    destruct a as [| a1 a]; inversion Hlen; simpl.
    move: (contiguous_between_cons_inv_first _ _ _ _ Hnext).
    match goal with |- (?a = _) -> _ => intro; subst a end.
    iPrologue "Hmclear".
    iApply (wp_move_success_reg _ i _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 0. }
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)".
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ i _ r_t1 r_t4 _ _ _ a0 _ _ _ _ _ _ a1 with "[$HPC $Hi $Hr_t1 $Hr_t4]");
      first eapply decode_encode_instrW_inv; first eauto; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 1. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha0 Ha_first" as "Hprog_done".
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ i _ r_t2 r_t4 _ _ _ a1 _ _ _ _ _ _ a2 with "[HPC Hi Hr_t2 Hr_t4]");
      first eapply decode_encode_instrW_inv; first eauto; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 2. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha1 Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    (* destruct b_r eqn:Hb_r. *)
    iApply (wp_add_sub_lt_success_r_dst _ i _ _ _ _ a2 _ _ r_t1 with "[HPC Hi Hr_t1 Hr_t2]"); try iFrame;
      [ apply decode_encode_instrW_inv | | |..]; eauto. 2: by iCorrectPC a_first a'.
    assert ((a2 + 1) = Some a3)%a as ->. { iContiguous_next Hnext 3. } by eauto.
    iEpilogue "(HPC & Ha2 & Hr_t1 & Hr_t2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done".
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r by solve_addr.
    iApply (wp_lea_success_reg _ i _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 4. }
    { destruct p_r; inversion Hwa; auto. }
    by iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done".
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ i _ r_t5 r_t4 _ _ _ a4 _ _ _ _ _ _ a5 with "[HPC Hi Hr_t5 Hr_t4]"); try iFrame;
      first apply decode_encode_instrW_inv; first eauto; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 5. }
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done".
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi Hr_t5]");
      [apply decode_encode_instrW_inv| | |iCorrectPC a_first a'|..]; eauto.
    assert ((a5 + 1)%a = Some a6) as ->. { iContiguous_next Hnext 6. } eauto.
    iEpilogue "(HPC & Ha5 & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ i _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 7. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done".
    (* lea r_t2 mclear_off_end *)
    iPrologue "Hprog".
    assert (p ≠ E) as Hpne.
    { have: (isCorrectPC (WCap p b e a_first)).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H15 as [? | ? ]; subst; auto. }
    iApply (wp_lea_success_z _ i _ _ _ a7 a8 _ r_t2 p _ _ a6 10 a_end with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 8. }
    { destruct Hjnz_off as (Ha7' & Hmclear_off_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done".
    (* move r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ i _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 9. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done".
    (* lea r_t3 mclear_off_iter *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ i _ _ _ a9 a10 _ r_t3 p _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 10. }
    { assert (2 = 1 + 1)%Z as ->; auto.
      apply incr_addr_trans with a9. iContiguous_next Hnext 9.
      iContiguous_next Hnext 10. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    do 5 iPrologue_pre. clear H1 H2 H3 H4.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iApply (mclear_iter_spec i a10 a11 a12 a13 a14 a15 b_r e_r b_r _
                        0 p b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r
              with "[-]"); auto.
    - repeat apply conj; iCorrectPC a_first a'.
    - repeat split; solve [
        iContiguous_next Hnext 11; auto
      | iContiguous_next Hnext 12; auto
      | iContiguous_next Hnext 13; auto
      | iContiguous_next Hnext 14; auto
      | iContiguous_next Hnext 15; auto ].
    - (* rewrite Z.add_0_r. intros Hle. *)
      rewrite /withinBounds. intro.
      rewrite andb_true_iff Z.leb_le Z.ltb_lt. lia.
    - apply addr_add_0.
    - rewrite Z.add_0_r.
      iFrame.
      iSplitL "Hr_t6". iNext. iExists w6. iFrame.
      iSplitR; auto.
      iNext.
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha11 & Ha12 & Ha13 & Ha14 &
         Ha9 & Hr_t5 & Hr_t1 & Ha10 & Hr_t2 & Hr_t6)".
      iCombine "Ha9 Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done".
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      iPrologue "Hprog".
      assert (a16 = a_end)%a as Ha16.
      { simpl in Hjnz_off.
        destruct Hjnz_off as (Ha16 & Ha16' & Hend).
        by inversion Hend.
      }
      destruct a as [| a17 a]; inversion Hlen.
      iApply (wp_move_success_z _ i _ _ _ a16 a17 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 17; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ i _ _ _ a17 a18 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 18. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ i _ _ _ a18 a19 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 19. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ i _ _ _ a19 a20 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 20. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ i _ _ _ a20 a21 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 21. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ i _ _ _ a21 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { eapply contiguous_between_last. eapply Hnext. reflexivity. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
         & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame.
  Qed.



  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)

  (* TODO: move this to the rules_Get.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Get_fail E i get_i dst src pc_p pc_b pc_e pc_a w zsrc wdst :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ (i,dst) ↦ᵣ wdst
      ∗ ▷ (i,src) ↦ᵣ WInt zsrc }}}
      (i, Instr Executable) @ E
      {{{ RET (i, FailedV); True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { rewrite /regs_of_core.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq by simplify_pair_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  (* TODO: move this to the rules_Lea.v file. *)
  Lemma wp_Lea_fail_none Ep i pc_p pc_b pc_e pc_a w r1 rv p b e a z :
    decodeInstrW w = Lea r1 (inr rv) →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (a + z)%a = None ->

     {{{ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e pc_a
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ (i,r1) ↦ᵣ WCap p b e a
           ∗ ▷ (i,rv) ↦ᵣ WInt z }}}
       (i,Instr Executable) @ Ep
     {{{ RET (i,FailedV); True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hz φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by rewrite /regs_of_core !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq by simplify_pair_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  (* ------------------------------- *)


  Definition reqperm_instrs r z :=
    [getp r_t1 r;
    sub_r_z r_t1 r_t1 z;
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition reqperm r z a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqperm_instrs r z), a_i ↦ₐ w_i)%I.

  Lemma reqperm_spec i r perm a w pc_p pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ reqperm r (encodePerm perm) a
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ (i,r) ↦ᵣ w
    ∗ ▷ (∃ w, (i,r_t1) ↦ᵣ w)
    ∗ ▷ (∃ w, (i,r_t2) ↦ᵣ w)
    ∗ ▷ (if isPermWord w perm then
           ∃ b e a', ⌜w = WCap perm b e a'⌝ ∧
          ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ reqperm r (encodePerm perm) a ∗
            (i,r) ↦ᵣ WCap perm b e a' ∗ (i,r_t1) ↦ᵣ WInt 0%Z ∗ (i,r_t2) ↦ᵣ WInt 0%Z
            -∗ WP (i,Seq (Instr Executable)) {{ φ }})
        else φ (i, FailedV))
    ⊢
      WP (i,Seq (Instr Executable)) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    destruct w.
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=".
      iApply wp_value. done.
    }
    (* if w is a capability, the getL will succeed *)
    destruct a as [|a l];[done|].
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".
    iSimpl in "Hr_t1".
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    destruct l;[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    destruct l;[done|].
    iPrologue "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t2 6 *)
    do 7 (destruct l;[done|]). destruct l; [|done].
    assert ((f + 6)%a = Some f5) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 f f5) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { apply isCorrectPC_range_perm in Hvpc as [Heq | Heq ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    destruct (decide (encodePerm p - encodePerm perm = 0))%Z.
    - (* p is perm *)
      rewrite e0. assert (p = perm);[apply encodePerm_inj;lia|subst].
      iSimpl in "Hcont". rewrite isPerm_refl. iDestruct "Hcont" as (b0 e1 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 3 *)
      assert ((f2 + 4)%a = Some f6) as Hlea'.
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 f2 f6) in Hcont; auto. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      assert (updatePcPerm (WCap pc_p pc_b pc_e f6) = (WCap pc_p pc_b pc_e f6)) as ->.
      { destruct pc_p; auto. congruence. }
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=f7) in Hcont as Hnext;[|auto].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      do 10 (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi").
      iFrame.
    - assert (p ≠ perm) as HneP.
      { intros Hcontr. subst. lia. }
      iSimpl in "Hcont". rewrite isPerm_ne;[|auto].
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* fail *)
      iPrologue "Hprog".
      assert (updatePcPerm (WCap pc_p pc_b pc_e f5) = (WCap pc_p pc_b pc_e f5)) as ->.
      { destruct pc_p; auto. congruence. }
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont".
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) greater than [minsize]. *)

  Definition reqsize_instrs r (minsize: Z) :=
    [getb r_t1 r;
     gete r_t2 r;
     sub_r_r r_t1 r_t2 r_t1;
     lt_z_r r_t1 minsize r_t1;
     move_r r_t2 PC;
     lea_z r_t2 4;
     jnz r_t2 r_t1;
     fail_end].

  Definition reqsize r minsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqsize_instrs r minsize), a_i ↦ₐ w_i)%I.

  Lemma reqsize_spec i r minsize a pc_p pc_b pc_e a_first a_last r_p r_b r_e r_a w1 w2 φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →

      ▷ reqsize r minsize a
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ (i,r) ↦ᵣ WCap r_p r_b r_e r_a
    ∗ ▷ (i,r_t1) ↦ᵣ w1
    ∗ ▷ (i,r_t2) ↦ᵣ w2
    ∗ ▷ (if (minsize <? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            reqsize r minsize a
            ∗ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last
            ∗ (i,r) ↦ᵣ WCap r_p r_b r_e r_a
            ∗ (i,r_t1) ↦ᵣ w1
            ∗ (i,r_t2) ↦ᵣ w2)
           -∗ WP (i, Seq (Instr Executable)) {{ φ }}
        else φ (i, FailedV))
    ⊢
    WP (i, Seq (Instr Executable)) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr1 & >Hr2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { iIntros (->). iApply (regname_dupl_false with "HPC Hr"). }
    destruct a as [| a l];[done|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_perm_non_E; eauto.
      generalize (contiguous_between_length _ _ _ Hcont). rewrite Hlength /=.
      clear; solve_addr. }
    (* getb r_t1 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr1)". iRename "Hi" into "Hprog_done".
    (* gete r_t2 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub_r_r r_t1 r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_dst with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 2|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt_z_r r_t1 minsize r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 3|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t2 PC *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t2 4 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|try done..].
    { change 4%Z with (Z.of_nat (4%nat)).
      (* FIXME: a bit annoying to have to specify the index manually *)
      eapply (contiguous_between_middle_to_end _ _ _ 4); eauto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    destruct (minsize <? r_e - r_b)%Z eqn:Htest; simpl.
    { iApply (wp_jnz_success_jmp with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|done|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iApply "Hcont". iExists _,_.
      rewrite updatePcPerm_cap_non_E //. iFrame.
      iDestruct "Hprog_done" as "(?&?&?&?&?&?)". iFrame. }
    { iApply (wp_jnz_success_next with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". }
  Qed.

  (* ---------------------------------------- CRTCLS ------------------------------------ *)
  (* The following macro creates a closure with one variable. A more general create closure would
     allow for more than one variable in the closure, but this is so far not necessary for our
     examples. The closure allocates a new region with a capability to the closure code, the closure
     variable, and the closure activation *)

  (* encodings of closure activation code *)
  Definition v1 := encodeInstr (Mov r_t1 (inr PC)).
  Definition v2 := encodeInstr (Lea r_t1 (inl 7%Z)).
  Definition v3 := encodeInstr (Load r_env r_t1).
  Definition v4 := encodeInstr (Lea r_t1 (inl (-1)%Z)).
  Definition v5 := encodeInstr (Load r_t1 r_t1).
  Definition v6 := encodeInstr (Jmp r_t1).

  Definition activation_instrs wcode wenv : list Word :=
    [ WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; wcode; wenv ].

  (* scrtcls: "static" crtcls. Requires a capability for the memory region where to write
     the activation record.

     It assumes the pointer to the region for the activation record is in r_t1, the
     code pointer is in register rcode, and the data pointer in rdata.
  *)
  Definition scrtcls_instrs rcode rdata :=
    [store_z r_t1 v1;
     lea_z r_t1 1;
     store_z r_t1 v2;
     lea_z r_t1 1;
     store_z r_t1 v3;
     lea_z r_t1 1;
     store_z r_t1 v4;
     lea_z r_t1 1;
     store_z r_t1 v5;
     lea_z r_t1 1;
     store_z r_t1 v6;
     lea_z r_t1 1;
     store_r r_t1 rcode;
     move_z rcode 0;
     lea_z r_t1 1;
     store_r r_t1 rdata;
     move_z rdata 0;
     lea_z r_t1 (-7)%Z;
     restrict_z r_t1 e].

  Definition scrtcls rcode rdata a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(scrtcls_instrs rcode rdata), a_i ↦ₐ w_i)%I.

  (* crtcls: calls malloc to allocate memory for the activation record, then scrtcls. *)
  (* f_m denotes the offset to the malloc capability in the lookup table *)
  (* crtcls assumes that the code lies in register r_t1 and the variable lies in r_t2 *)
  Definition crtcls_instrs f_m :=
    [move_r r_t6 r_t1;
    move_r r_t7 r_t2] ++
    malloc_instrs f_m 8%nat ++
    scrtcls_instrs r_t6 r_t7.

  Definition crtcls f_m a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(crtcls_instrs f_m), a_i ↦ₐ w_i)%I.

  (* scrtcls *)
  Lemma scrtcls_spec i rcode rdata wvar wcode a pc_p pc_b pc_e a_first a_last
        act_b act_e act EN φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (act_b + 8)%a = Some act_e →

      ▷ scrtcls rcode rdata a
    ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first
    (* register state *)
    ∗ ▷ (i,r_t1) ↦ᵣ WCap RWX act_b act_e act_b
    ∗ ▷ (i,rcode) ↦ᵣ wcode
    ∗ ▷ (i,rdata) ↦ᵣ wvar
    (* memory for the activation record *)
    ∗ ▷ ([[act_b,act_e]] ↦ₐ [[ act ]])
    (* continuation *)
    ∗ ▷ ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ scrtcls rcode rdata a
         ∗ (i,r_t1) ↦ᵣ WCap E act_b act_e act_b
         ∗ [[act_b,act_e]] ↦ₐ [[ activation_instrs wcode wvar ]]
         ∗ (i,rcode) ↦ᵣ WInt 0%Z
         ∗ (i,rdata) ↦ᵣ WInt 0%Z
         -∗ WP (i,Seq (Instr Executable)) @ EN {{ φ }})
    ⊢
      WP (i,Seq (Instr Executable)) @ EN {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hact) "(>Hprog & >HPC & >Hr_t1 & >Hrcode & >Hrdata & >Hact & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (act_b < act_e)%a as Hlt;[solve_addr|].
    feed pose proof (contiguous_between_region_addrs act_b act_e) as Hcont_act. solve_addr.
    unfold region_mapsto.
    remember (finz.seq_between act_b act_e) as acta.
    assert (Hact_len_a : length acta = 8).
    { rewrite Heqacta finz_seq_between_length. by apply finz_incr_iff_dist. }
    iDestruct (big_sepL2_length with "Hact") as %Hact_len.
    rewrite Hact_len_a in Hact_len. symmetry in Hact_len.
    repeat (destruct act as [| ? act]; try by inversion Hact_len). clear Hact_len.
    destruct a as [|a l]; [inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    assert (∀ i a', acta !! i = Some a' → withinBounds act_b act_e a' = true) as Hwbact.
    { intros ni a' Hsome. apply andb_true_intro. subst acta.
      apply contiguous_between_incr_addr with (i:=ni) (ai:=a') in Hcont_act. 2: done.
      apply lookup_lt_Some in Hsome. split;[apply Z.leb_le|apply Z.ltb_lt]; solve_addr. }
    (* store_z r_t1 v1 *)
    destruct l; [inversion Hlength|].
    destruct acta as [| a0 acta]; [inversion Hact_len_a|].
    assert (a0 = act_b) as ->.
    { feed pose proof (finz_seq_between_first act_b act_e) as HH. solve_addr.
      rewrite -Heqacta /= in HH. by inversion HH. }
    iDestruct "Hact" as "[Ha0 Hact]".
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Ha0 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|..]; auto.
    { apply Hwbact with 0. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hact')"; iRename "Hi" into "Hprog_done".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| a1 acta]; [inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|
       iContiguous_next Hcont_act 0|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v2 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha1 Hact]".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Ha1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|..]; auto.
    { apply Hwbact with 1. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Ha1)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha1" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|
       iContiguous_next Hcont_act 1|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v3 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha2 Hact]".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Ha2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..]; auto.
    { apply Hwbact with 2. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Ha2)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha2" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|
       iContiguous_next Hcont_act 2|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v4 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha3 Hact]".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Ha3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..]; auto.
    { apply Hwbact with 3. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Ha3)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha3" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|
       iContiguous_next Hcont_act 3|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v5 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha4 Hact]".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Ha4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|..]; auto.
    { apply Hwbact with 4. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Ha4)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha4" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|
       iContiguous_next Hcont_act 4|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v6 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha5 Hact]".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Ha5]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 10|..]; auto.
    { apply Hwbact with 5. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Ha5)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha5" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 11|
       iContiguous_next Hcont_act 5|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 rcode *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha6 Hact]".
    iApply (wp_store_success_reg with "[$HPC $Hi $Ha6 $Hrcode $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 12|..]; auto.
    { apply Hwbact with 6. auto. }
    iEpilogue "(HPC & Hi & Hrcode & Hr_t1 & Ha6)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha6" "Hact'" as "Hact'".
    (* move rcode 0 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hrcode]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 13|auto..].
    iEpilogue "(HPC & Hi & Hrcode)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 14|
       iContiguous_next Hcont_act 6|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 rdata *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iDestruct "Hact" as "[Ha7 Hact]".
    iApply (wp_store_success_reg with "[$HPC $Hi $Ha7 $Hrdata $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 15|..]; auto.
    { apply Hwbact with 7. auto. }
    iEpilogue "(HPC & Hi & Hrdata & Hr_t1 & Ha7)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha7" "Hact'" as "Hact'".
    (* move rdata 0 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hrdata]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 16|auto..].
    iEpilogue "(HPC & Hi & Hrdata)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 -7 *)
    destruct l;[by inversion Hlength|].
    destruct acta as [| ? acta];[| by inversion Hact_len_a].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=f19) in Hcont_act as Hnext; auto.
    assert ((f19 + (-7))%a = Some act_b) as Hlea.
    { apply contiguous_between_length in Hcont_act. revert Hnext Hact; clear. solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 17|apply Hlea|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* restrict r_t1 (Global,E) *)
    destruct l;[|by inversion Hlength].
    apply contiguous_between_last with (ai:=f22) in Hcont as Hlast; auto.
    iPrologue "Hprog". iClear "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hlast|auto..].
    { rewrite decode_encode_perm_inv. auto. }
    rewrite decode_encode_perm_inv.
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC". iSplitL "Hprog_done".
    { do 21 iDestruct "Hprog_done" as "[$ Hprog_done]". iFrame. done. }
    iFrame. do 7 iDestruct "Hact'" as "[$ Hact']". iFrame.
  Qed.


  (* crtcls spec *)
  (* Lemma crtcls_spec i f_m wvar wcode a pc_p pc_b pc_e *)
  (*       a_first a_last b_link a_link e_link a_entry b_m e_m mallocN γ EN rmap cont φ : *)
  (*   isCorrectPC_range pc_p pc_b pc_e a_first a_last → *)
  (*   contiguous_between a a_first a_last → *)
  (*   withinBounds b_link e_link a_entry = true → *)
  (*   (a_link + f_m)%a = Some a_entry → *)
  (*   dom (gset (CoreN * RegName)) rmap = *)
  (*     ((set_map (fun r=> (i,r)) all_registers_s) ∖ {[ (i, PC); (i, r_t0); (i, r_t1);(i, r_t2) ]}) → *)
  (*   ↑mallocN ⊆ EN → *)

  (*     ▷ crtcls f_m a *)
  (*   ∗ ▷ (i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_first *)
  (*   ∗ inv mallocN (malloc_inv b_m e_m γ) *)
  (*   (* we need to assume that the malloc capability is in the linking table at offset 0 *) *)
  (*   ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link *)
  (*   ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m *)
  (*   (* register state *) *)
  (*   ∗ ▷ (i,r_t0) ↦ᵣ cont *)
  (*   ∗ ▷ (i,r_t1) ↦ᵣ wcode *)
  (*   ∗ ▷ (i,r_t2) ↦ᵣ wvar *)
  (*   ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
  (*   (* continuation *) *)
  (*   ∗ ▷ ((i,PC) ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ crtcls f_m a *)
  (*        ∗ pc_b ↦ₐ WCap RO b_link e_link a_link *)
  (*        ∗ a_entry ↦ₐ WCap E b_m e_m b_m *)
  (*        (* the newly allocated region *) *)
  (*        ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ (i,r_t1) ↦ᵣ WCap E b e b *)
  (*        ∗ [[b,e]] ↦ₐ [[ activation_instrs wcode wvar ]] *)
  (*        ∗ (i,r_t0) ↦ᵣ cont *)
  (*        ∗ (i,r_t2) ↦ᵣ WInt 0%Z *)
  (*        ∗ ([∗ map] r_i↦w_i ∈ <[(i,r_t3):=WInt 0%Z]> *)
  (*                              (<[(i,r_t4):=WInt 0%Z]> *)
  (*                               (<[(i,r_t5):=WInt 0%Z]> *)
  (*                                (<[(i,r_t6):=WInt 0%Z]> *)
  (*                                 (<[(i,r_t7):=WInt 0%Z]> rmap)))), r_i ↦ᵣ w_i)) *)
  (*        -∗ WP (i,Seq (Instr Executable)) @ EN {{ φ }}) *)
  (*   ⊢ *)
  (*     WP (i,Seq (Instr Executable)) @ EN {{ λ v, φ v ∨ ⌜v = (i,FailedV)⌝ }}. *)
  (* Proof. *)
  (*   iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN) *)
  (*           "(>Hprog & >HPC & #Hmalloc & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hφ)". *)
  (*   (* get some registers out of regs *) *)
  (*   iDestruct (big_sepL2_length with "Hprog") as %Hlength. *)
  (*   assert (is_Some (rmap !! (i,r_t6))) as [rv6 ?]. rewrite elem_of_gmap_dom Hrmap_dom; set_solver+. *)
  (*   iDestruct (big_sepM_delete _ _ (i,r_t6) with "Hregs") as "[Hr_t6 Hregs]"; eauto. *)
  (*   assert (is_Some (rmap !! (i,r_t7))) as [rv7 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver+. *)
  (*   iDestruct (big_sepM_delete _ _ (i,r_t7) with "Hregs") as "[Hr_t7 Hregs]". by rewrite lookup_delete_ne //. *)
  (*   destruct a as [|a l];[inversion Hlength|]. *)
  (*   apply contiguous_between_cons_inv_first in Hcont as Heq. subst. *)
  (*   (* move r_t6 r_t1 *) *)
  (*   destruct l;[inversion Hlength|]. *)
  (*   iPrologue "Hprog". *)
  (*   iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1]"); *)
  (*     [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|]. *)
  (*   iEpilogue "(HPC & Hprog_done & Hr_t6 & Hr_t1)". *)
  (*   (* move r_t7 r_t2 *) *)
  (*   destruct l;[inversion Hlength|]. *)
  (*   iPrologue "Hprog". *)
  (*   iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t7 $Hr_t2]"); *)
  (*     [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|]. *)
  (*   iEpilogue "(HPC & Hi & Hr_t7 & Hr_t2)"; iCombine "Hi Hprog_done" as "Hprog_done". *)
  (*   assert (contiguous_between (f0 :: l) f0 a_last) as Hcont'. *)
  (*   { apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)]. *)
  (*     apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)]. *)
  (*     pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst. apply Hcont. } *)
  (*   (* malloc 8 *) *)
  (*   iDestruct (contiguous_between_program_split with "Hprog") as *)
  (*       (malloc_prog rest link) "(Hmalloc_prog & Hprog & #Hcont)";[apply Hcont'|]. *)
  (*   iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink). *)
  (*   (* we start by putting the registers back together *) *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs". *)
  (*   rewrite lookup_delete_ne ; last simplify_pair_eq. *)
  (*   by rewrite lookup_delete. *)
  (*   rewrite delete_commute insert_delete. *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs". *)
  (*   rewrite lookup_insert_ne ; last simplify_pair_eq. *)
  (*   by rewrite lookup_delete. *)
  (*   rewrite (insert_commute _ (i,r_t7) (i,r_t6)) ; last simplify_pair_eq. *)
  (*   rewrite insert_delete. *)
  (*   assert (∀ (r:RegName), *)
  (*             (i,r) ∈ ({[(i,PC);(i,r_t0);(i,r_t1);(i,r_t2)]} : gset (CoreN*RegName)) *)
  (*                          → rmap !! (i, r) = None) as Hnotin_rmap. *)
  (*   { intros r Hr. eapply (@not_elem_of_dom _ _ (gset (CoreN*RegName))). typeclasses eauto. *)
  (*     rewrite Hrmap_dom. set (rmap' := set_map (λ r0 : RegName, (i, r0)) *)
  (*                                        all_registers_s). *)
  (*     admit. } *)
  (*     (* set_solver. } *) *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs". *)
  (*   do 2 (rewrite lookup_insert_ne ; last simplify_pair_eq). *)
  (*     apply Hnotin_rmap ; last set_solver+. *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs". *)
  (*   do 3 (rewrite lookup_insert_ne ; last simplify_pair_eq). *)
  (*     apply Hnotin_rmap ; last set_solver+. *)
  (*   (* apply the malloc spec *) *)
  (*   rewrite -/(malloc _ _ _). *)
  (*   iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr_t0 $Hregs $Hmalloc_prog]"); *)
  (*     [|apply Hcont_fetch|apply Hwb|apply Ha_entry| |auto|lia|..]. *)
  (*   { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. *)
  (*     apply contiguous_between_bounds in Hcont_rest. *)
  (*     apply contiguous_between_incr_addr with (i:=2) (ai:=f0) in Hcont;auto. *)
  (*     revert Hcont Hcont_rest Hmid; clear. solve_addr. } *)
  (*   { rewrite !dom_insert_L. rewrite Hrmap_dom. *)
  (*     clear. *)
  (*     rewrite singleton_union_difference_L. *)
  (*     admit. } *)
  (*     (* set_solver+. *) *)
  (*     (* repeat (rewrite singleton_union_difference_L all_registers_union_l). *) *)
  (*     (* f_equal. clear; set_solver+. } *) *)
  (*   iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_entry & Hbe & Hr_t0 & Hregs)". *)
  (*   iDestruct "Hbe" as (b e Hbe) "(Hr_t1 & Hbe)". *)
  (*   rewrite delete_insert_delete. *)
  (*   rewrite (delete_insert_ne _ (i, r_t1) (i, r_t2)) ; last simplify_pair_eq. *)
  (*   do 7 (rewrite (insert_commute _ _ (i, r_t2)) ; last simplify_pair_eq). *)
  (*   rewrite insert_insert. *)
  (*   iDestruct (big_sepM_delete _ _ (i, r_t6) with "Hregs") as "[Hr_t6 Hregs]". *)
  (*   do 4 (rewrite lookup_insert_ne ; last simplify_pair_eq). *)
  (*   rewrite lookup_insert //. *)
  (*   iDestruct (big_sepM_delete _ _ (i, r_t7) with "Hregs") as "[Hr_t7 Hregs]". *)
  (*   rewrite lookup_delete_ne ; last simplify_pair_eq. *)
  (*   do 5 (rewrite lookup_insert_ne ; last simplify_pair_eq). *)
  (*   rewrite lookup_insert //. *)
  (*   do 8 (rewrite delete_insert_ne ; last simplify_pair_eq) ; []. *)
  (*   rewrite delete_insert_delete. *)
  (*   do 1 (rewrite delete_insert_ne ; last simplify_pair_eq) ; []. *)
  (*   rewrite delete_insert_delete. *)
  (*   do 4 (rewrite delete_insert_ne ; last simplify_pair_eq) ; []. *)
  (*   rewrite (delete_commute _ (i, r_t6)) delete_insert_delete. *)
  (*   do 2 (rewrite (delete_commute _ (i, r_t7))) ; rewrite delete_insert_delete. *)
  (*   iApply (scrtcls_spec with "[- $Hprog $HPC $Hr_t1 $Hr_t6 $Hr_t7 $Hbe]"); eauto. *)
  (*   { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. *)
  (*     apply contiguous_between_bounds in Hcont_rest. *)
  (*     apply contiguous_between_bounds in Hcont_fetch. *)
  (*     apply contiguous_between_incr_addr with (i:=2) (ai:=f0) in Hcont; auto. *)
  (*     revert Hmid Hcont_rest Hcont_fetch Hcont ; clear. solve_addr. } *)
  (*   iNext. iIntros "(HPC & Hscrtcls_prog & Hr_t1 & Hact & Hr_t6 & Hr_t7)". *)
  (*   (* continuation *) *)
  (*   iApply "Hφ". iFrame "HPC Hpc_b Ha_entry". iSplitL "Hprog_done Hmalloc_prog Hscrtcls_prog". *)
  (*   { rewrite Heqapp. iDestruct "Hprog_done" as "[? ?]". iFrame. } *)
  (*   iExists b,e. iSplitR;auto. iFrame. *)
  (*   iDestruct (big_sepM_delete _ _ (i, r_t2) with "Hregs") as "[Hr_t2 Hregs]". *)
  (*     rewrite lookup_insert //. *)
  (*   iFrame "Hr_t2". *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs". *)
  (*   by simpl_map. *)
  (*   iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs". *)
  (*   by simpl_map. *)
  (*   repeat (repeat (rewrite delete_insert_ne ; last simplify_pair_eq; []); rewrite delete_insert_delete). *)
  (*   rewrite (delete_notin _ r_t1). 2: apply Hnotin_rmap; set_solver. *)
  (*   rewrite (delete_notin _ r_t2). 2: rewrite !lookup_delete_ne //; apply Hnotin_rmap; set_solver. *)
  (*   repeat (rewrite -delete_insert_ne //; []). rewrite insert_delete. *)
  (*   repeat (rewrite -delete_insert_ne //; []). rewrite insert_delete. *)
  (*   repeat (rewrite (insert_commute _ r_t7) //;[]). *)
  (*   repeat (rewrite (insert_commute _ r_t6) //;[]). rewrite (insert_commute _ r_t6 r_t5) //. *)
  (* Qed. *)

  (* ------------------------------- Closure Activation --------------------------------- *)

  (* Lemma closure_activation_spec pc_p b_cls e_cls r1v renvv wcode wenv φ : *)
  (*   readAllowed pc_p = true → *)
  (*   isCorrectPC_range pc_p b_cls e_cls b_cls e_cls → *)
  (*   pc_p ≠ E → *)
  (*   PC ↦ᵣ WCap pc_p b_cls e_cls b_cls *)
  (*   ∗ r_t1 ↦ᵣ r1v *)
  (*   ∗ r_env ↦ᵣ renvv *)
  (*   ∗ [[b_cls, e_cls]]↦ₐ[[ activation_instrs wcode wenv ]] *)
  (*   ∗ (  PC ↦ᵣ updatePcPerm wcode *)
  (*      ∗ r_t1 ↦ᵣ wcode *)
  (*      ∗ r_env ↦ᵣ wenv *)
  (*      ∗ [[b_cls, e_cls]]↦ₐ[[ activation_instrs wcode wenv ]] *)
  (*      -∗ WP Seq (Instr Executable) {{ φ }}) *)
  (*   ⊢ *)
  (*     WP Seq (Instr Executable) {{ φ }}. *)
  (* Proof. *)
  (*   iIntros (Hrpc Hvpc HnpcE) "(HPC & Hr1 & Hrenv & Hcls & Hcont)". *)
  (*   rewrite /region_mapsto. *)
  (*   iDestruct (big_sepL2_length with "Hcls") as %Hcls_len. simpl in Hcls_len. *)
  (*   assert (b_cls + 8 = Some e_cls)%a as Hbe. *)
  (*   { rewrite finz_seq_between_length /finz.dist in Hcls_len. *)
  (*     revert Hcls_len; clear; solve_addr. } *)
  (*   assert (contiguous_between (finz.seq_between b_cls e_cls) b_cls e_cls) as Hcont_cls. *)
  (*   { apply contiguous_between_of_region_addrs; auto. revert Hbe; clear; solve_addr. } *)
  (*   pose proof (finz_seq_between_NoDup b_cls e_cls) as Hcls_nodup. *)
  (*   iDestruct (big_sepL2_split_at 6 with "Hcls") as "[Hcls_code Hcls_data]". *)
  (*   cbn [take drop]. *)
  (*   destruct (finz.seq_between b_cls e_cls) as [| ? ll]; [by inversion Hcls_len|]. *)
  (*   pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_cls). subst. *)
  (*   do 7 (destruct ll as [| ? ll]; [by inversion Hcls_len|]). *)
  (*   destruct ll;[| by inversion Hcls_len]. cbn [take drop]. *)
  (*   iDestruct "Hcls_data" as "(Hcls_ptr & Hcls_env & _)". *)
  (*   (* move r_t1 PC *) *)
  (*   iPrologue "Hcls_code". *)
  (*   iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]"); *)
  (*     [apply decode_encode_instrW_inv| iCorrectPC b_cls e_cls | *)
  (*      iContiguous_next Hcont_cls 0 |..]. *)
  (*   iEpilogue "(HPC & Hprog_done & Hr1)". *)
  (*   (* lea r_t1 7 *) *)
  (*   iPrologue "Hprog". *)
  (*   iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]"); *)
  (*     [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | *)
  (*      iContiguous_next Hcont_cls 1 | | done | ..]. *)
  (*   { eapply contiguous_between_incr_addr_middle' with (i:=0); eauto. *)
  (*     cbn. clear. lia. } *)
  (*   iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done". *)
  (*   (* load r_env r_t1 *) *)
  (*   iPrologue "Hprog". *)
  (*   (* FIXME: tedious & fragile *) *)
  (*   assert ((f5 =? f0)%a = false) as H_5_0. *)
  (*   { apply Z.eqb_neq. intros Heqb. assert (f5 = f0) as ->. revert Heqb; clear; solve_addr. *)
  (*     exfalso. by pose proof (NoDup_lookup _ 2 7 _ Hcls_nodup eq_refl eq_refl). } *)
  (*   iApply (wp_load_success with "[$HPC $Hi $Hrenv $Hr1 Hcls_env]"); *)
  (*     [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | *)
  (*      split;[done|] | iContiguous_next Hcont_cls 2 | ..]. *)
  (*   { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?]. *)
  (*     by eapply le_addr_withinBounds; eauto. repeat constructor. } *)
  (*   { rewrite H_5_0. iFrame. } *)
  (*   iEpilogue "(HPC & Hrenv & Hi & Hr1 & Hcls_env)". rewrite H_5_0. *)
  (*   iCombine "Hi Hprog_done" as "Hprog_done". *)
  (*   (* lea r_t1 (-1) *) *)
  (*   iPrologue "Hprog". *)
  (*   iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]"); *)
  (*     [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | *)
  (*      iContiguous_next Hcont_cls 3 | | done | ..]. *)
  (*   { assert ((f4 + 1)%a = Some f5) as HH. by iContiguous_next Hcont_cls 6. *)
  (*     instantiate (1 := f4). revert HH. clear; solve_addr. } *)
  (*   iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done". *)
  (*   (* load r_t1 r_t1 *) *)
  (*   iPrologue "Hprog". *)
  (*   (* FIXME: tedious & fragile *) *)
  (*   assert ((f4 =? f2)%a = false) as H_4_2. *)
  (*   { apply Z.eqb_neq. intros Heqb. assert (f4 = f2) as ->. revert Heqb; clear; solve_addr. *)
  (*     exfalso. by pose proof (NoDup_lookup _ 4 6 _ Hcls_nodup eq_refl eq_refl). } *)
  (*   iApply (wp_load_success_same with "[$HPC $Hi $Hr1 Hcls_ptr]"); *)
  (*     [(* FIXME *) auto | apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | *)
  (*      done | auto | iContiguous_next Hcont_cls 4 | ..]. *)
  (*   { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?]. *)
  (*     by eapply le_addr_withinBounds; eauto. repeat constructor. } *)
  (*   { rewrite H_4_2. iFrame. } *)
  (*   iEpilogue "(HPC & Hr1 & Hi & Hcls_ptr)". rewrite H_4_2. *)
  (*   iCombine "Hi Hprog_done" as "Hprog_done". *)
  (*   (* jmp r_t1 *) *)
  (*   iPrologue "Hprog". *)
  (*   iApply (wp_jmp_success with "[$HPC $Hi $Hr1]"); *)
  (*     [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | .. ]. *)
  (*   iEpilogue "(HPC & Hi & Hr1)". *)

  (*   iApply "Hcont". do 4 (iDestruct "Hprog_done" as "(? & Hprog_done)"). iFrame. *)
  (* Qed. *)

End macros.
