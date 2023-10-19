From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_binary logrel.
From cap_machine.proofmode Require Import tactics_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous malloc_binary.
From cap_machine Require Import macros.

(** This file contains specification side specs for macros. Malloc, and the first
    part of crtclosure is written out as a binary specification, since malloc must
    happen in lock step
 *)

Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.


  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)


  Definition fetch_s f a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(fetch_instrs f), a_i ↣ₐ w_i)%I.

  Lemma fetch_s_spec E f a pc_p pc_b pc_e a_first a_last b_link e_link a_link entry_a wentry w1 w2 w3:
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->
    nclose specN ⊆ E →

      ▷ fetch_s f a
    ∗ spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↣ₐ WCap RO b_link e_link a_link
    ∗ ▷ entry_a ↣ₐ wentry
    ∗ ▷ r_t1 ↣ᵣ w1
    ∗ ▷ r_t2 ↣ᵣ w2
    ∗ ▷ r_t3 ↣ᵣ w3
      ={E}=∗ ⤇ Seq (Instr Executable)
          ∗ PC ↣ᵣ WCap pc_p pc_b pc_e a_last ∗ fetch_s f a
          ∗ r_t1 ↣ᵣ wentry ∗ r_t2 ↣ᵣ WInt 0%Z ∗ r_t3 ↣ᵣ WInt 0%Z
          ∗ pc_b ↣ₐ WCap RO b_link e_link a_link
          ∗ entry_a ↣ₐ wentry.

  Proof.
    iIntros (Hvpc Hcont Hwb Hentry Hnclose) "(>Hprog & #Hspec & Hj & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t1 PC *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hprog_done & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|..].
    iEpilogue_s.
    (* getb r_t2 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t1 & Hr_t2)";
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t3 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Hr_t3]")
      as "(Hj & HPC & Hi & Hr_t1 & Hr_t3)";
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t2 r_t3 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_add_sub_lt_success_dst_r _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t3 $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t3 & Hr_t2)";
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 3|iCorrectPC a_first a_last|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 r_t2 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    assert ((a_first + (pc_b - a_first))%a = Some pc_b) as Hlea;[solve_addr|].
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t2 & Hr_t1) /=";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | ->]; auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_load_success_same_alt _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 Hpc_b]")
      as "(Hj & HPC & Hr_t1 & Hi & Hpc_b)";
      [|apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 5|auto..].
    { exact (WCap RW b_link e_link a_link). }
    { apply contiguous_between_length in Hcont as Hlen.
      assert (pc_b < pc_e)%Z as Hle.
      { eapply isCorrectPC_contiguous_range in Hvpc as Hwb';[|eauto|apply elem_of_cons;left;eauto].
        inversion Hwb'. solve_addr. }
      apply isCorrectPC_range_perm in Hvpc as Heq; [|revert Hlen; clear; solve_addr].
      split;[destruct Heq as [-> | ->]; auto|].
      apply andb_true_intro. split;[apply Z.leb_le;solve_addr|apply Z.ltb_lt;auto].
    }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 f *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hentry|simpl;auto..].
    iEpilogue_s ; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|auto|..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t3]")
      as "(Hj & HPC & Hi & Hr_t3)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|auto|..].
    iEpilogue_s ; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[|inversion Hlength].
    apply contiguous_between_last with (ai:=f8) in Hcont as Hlink;[|auto].
    iPrologue_s "Hprog".
    iMod (step_load_success_same_alt _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha_entry]")
      as "(Hj & HPC & Hr_t1 & Hi & Hentry_a)";
      [exact wentry|apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|apply Hlink|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* macro is done *)
    iFrame. do 9 iDestruct "Hprog_done" as "[$ Hprog_done]". by iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition malloc_s f_m size a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(malloc_instrs f_m size), a_i ↣ₐ w_i)%I.

  (* malloc spec *)
  Lemma malloc_s_spec φ size cont cont'
        a pc_p pc_b pc_e a_first a_last
        a' pcs_p pcs_b pcs_e s_first s_last
        b_link e_link a_link f_m a_entry
        bs_link es_link as_link fs_m as_entry
        mallocN b_m e_m EN
        rmap smap :

    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last →
    contiguous_between a a_first a_last →
    contiguous_between a' s_first s_last →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →

    withinBounds bs_link es_link as_entry = true →
    (as_link + fs_m)%a = Some as_entry →

    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    dom smap = all_registers_s ∖ {[ PC; r_t0 ]} →

    ↑mallocN ⊆ EN →
    nclose specN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a ∗ ▷ malloc_s fs_m size a'
    ∗ spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ na_inv logrel_nais mallocN (malloc_inv_binary b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ ▷ pcs_b ↣ₐ WCap RO bs_link es_link as_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m ∗ ▷ as_entry ↣ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ ▷ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
    ∗ ▷ r_t0 ↦ᵣ cont ∗ ▷ r_t0 ↣ᵣ cont'
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) ∗ ▷ ([∗ map] r_i↦w_i ∈ smap, r_i ↣ᵣ w_i)
    (* continuation *)
    ∗ ▷ (⤇ Seq (Instr Executable) ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_last
         ∗ malloc f_m size a ∗ malloc_s fs_m size a'
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ pcs_b ↣ₐ WCap RO bs_link es_link as_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m ∗ as_entry ↣ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ WCap RWX b e b ∗ r_t1 ↣ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]] ∗ [[b,e]] ↣ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont ∗ r_t0 ↣ᵣ cont'
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 smap))))), r_i ↣ᵣ w_i)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hwb1 Ha_entry Hwb2 Has_entry Hrmap_dom Hsmap_dom HmallocN HspecN Hsize)
            "(>Hprog & >Hsprog & #Hspec & Hj & #Hmalloc & Hna
            & >Hpc_b & >Hpcs_b & >Ha_entry & >Hs_entry & >HPC & > HsPC
            & >Hr_t0 & >Hs_t0 & >Hregs & >Hsegs & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    iDestruct (big_sepL2_length with "Hsprog") as %Hslength.

    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.

    assert (is_Some (smap !! r_t1)) as [sv1 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hsegs") as "[Hs_t1 Hsegs]"; eauto.
    assert (is_Some (smap !! r_t2)) as [sv2 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hsegs") as "[Hs_t2 Hsegs]". by rewrite lookup_delete_ne //.
    assert (is_Some (smap !! r_t3)) as [sv3 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hsegs") as "[Hs_t3 Hsegs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (smap !! r_t5)) as [sv5 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hsegs") as "[Hs_t5 Hsegs]". by rewrite !lookup_delete_ne //.

    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst.
    destruct a' as [|a' ls];[inversion Hslength|].
    apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst.
    (* fetch f : impl *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont1|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb1|apply Ha_entry|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* fetch f : spec *)
    iDestruct (contiguous_between_program_split with "Hsprog") as (fetch_progs rests links)
                                                                   "(Hfetchs & Hsprog & #Hcont)";[apply Hcont2|].
    iDestruct "Hcont" as %(Hcont_fetchs & Hcont_rests & Heqapps & Hlinks).
    iMod (fetch_s_spec with "[$Hspec $Hj $HsPC $Hfetchs $Hs_t1 $Hs_t2 $Hs_t3 $Hs_entry $Hpcs_b]")
      as "(Hj & HsPC & Hfetchs & Hs_t1 & Hs_t2 & Hs_t3 & Hpcs_b & Hs_entry)";
      [|apply Hcont_fetchs|apply Hwb2|apply Has_entry|auto..].
    { intros mid Hmid. apply isCorrectPC_inrange with s_first s_last; auto.
      apply contiguous_between_bounds in Hcont_rests. revert Hcont_rests Hmid; clear. solve_addr. }
    iDestruct (big_sepL2_length with "Hsprog") as %Hlength_rests.
    assert (isCorrectPC_range pcs_p pcs_b pcs_e links s_last) as Hvpc_rests.
    { intros mid Hmid. apply isCorrectPC_inrange with s_first s_last; auto. revert Hmid Hlinks;clear. solve_addr. }
    destruct rests as [|a ls'];[inversion Hlength_rests|].
    apply contiguous_between_cons_inv_first in Hcont_rests as Heq. subst.
    (* move r_t5 r_t0 *)
    destruct l';[inversion Hlength_rest|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t5 $Hs_t0]")
      as "(Hj & HsPC & Hsprog_done & Hs_t5 & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 0|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue_both "(HPC & Hprog_done & Hr_t5 & Hr_t0)".
    iCombine "Hprog_done" "Hfetch" as "Hprog_done".
    iCombine "Hsprog_done" "Hfetchs" as "Hsprog_done".
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t3 $Hs_t1]")
      as "(Hj & HsPC & Hsi & Hs_t3 & Hs_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 1|auto..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue_both "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombinePtrn.
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t1]")
      as "(Hj & HsPC & Hsi & Hs_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 2|auto|..].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue_both "(HPC & Hi & Hr_t1)"; iCombinePtrn.
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
      as "(Hj & HsPC & Hsi & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 3|auto|..].
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue_both "(HPC & Hi & Hr_t0)"; iCombinePtrn.
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    destruct ls';[inversion Hlength_rests|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    assert ((f3 + 3)%a = Some f8) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f3 f8) in Hcont_rest; auto. }
    assert ((f4 + 3)%a = Some f10) as Hlea'.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f4 f10) in Hcont_rests; auto. }
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
      as "(Hj & HsPC & Hsi & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 4|apply Hlea'|auto..].
    { apply contiguous_between_length in Hcont2.
      apply isCorrectPC_range_perm in Hvpc2; [|revert Hcont2; clear; solve_addr].
      destruct Hvpc2 as [-> | -> ]; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont1.
      apply isCorrectPC_range_perm in Hvpc1; [|revert Hcont1; clear; solve_addr].
      destruct Hvpc1 as [-> | -> ]; auto. }
    iEpilogue_both "(HPC & Hi & Hr_t0)"; iCombinePtrn.
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|]. destruct ls';[inversion Hlength_rests|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t3]")
      as "(Hj & HsPC & Hsi & Hs_t3)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|auto|].
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue_both "(HPC & Hi & Hr_t3) /="; iCombinePtrn.
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs";[by rewrite lookup_delete_ne // lookup_delete|].
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hsegs $Hs_t3]") as "Hsegs";[by rewrite lookup_delete_ne // lookup_delete|].
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete_ne // lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hsegs $Hs_t2]") as "Hsegs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete_ne // lookup_delete.

    rewrite - !(delete_insert_ne _ r_t5 r_t3) // !insert_delete_insert.
    rewrite - !(delete_insert_ne _ r_t5 r_t2) // !(insert_commute _ r_t2 r_t3) //.
    rewrite !insert_delete_insert.

    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by rewrite lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hsegs $Hs_t5]") as "Hsegs".
      by rewrite lookup_delete. rewrite !insert_delete_insert.

    iApply (wp_wand with "[-]").
    iApply (malloc_binary.simple_malloc_subroutine_spec with "[- $Hspec $Hj $Hmalloc $Hna $Hregs $Hsegs $Hr_t0 $Hs_t0 $HPC $HsPC $Hr_t1 $Hs_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite !difference_difference_l_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. }
    { rewrite !dom_insert_L dom_delete_L Hsmap_dom.
      rewrite !difference_difference_l_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. }
    (* { lia. } *)
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rests). cbn.
         clear; solve_addr. }

    iIntros "(Hna & Hregs & Hr_t0 & HPC & Hsegs & Hs_t0 & HsPC & Hj & Hbe) /=".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hs_t1 & Hbe & Hsbe)". inversion Hsize'; subst size'.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      by rewrite lookup_insert_ne // lookup_insert //.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hsegs") as "[Hs_t3 Hsegs]".
      by rewrite lookup_insert_ne // lookup_insert //.
    rewrite !(delete_insert_ne _ _ r_t2) // !delete_insert_delete.
    repeat (rewrite delete_insert_ne;[|done]). rewrite delete_insert_delete.
    repeat (rewrite (delete_insert_ne);[|done]). rewrite delete_insert_delete (delete_insert_ne _ r_t3)//.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      by (repeat (rewrite lookup_insert_ne //;[]); rewrite lookup_insert //).
    iDestruct (big_sepM_delete _ _ r_t5 with "Hsegs") as "[Hs_t5 Hsegs]".
      by (repeat (rewrite lookup_insert_ne //;[]); rewrite lookup_insert //).
    repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete.
    repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete (delete_insert_ne _ r_t5) //.

    (* move r_t0 r_t5 *)
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0 $Hs_t5]")
      as "(Hj & HsPC & Hsi & Hs_t0 & Hs_t5)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|iContiguous_next Hcont_rests 6|auto|..].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue_both "(HPC & Hi & Hr_t0 & Hr_t5)"; iCombinePtrn.
    (* move r_t5 0 *)
    destruct l';[| by inversion Hlength_rest]. destruct ls';[| by inversion Hlength_rests].
    iPrologue_both "Hprog" "Hsprog".
    apply contiguous_between_last with (ai:=f11) in Hcont_rest as Hlast;[|auto].
    apply contiguous_between_last with (ai:=f12) in Hcont_rests as Hlast';[|auto].
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t5]")
      as "(Hj & HsPC & Hsi & Hs_t5)";
      [apply decode_encode_instrW_inv|iCorrectPC links s_last|apply Hlast'|auto|..].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue_both "(HPC & Hi & Hr_t5)"; iCombinePtrn.
    (* continuation *)
    iApply "Hφ".
    iFrame "HsPC HPC Hj". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iSplitL "Hsprog_done".
    { rewrite Heqapps. repeat (iDestruct "Hsprog_done" as "[$ Hsprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
    repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hsegs $Hs_t5]") as "Hsegs".
    repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete.

    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
    repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hsegs $Hs_t3]") as "Hsegs".
    repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //.

    repeat (rewrite (insert_commute _ r_t5) //;[]).
    rewrite !insert_delete_insert - !(delete_insert_ne _ _ r_t5) //.
    rewrite !(insert_commute _ r_t4 r_t2) // !insert_insert.
    repeat (rewrite -(delete_insert_ne _ r_t3);[|done]); rewrite insert_delete_insert.
    repeat (rewrite -(delete_insert_ne _ r_t3);[|done]); rewrite insert_delete_insert.
    iFrame.
    iExists b,e. iFrame. auto. auto.
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition rclear_s (a : list Addr) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↣ₐ w_i)%I.

  Lemma rclear_s_spec E (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p b e a1 an :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p b e a1 an →
    list_to_set r = dom rmap →
     nclose specN ⊆ E →

     spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↣ᵣ w_i)
    ∗ ▷ PC ↣ᵣ WCap p b e a1
    ∗ ▷ rclear_s a r
     ={E}=∗ ⤇ Seq (Instr Executable)
         ∗ PC ↣ᵣ WCap p b e an
         ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↣ᵣ WInt 0%Z)
         ∗ rclear_s a r.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hrdom Hnclose) "(#Hspec & Hj & >Hreg & >HPC & >Hrclear)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    rewrite /rclear_s /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! r)) as [rv ?].
    { rewrite -elem_of_dom -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hr $Ha1]")
      as "(Hj & HPC & Ha1 & Hr)";
      [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|auto..].
    iEpilogue_s.
    destruct a.
    { iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ r). eauto.
      rewrite (_: delete r rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset RegName)).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete_insert.
      (* iCombine "Ha1" "Hrclear" as "Hrclear". *) iSimpl. iFrame "Ha1".
      iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. }
      { iApply (big_sepM_delete _ _ r). eauto.
        iDestruct (big_sepM_delete _ _ r with "Hregs") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. } }
    { iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. }
      iApply (big_sepM_delete _ _ r). eauto. iFrame. done.
    }
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* --------------------------------------- CRTCLS ---------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition scrtcls_s rcode rdata a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(scrtcls_instrs rcode rdata), a_i ↣ₐ w_i)%I.

  Definition crtcls_s f_m a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(crtcls_instrs f_m), a_i ↣ₐ w_i)%I.

  Lemma scrtcls_s_spec Ep rcode rdata wvar wcode a pc_p pc_b pc_e a_first a_last
        act_b act_e act :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (act_b + 8)%a = Some act_e →
    nclose specN ⊆ Ep →

    spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ scrtcls_s rcode rdata a
    ∗ ▷ PC ↣ᵣ WCap pc_p pc_b pc_e a_first
    (* register state *)
    ∗ ▷ r_t1 ↣ᵣ WCap RWX act_b act_e act_b
    ∗ ▷ rcode ↣ᵣ wcode
    ∗ ▷ rdata ↣ᵣ wvar
    (* memory for the activation record *)
    ∗ ▷ ([[act_b,act_e]] ↣ₐ [[ act ]])
    (* continuation *)
    ={Ep}=∗ ⤇ Seq (Instr Executable)
        ∗ PC ↣ᵣ WCap pc_p pc_b pc_e a_last
        ∗ scrtcls_s rcode rdata a
        ∗ r_t1 ↣ᵣ WCap E act_b act_e act_b
        ∗ [[act_b,act_e]] ↣ₐ [[ activation_instrs wcode wvar ]]
        ∗ rcode ↣ᵣ WInt 0%Z
        ∗ rdata ↣ᵣ WInt 0%Z.
  Proof.
    iIntros (Hvpc Hcont Hact Hnclose) "(#Hspec & Hj & >Hprog & >HPC & >Hr_t1 & >Hrcode & >Hrdata & >Hact)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (act_b < act_e)%a as Hlt;[solve_addr|].
    opose proof (contiguous_between_region_addrs act_b act_e _) as Hcont_act; first solve_addr.
    unfold region_mapsto_spec.
    remember (finz.seq_between act_b act_e) as acta.
    assert (Hact_len_a : length acta = 8).
    { rewrite Heqacta finz_seq_between_length. by apply finz_incr_iff_dist. }
    iDestruct (big_sepL2_length with "Hact") as %Hact_len.
    rewrite Hact_len_a in Hact_len. symmetry in Hact_len.
    repeat (destruct act as [| ? act]; try by inversion Hact_len). clear Hact_len.
    destruct a as [|a l]; [inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    assert (∀ i a', acta !! i = Some a' → withinBounds act_b act_e a' = true) as Hwbact.
    { intros i a' Hsome. apply andb_true_intro. subst acta.
      apply contiguous_between_incr_addr with (i:=i) (ai:=a') in Hcont_act. 2: done.
      apply lookup_lt_Some in Hsome. split;[apply Z.leb_le|apply Z.ltb_lt]; solve_addr. }
    (* store_z r_t1 v1 *)
    destruct l; [inversion Hlength|].
    destruct acta as [| a0 acta]; [inversion Hact_len_a|].
    assert (a0 = act_b) as ->.
    { opose proof (finz_seq_between_first act_b act_e _) as HH; first solve_addr.
      rewrite -Heqacta /= in HH. by inversion HH. }
    iDestruct "Hact" as "[Ha0 Hact]".
    iPrologue_s "Hprog".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Ha0 $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1 & Hact')";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    { split; auto. apply Hwbact with 0. auto. }
    iEpilogue_s; iRename "Hi" into "Hprog_done".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| a1 acta]; [inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|
       iContiguous_next Hcont_act 0|simpl;auto..].
    iEpilogue_s ; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v2 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha1 Hact]".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha1]")
      as "(Hj & HPC & Hi & Hr_t1 & Ha1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto..].
    { split;auto. apply Hwbact with 1. auto. }
    iEpilogue_s ; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha1" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|
       iContiguous_next Hcont_act 1|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v3 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha2 Hact]".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha2]")
      as "(Hj & HPC & Hi & Hr_t1 & Ha2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    { split;auto. apply Hwbact with 2. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha2" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|
       iContiguous_next Hcont_act 2|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v4 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha3 Hact]".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha3]")
      as "(Hj & HPC & Hi & Hr_t1 & Ha3)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|auto..].
    { split;auto. apply Hwbact with 3. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha3" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|
       iContiguous_next Hcont_act 3|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v5 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha4 Hact]".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha4]")
      as "(Hj & HPC & Hi & Hr_t1 & Ha4)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|auto..].
    { split;auto. apply Hwbact with 4. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha4" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|
       iContiguous_next Hcont_act 4|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store_z r_t1 v6 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha5 Hact]".
    iMod (step_store_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Ha5]")
    as "(Hj & HPC & Hi & Hr_t1 & Ha5)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 10|auto..].
    { split;auto. apply Hwbact with 5. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha5" "Hact'" as "Hact'".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 11|
       iContiguous_next Hcont_act 5|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 rcode *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha6 Hact]".
    iMod (step_store_success_reg _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Ha6 $Hrcode $Hr_t1]")
      as "(Hj & HPC & Hi & Hrcode & Hr_t1 & Ha6)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 12|auto..].
    { split;auto. apply Hwbact with 6. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha6" "Hact'" as "Hact'".
    (* move rcode 0 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hrcode]")
      as "(Hj & HPC & Hi & Hrcode)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 13|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 1 *)
    destruct l;[inversion Hlength|].
    destruct acta as [| ? acta];[inversion Hact_len_a|].
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 14|
       iContiguous_next Hcont_act 6|simpl;auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 rdata *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iDestruct "Hact" as "[Ha7 Hact]".
    iMod (step_store_success_reg _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Ha7 $Hrdata $Hr_t1]")
      as "(Hj & HPC & Hi & Hrdata & Hr_t1 & Ha7)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 15|auto..].
    { split;auto. apply Hwbact with 7. auto. }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Ha7" "Hact'" as "Hact'".
    (* move rdata 0 *)
    destruct l;[inversion Hlength|].
    iPrologue_s "Hprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hrdata]")
      as "(Hj & HPC & Hi & Hrdata)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 16|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 -7 *)
    destruct l;[by inversion Hlength|].
    destruct acta as [| ? acta];[| by inversion Hact_len_a].
    iPrologue_s "Hprog".
    apply contiguous_between_last with (ai:=f19) in Hcont_act as Hnext; auto.
    assert ((f19 + (-7))%a = Some act_b) as Hlea.
    { apply contiguous_between_length in Hcont_act. revert Hnext Hact; clear. solve_addr. }
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 17|apply Hlea|simpl;auto..].
    iEpilogue_s;iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* restrict r_t1 (Global,E) *)
    destruct l;[|by inversion Hlength].
    apply contiguous_between_last with (ai:=f22) in Hcont as Hlast; auto.
    iPrologue_s "Hprog". iClear "Hprog".
    iMod (step_restrict_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hlast|auto..].
    { rewrite decode_encode_perm_inv. auto. }
    rewrite decode_encode_perm_inv.
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iFrame "HPC Hj". iSplitL "Hprog_done".
    { do 18 iDestruct "Hprog_done" as "[$ Hprog_done]". iFrame. iModIntro. done. }
    iFrame. do 7 iDestruct "Hact'" as "[$ Hact']". by iFrame.
  Qed.

  (* The full crt closure spec must be a binary spec, since we must invoke malloc in lockstep *)
  (* crtcls spec *)
  Lemma crtcls_spec
        wvar wcode wvar' wcode' (* the environment and code capabilities can be different! *)
        a pc_p pc_b pc_e a_first a_last
        a' pcs_p pcs_b pcs_e s_first s_last
        f_m b_link a_link e_link a_entry
        fs_m bs_link as_link es_link as_entry
        b_m e_m mallocN EN
        rmap smap
        cont cont' φ :

    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    isCorrectPC_range pcs_p pcs_b pcs_e s_first s_last →
    contiguous_between a a_first a_last →
    contiguous_between a' s_first s_last →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →

    withinBounds bs_link es_link as_entry = true →
    (as_link + fs_m)%a = Some as_entry →

    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    dom smap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →

    ↑mallocN ⊆ EN →
    nclose specN ⊆ EN →

    spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ crtcls f_m a ∗ ▷ crtcls_s fs_m a'
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first ∗ ▷ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_first
    ∗ na_inv logrel_nais mallocN (malloc_inv_binary b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ ▷ pcs_b ↣ₐ WCap RO bs_link es_link as_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m ∗ ▷ as_entry ↣ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont ∗ ▷ r_t0 ↣ᵣ cont'
    ∗ ▷ r_t1 ↦ᵣ wcode ∗ ▷ r_t1 ↣ᵣ wcode'
    ∗ ▷ r_t2 ↦ᵣ wvar ∗ ▷ r_t2 ↣ᵣ wvar'
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ smap, r_i ↣ᵣ w_i)
    (* continuation *)
    ∗ ▷ (⤇ Seq (Instr Executable)
         ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ crtcls f_m a
         ∗ PC ↣ᵣ WCap pcs_p pcs_b pcs_e s_last ∗ crtcls_s fs_m a'
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ pcs_b ↣ₐ WCap RO bs_link es_link as_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m ∗ as_entry ↣ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ WCap E b e b ∗ r_t1 ↣ᵣ WCap E b e b (* the created capabilities will be syntactically identical *)
         ∗ [[b,e]] ↦ₐ [[ activation_instrs wcode wvar ]]
         ∗ [[b,e]] ↣ₐ [[ activation_instrs wcode' wvar' ]]
         ∗ r_t0 ↦ᵣ cont ∗ r_t0 ↣ᵣ cont'
         ∗ r_t2 ↦ᵣ WInt 0%Z ∗ r_t2 ↣ᵣ WInt 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=WInt 0%Z]>
                               (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]>
                                 (<[r_t6:=WInt 0%Z]>
                                  (<[r_t7:=WInt 0%Z]> rmap)))), r_i ↦ᵣ w_i)
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=WInt 0%Z]>
                               (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]>
                                 (<[r_t6:=WInt 0%Z]>
                                  (<[r_t7:=WInt 0%Z]> smap)))), r_i ↣ᵣ w_i))
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc1 Hvpc2 Hcont1 Hcont2 Hwb Ha_entry Hwb' Ha_entry' Hrmap_dom Hsmap_dom HmallocN HspecN)
            "(#Hspec & Hj & >Hprog & >Hsprog & >HPC & >HsPC
            & #Hmalloc & Hna & >Hpc_b & >Hpcs_b & >Ha_entry & >Has_entry
            & >Hr_t0 & >Hs_t0 & >Hr_t1 & >Hs_t1 & >Hr_t2 & >Hs_t2 & >Hregs & >Hsegs & Hφ)".
    (* get some registers out of regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    iDestruct (big_sepL2_length with "Hsprog") as %Hlengths.
    assert (is_Some (rmap !! r_t6)) as [rv6 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    assert (is_Some (smap !! r_t6)) as [sv6 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]"; eauto.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hsegs") as "[Hs_t6 Hsegs]"; eauto.
    assert (is_Some (rmap !! r_t7)) as [rv7 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    assert (is_Some (smap !! r_t7)) as [sv7 ?]. by rewrite -elem_of_dom Hsmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]". by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hsegs") as "[Hs_t7 Hsegs]". by rewrite lookup_delete_ne //.

    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont1 as Heq. subst.
    destruct a' as [|a' ls];[inversion Hlengths|].
    apply contiguous_between_cons_inv_first in Hcont2 as Heq. subst.
    (* move r_t6 r_t1 *)
    destruct l;[inversion Hlength|]. destruct ls;[inversion Hlengths|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t6 $Hs_t1]")
      as "(Hj & HsPC & Hsprog_done & Hs_t6 & Hs_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 0|auto|].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 0|].
    iEpilogue_both "(HPC & Hprog_done & Hr_t6 & Hr_t1)".
    (* move r_t7 r_t2 *)
    destruct l;[inversion Hlength|]. destruct ls;[inversion Hlengths|].
    iPrologue_both "Hprog" "Hsprog".
    iMod (step_move_success_reg _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t7 $Hs_t2]")
      as "(Hj & HsPC & Hsi & Hs_t7 & Hs_t2)";
      [apply decode_encode_instrW_inv|iCorrectPC s_first s_last|iContiguous_next Hcont2 1|auto|].
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t7 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont1 1|].
    iEpilogue_both "(HPC & Hi & Hr_t7 & Hr_t2)"; iCombinePtrn.
    assert (contiguous_between (f1 :: l) f1 a_last) as Hcont'.
    { apply contiguous_between_cons_inv in Hcont1 as [_ (? & ? & Hcont1)].
      apply contiguous_between_cons_inv in Hcont1 as [_ (? & ? & Hcont1)].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont1). subst. apply Hcont1. }
    assert (contiguous_between (f2 :: ls) f2 s_last) as Hcont''.
    { apply contiguous_between_cons_inv in Hcont2 as [_ (? & ? & Hcont2)].
      apply contiguous_between_cons_inv in Hcont2 as [_ (? & ? & Hcont2)].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont2). subst. apply Hcont2. }
    (* malloc 8 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest link) "(Hmalloc_prog & Hprog & #Hcont)";[apply Hcont'|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iDestruct (contiguous_between_program_split with "Hsprog") as
        (malloc_progs rests links) "(Hmalloc_sprog & Hsprog & #Hscont)";[apply Hcont''|].
    iDestruct "Hscont" as %(Hcont_fetchs & Hcont_rests & Heqapps & Hlinks).
    (* we start by putting the registers back together *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs".
      by rewrite lookup_delete_ne // lookup_delete.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t6]") as "Hsegs".
      by rewrite lookup_delete_ne // lookup_delete.
    rewrite !(delete_commute _ r_t7) // !insert_delete_insert.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t7]") as "Hsegs".
      by rewrite lookup_insert_ne // lookup_delete.
    rewrite !(insert_commute _ r_t7) // !insert_delete_insert.
    assert (∀ (r:RegName), r ∈ ({[PC;r_t0;r_t1;r_t2]} : gset RegName) → rmap !! r = None) as Hnotin_rmap.
    { intros r Hr. eapply (@not_elem_of_dom _ _ (gset RegName)). typeclasses eauto.
      rewrite Hrmap_dom. clear -Hr Hrmap_dom. set_solver. }
    assert (∀ (r:RegName), r ∈ ({[PC;r_t0;r_t1;r_t2]} : gset RegName) → smap !! r = None) as Hnotin_smap.
    { intros r Hr. eapply (@not_elem_of_dom _ _ (gset RegName)). typeclasses eauto.
      rewrite Hsmap_dom. clear -Hr Hsmap_dom. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t2]") as "Hsegs".
      by rewrite !lookup_insert_ne //; apply Hnotin_smap; set_solver.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t1]") as "Hsegs".
      by rewrite !lookup_insert_ne //; apply Hnotin_smap; set_solver.
    (* apply the malloc spec *)
    rewrite -/(malloc _ _ _).
    iApply (malloc_s_spec with "[- $Hspec $Hj $HPC $HsPC $Hmalloc $Hna $Hpc_b $Hpcs_b $Ha_entry $Has_entry
     $Hr_t0 $Hs_t0 $Hregs $Hsegs $Hmalloc_prog $Hmalloc_sprog]");
      [| |apply Hcont_fetch|apply Hcont_fetchs|apply Hwb|apply Ha_entry|apply Hwb'|apply Ha_entry'| | |auto|auto|clear;lia|..].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest.
      apply contiguous_between_incr_addr with (i:=2) (ai:=f1) in Hcont1;auto.
      revert Hcont1 Hcont_rest Hmid; clear. solve_addr. }
    { intros mid Hmid. apply isCorrectPC_inrange with s_first s_last; auto.
      apply contiguous_between_bounds in Hcont_rests.
      apply contiguous_between_incr_addr with (i:=2) (ai:=f2) in Hcont2;auto.
      revert Hcont2 Hcont_rests Hmid; clear. solve_addr. }
    { rewrite !dom_insert_L. rewrite Hrmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. }
    { rewrite !dom_insert_L. rewrite Hsmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. }
    iNext. iIntros "(Hj & HPC & HsPC & Hmalloc_prog & Hmalloc_sprog & Hpc_b & Hpcs_b
    & Ha_entry & Has_entry & Hbe & Hr_t0 & Hs_t0 & Hna & Hregs & Hsegs)".
    iDestruct "Hbe" as (b e Hbe) "(Hr_t1 & Hs_t1 & Hbe & Hsbe)".
    rewrite !delete_insert_delete.
    rewrite !(delete_insert_ne _ r_t1 r_t2) //.
    repeat (rewrite (insert_commute _ _ r_t2) //;[]). rewrite insert_insert.
    repeat (rewrite (insert_commute _ _ r_t2) //;[]). rewrite insert_insert.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]".
      by rewrite !lookup_insert_ne // lookup_delete_ne // lookup_insert //.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hsegs") as "[Hs_t6 Hsegs]".
      by rewrite !lookup_insert_ne // lookup_delete_ne // lookup_insert //.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]".
      rewrite lookup_delete_ne // !lookup_insert_ne // lookup_delete_ne //
              lookup_insert_ne // lookup_insert //.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hsegs") as "[Hs_t7 Hsegs]".
      rewrite lookup_delete_ne // !lookup_insert_ne // lookup_delete_ne //
              lookup_insert_ne // lookup_insert //.

    iApply (scrtcls_spec with "[- $Hprog $HPC $Hr_t1 $Hr_t6 $Hr_t7 $Hbe]"); eauto.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest.
      apply contiguous_between_bounds in Hcont_fetch.
      apply contiguous_between_incr_addr with (i:=2) (ai:=f1) in Hcont1; auto.
      revert Hmid Hcont_rest Hcont_fetch Hcont1 ; clear. solve_addr. }
    iNext. iIntros "(HPC & Hscrtcls_prog & Hr_t1 & Hact & Hr_t6 & Hr_t7)".

    iMod (scrtcls_s_spec with "[$Hspec $Hj $Hsprog $HsPC $Hs_t1 $Hs_t6 $Hs_t7 $Hsbe]")
      as "(Hj & HsPC & Hscrtcls_sprog & Hs_t1 & Hacts & Hs_t6 & Hs_t7)"; eauto.
    { intros mid Hmid. apply isCorrectPC_inrange with s_first s_last; auto.
      apply contiguous_between_bounds in Hcont_rests.
      apply contiguous_between_bounds in Hcont_fetchs.
      apply contiguous_between_incr_addr with (i:=2) (ai:=f2) in Hcont2; auto.
      revert Hmid Hcont_rests Hcont_fetchs Hcont2 ; clear. solve_addr. }

    (* continuation *)
    iApply "Hφ". iFrame "HPC HsPC Hpc_b Hpcs_b Ha_entry Has_entry Hj". iSplitL "Hprog_done Hmalloc_prog Hscrtcls_prog".
    { rewrite Heqapp. iDestruct "Hprog_done" as "[? ?]". iFrame. }
    iSplitL "Hsprog_done Hmalloc_sprog Hscrtcls_sprog".
    { rewrite Heqapps. iDestruct "Hsprog_done" as "[? ?]". iFrame. }
    iExists b,e. iSplitR;auto. iFrame.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by do 2 (rewrite lookup_delete_ne //); rewrite lookup_insert //.
    iFrame "Hr_t2".
    iDestruct (big_sepM_delete _ _ r_t2 with "Hsegs") as "[Hs_t2 Hsegs]".
      by do 2 (rewrite lookup_delete_ne //); rewrite lookup_insert //.
    iFrame "Hs_t2".
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs".
      by do 2 (rewrite lookup_delete_ne //); rewrite lookup_delete //.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete //.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t6]") as "Hsegs".
      by do 2 (rewrite lookup_delete_ne //); rewrite lookup_delete //.
    iDestruct (big_sepM_insert with "[$Hsegs $Hs_t7]") as "Hsegs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete //.

    repeat (repeat (rewrite delete_insert_ne //; []); rewrite delete_insert_delete).
    rewrite (delete_notin _ r_t1). 2: apply Hnotin_rmap; set_solver.
    rewrite (delete_notin _ r_t2). 2: rewrite !lookup_delete_ne //; apply Hnotin_rmap; set_solver.
    rewrite (delete_notin _ r_t1). 2: apply Hnotin_smap; set_solver.
    rewrite (delete_notin _ r_t2). 2: rewrite !lookup_delete_ne //; apply Hnotin_smap; set_solver.
    repeat (repeat (rewrite -delete_insert_ne //; []); rewrite insert_delete_insert).
    repeat (rewrite (insert_commute _ r_t7) //;[]).
    repeat (rewrite (insert_commute _ r_t6) //;[]). iFrame.
  Qed.

  (* ------------------------------- Closure Activation --------------------------------- *)

  Lemma closure_activation_spec_step Ep pc_p b_cls e_cls r1v renvv wcode wenv :
    readAllowed pc_p = true →
    isCorrectPC_range pc_p b_cls e_cls b_cls e_cls →
    pc_p ≠ E →
    nclose specN ⊆ Ep →

    spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↣ᵣ WCap pc_p b_cls e_cls b_cls
    ∗ r_t1 ↣ᵣ r1v
    ∗ r_env ↣ᵣ renvv
    ∗ [[b_cls, e_cls]]↣ₐ[[ activation_instrs wcode wenv ]]
    ={Ep}=∗ ⤇ Seq (Instr Executable)
        ∗ PC ↣ᵣ updatePcPerm wcode
        ∗ r_t1 ↣ᵣ wcode
        ∗ r_env ↣ᵣ wenv
        ∗ [[b_cls, e_cls]]↣ₐ[[ activation_instrs wcode wenv ]].
  Proof.
    iIntros (Hrpc Hvpc HnpcE Hnclose) "(#Hspec & Hj & HPC & Hr1 & Hrenv & Hcls)".
    rewrite /region_mapsto_spec.
    iDestruct (big_sepL2_length with "Hcls") as %Hcls_len. simpl in Hcls_len.
    assert (b_cls + 8 = Some e_cls)%a as Hbe.
    { rewrite finz_seq_between_length /finz.dist in Hcls_len.
      revert Hcls_len; clear; solve_addr. }
    assert (contiguous_between (finz.seq_between b_cls e_cls) b_cls e_cls) as Hcont_cls.
    { apply contiguous_between_of_region_addrs; auto. revert Hbe; clear; solve_addr. }
    pose proof (finz_seq_between_NoDup b_cls e_cls) as Hcls_nodup.
    iDestruct (big_sepL2_split_at 6 with "Hcls") as "[Hcls_code Hcls_data]".
    cbn [take drop].
    destruct (finz.seq_between b_cls e_cls) as [| ? ll]; [by inversion Hcls_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_cls). subst.
    do 7 (destruct ll as [| ? ll]; [by inversion Hcls_len|]).
    destruct ll;[| by inversion Hcls_len]. cbn [take drop].
    iDestruct "Hcls_data" as "(Hcls_ptr & Hcls_env & _)".
    (* move r_t1 PC *)
    iPrologue_s "Hcls_code".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr1]")
      as "(Hj & HPC & Hprog_done & Hr1)";
      [apply decode_encode_instrW_inv| iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 0 |auto..].
    iEpilogue_s.
    (* lea r_t1 7 *)
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr1]")
      as "(Hj & HPC & Hi & Hr1)";
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 1 | | done |auto ..].
    { eapply contiguous_between_incr_addr_middle' with (i:=0); eauto.
      cbn. clear. lia. }
    iEpilogue_s. iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_env r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_load_success_alt _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hrenv $Hr1 Hcls_env]")
      as "(Hj & HPC & Hrenv & Hi & Hr1 & Hcls_env)";
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       split;[done|] | iContiguous_next Hcont_cls 2 |auto ..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    iEpilogue_s.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* lea r_t1 (-1) *)
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr1]")
      as "(Hj & HPC & Hi & Hr1)";
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 3 | | done |auto ..].
    { assert ((f4 + 1)%a = Some f5) as HH. by iContiguous_next Hcont_cls 6.
      instantiate (1 := f4). revert HH. clear; solve_addr. }
    iEpilogue_s. iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_load_success_same_alt _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr1 Hcls_ptr]")
      as "(Hj & HPC & Hr1 & Hi & Hcls_ptr)";
      [(* FIXME *) auto | apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       split;[done|] | iContiguous_next Hcont_cls 4 | auto..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    iEpilogue_s.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* jmp r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr1]")
      as "(Hj & HPC & Hi & Hr1)";
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | auto.. ].
    iEpilogue_s.
    iFrame. do 4 (iDestruct "Hprog_done" as "(? & Hprog_done)"). iFrame. done.
  Qed.


End macros.
