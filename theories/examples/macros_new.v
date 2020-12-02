From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics spec_patterns coq_tactics ltac_tactics reduction.
Require Import Eqdep_dec List.
From cap_machine Require Import classes rules logrel macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous malloc.
From cap_machine Require Import solve_pure proofmode map_simpl.

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) : list Word :=
    encodeInstrsW [
      Mov r_t1 PC;
      GetB r_t2 r_t1;
      GetA r_t3 r_t1;
      Sub r_t2 r_t2 r_t3;
      Lea r_t1 r_t2;
      Load r_t1 r_t1;
      Lea r_t1 f;
      Mov r_t2 0;
      Mov r_t3 0;
      Load r_t1 r_t1
    ].

  Lemma fetch_spec f pc_p pc_b pc_e a_first b_link e_link a_link entry_a wentry φ w1 w2 w3:
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (fetch_instrs f))%a →
    withinBounds (RW, b_link, e_link, entry_a) = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first (fetch_instrs f)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
    ∗ ▷ entry_a ↦ₐ wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_b,pc_e, (a_first ^+ length (fetch_instrs f))%a)
         ∗ codefrag a_first (fetch_instrs f)
         (* the newly allocated region *)
         ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z
         ∗ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
         ∗ entry_a ↦ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog". transitivity (Some pc_b); eauto. solve_addr.
    iGo "Hprog". iApply "Hφ"; iFrame.
 Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* The assert macro relies on a convention for the failure flag. This file contains the
     failure subroutine *)

  (* The convention for the failure flag: one address after the last instruction of the failure subroutine *)
  (* failing the assert will set the flag to 1 and then crash the program to a Failed configuration. The flag
     capability is at one address after the instructions *)
  Definition assert_fail_instrs :=
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 6;
      Load r_t1 r_t1;
      Store r_t1 1;
      Mov r_t1 0;
      Fail
    ].

  (* f_a is the offset of the failure subroutine in the linking table *)
  (* assert r z asserts that the register r contains the integer z *)
  (* r is assumed not to be r_t1 *)
  Definition assert_r_z_instrs f_a (r: RegName) (z: Z) :=
    fetch_instrs f_a ++
    encodeInstrsW [
      Sub r r z;
      Jnz r_t1 r;
      Mov r_t1 0
    ].

  (* Spec for assertion success *)
  (* Since we are not jumping to the failure subroutine, we do not need any assumptions
     about the failure subroutine *)
  Lemma assert_r_z_success f_a r z pc_p pc_b pc_e a_first
        b_link e_link a_link a_entry fail_cap w_r w1 w2 w3 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_r_z_instrs f_a r z))%a →
    (* linking table assumptions *)
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* condition for assertion success *)
    (w_r = inl z) ->

    ▷ codefrag a_first (assert_r_z_instrs f_a r z)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ fail_cap
    ∗ ▷ r ↦ᵣ w_r
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ (r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ r ↦ᵣ inl 0%Z
         ∗ PC ↦ᵣ inr (pc_p,pc_b,pc_e,(a_first ^+ length (assert_r_z_instrs f_a r z))%a)
         ∗ codefrag a_first (assert_r_z_instrs f_a r z)
         ∗ pc_b ↦ₐ inr (RO,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable Hsuccess)
            "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    subst w_r. rewrite {1}/assert_r_z_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameCapSolve.
    iNext. iIntros "(HPC & Hfetch & Hr1 & Hr2 & Hr3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iInstr "Hprog". rewrite (_: (z - z = 0)%Z); [| lia].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame.
    changePCto (a_first ^+ length (assert_r_z_instrs f_a r z))%a. iFrame.
  Qed.

  (* Spec for assertion failure *)
  (* When the assertion fails, the program jumps to the failure subroutine, sets the
     flag (which by convention is one address after subroutine) and Fails *)
  Lemma assert_r_z_fail f_a r z pc_p pc_b pc_e a_first z_r
        b_link e_link a_link a_entry
        f_b f_e f_a_first a_env (* fail subroutine *)
        flag_p flag_b flag_e flag_a (* flag capability *)
        w1 w2 w3 wf :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_r_z_instrs f_a r z))%a →
    (* linking table assumptions *)
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* failure subroutine assumptions *)
    SubBounds f_b f_e f_a_first (f_a_first ^+ length assert_fail_instrs)%a →
    (f_a_first + (length assert_fail_instrs))%a = Some a_env ->
    withinBounds (RX,f_b,f_e,a_env) = true ->
    (* flag assumptions *)
    withinBounds (flag_p,flag_b,flag_e,flag_a) = true →
    writeAllowed flag_p = true ->
    (* condition for assertion failure *)
    (z_r ≠ z) ->

    (* the assert and assert failure subroutine programs *)
    {{{ ▷ codefrag a_first (assert_r_z_instrs f_a r z)
    ∗ ▷ codefrag f_a_first assert_fail_instrs
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
    (* linking table and assertion flag *)
    ∗ ▷ pc_b ↦ₐ inr (RO,b_link,e_link,a_link) (* the linking table capability *)
    ∗ ▷ a_entry ↦ₐ inr (E,f_b,f_e,f_a_first) (* the capability to the failure subroutine *)
    ∗ ▷ a_env ↦ₐ inr (flag_p,flag_b,flag_e,flag_a) (* the assertion flag capability *)
    ∗ ▷ flag_a ↦ₐ wf (* the assertion flag *)
    (* registers *)
    ∗ ▷ r ↦ᵣ inl z_r
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3 }}}

      Seq (Instr Executable)

    {{{ RET FailedV; r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ (∃ z, r ↦ᵣ inl z ∧ ⌜z ≠ 0⌝)
         ∗ PC ↦ᵣ inr (RX, f_b, f_e, (f_a_first ^+ (length assert_fail_instrs - 1))%a)
         ∗ codefrag a_first (assert_r_z_instrs f_a r z)
         ∗ codefrag f_a_first assert_fail_instrs
         ∗ pc_b ↦ₐ inr (RO,b_link,e_link,a_link) ∗ a_entry ↦ₐ inr (E,f_b,f_e,f_a_first)
         ∗ a_env ↦ₐ inr (flag_p,flag_b,flag_e,flag_a) ∗ flag_a ↦ₐ inl 1%Z }}}.
  Proof.
    iIntros (Hexpc Hsub Hwb Htable Hsub' Henv Henvwb Hwb' Hwa Hfailure φ)
            "(>Hprog & >Hprog' & >HPC & >Hpc_b & >Ha_entry & >Ha_env & >Hflag & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3) Hφ".
    rewrite {1}/assert_r_z_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameCapSolve.
    iNext. iIntros "(HPC & Hfetch & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as amid1 Hamid1 "Hprog" "Hcont".
    iInstr "Hprog".
    iInstr "Hprog". by intros HH; inversion HH; lia.
    unfocus_block "Hprog" "Hcont" as "Hprog".

    rewrite {1}/assert_fail_instrs.
    codefrag_facts "Hprog'". iGo "Hprog'".
    wp_end. iApply "Hφ". iFrame. iExists _. iFrame. iPureIntro. lia.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m (size: Z) :=
    fetch_instrs f_m ++
    encodeInstrsW [
     Mov r_t5 r_t0;
     Mov r_t3 r_t1;
     Mov r_t1 size;
     Mov r_t0 PC;
     Lea r_t0 3;
     Jmp r_t3;
     Mov r_t0 r_t5;
     Mov r_t5 0
  ].

  (* malloc spec *)
  Lemma malloc_spec_alt φ ψ size cont pc_p pc_b pc_e a_first
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ inr (E,b_m,e_m,b_m)
    (* register state *)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_b,pc_e,(a_first ^+ length (malloc_instrs f_m size))%a)
         ∗ codefrag a_first (malloc_instrs f_m size)
         ∗ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
         ∗ a_entry ↦ₐ inr (E,b_m,e_m,b_m)
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ inr (RWX,b,e,b)
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=inl 0%Z]>
                               (<[r_t3:=inl 0%Z]>
                                (<[r_t4:=inl 0%Z]>
                                 (<[r_t5:=inl 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.

    rewrite {1}/malloc_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameCapSolve.
    iNext. iIntros "(HPC & Hfetch & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as amid1 Hamid1 "Hprog" "Hcont".
    iGo "Hprog". (* PC is now at b_m *)
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by simplify_map_eq.
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by simplify_map_eq.
    map_simpl "Hregs".
    iApply (wp_wand with "[- Hφfailed Hψ]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite !difference_difference_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. set_solver-. }
    iNext.
    rewrite updatePcPerm_cap_non_E; [| solve_pure].
    iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize'; subst size'.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      simplify_map_eq. eauto.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      simplify_map_eq. eauto.
    (* back our program, in the continuation of malloc *)
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    (* continuation *)
    iApply "Hφ". changePCto (a_first ^+ 18%nat)%a.
    iFrame. iSplitL "Hr_t1 Hbe".
    { iExists _,_. iFrame. iPureIntro; eauto. }
    { iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
        simplify_map_eq. reflexivity.
      iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
        simplify_map_eq. reflexivity.
      map_simpl "Hregs".
      repeat (rewrite (insert_commute _ r_t5) //;[]).
      rewrite (insert_commute _ r_t2 r_t3) //. }
    { iIntros (v) "[Hφ|Hφ] /=". iApply "Hψ". iFrame. iSimplifyEq. eauto. }
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec φ size cont pc_p pc_b pc_e a_first
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds (RW, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ inr (E,b_m,e_m,b_m)
    (* register state *)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_b,pc_e, (a_first ^+ length (malloc_instrs f_m size))%a)
         ∗ codefrag a_first (malloc_instrs f_m size)
         ∗ pc_b ↦ₐ inr (RO,b_link,e_link,a_link)
         ∗ a_entry ↦ₐ inr (E,b_m,e_m,b_m)
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ inr (RWX,b,e,b)
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=inl 0%Z]>
                               (<[r_t3:=inl 0%Z]>
                                (<[r_t4:=inl 0%Z]>
                                 (<[r_t5:=inl 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)".
    iApply malloc_spec_alt; iFrameCapSolve; eauto. iFrame. iFrame "Hmalloc".
    iSplitL. iNext. eauto. eauto.
  Qed.

End macros.
