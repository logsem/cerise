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
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first (fetch_instrs f)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ entry_a ↦ₐ wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (fetch_instrs f))%a
         ∗ codefrag a_first (fetch_instrs f)
         (* the newly allocated region *)
         ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ WInt 0%Z ∗ r_t3 ↦ᵣ WInt 0%Z
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
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
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    (* condition for assertion success *)
    (w_r = WInt z) ->

    ▷ codefrag a_first (assert_r_z_instrs f_a r z)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ fail_cap
    ∗ ▷ r ↦ᵣ w_r
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ (r_t1 ↦ᵣ WInt 0%Z ∗ r_t2 ↦ᵣ WInt 0%Z ∗ r_t3 ↦ᵣ WInt 0%Z ∗ r ↦ᵣ WInt 0%Z
         ∗ PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (assert_r_z_instrs f_a r z))%a
         ∗ codefrag a_first (assert_r_z_instrs f_a r z)
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry ↦ₐ fail_cap
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
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    (* failure subroutine assumptions *)
    SubBounds f_b f_e f_a_first (f_a_first ^+ length assert_fail_instrs)%a →
    (f_a_first + (length assert_fail_instrs))%a = Some a_env ->
    withinBounds f_b f_e a_env = true ->
    (* flag assumptions *)
    withinBounds flag_b flag_e flag_a = true →
    writeAllowed flag_p = true ->
    (* condition for assertion failure *)
    (z_r ≠ z) ->

    (* the assert and assert failure subroutine programs *)
    {{{ ▷ codefrag a_first (assert_r_z_instrs f_a r z)
    ∗ ▷ codefrag f_a_first assert_fail_instrs
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    (* linking table and assertion flag *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link (* the linking table capability *)
    ∗ ▷ a_entry ↦ₐ WCap E f_b f_e f_a_first (* the capability to the failure subroutine *)
    ∗ ▷ a_env ↦ₐ WCap flag_p flag_b flag_e flag_a (* the assertion flag capability *)
    ∗ ▷ flag_a ↦ₐ wf (* the assertion flag *)
    (* registers *)
    ∗ ▷ r ↦ᵣ WInt z_r
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3 }}}

      Seq (Instr Executable)

    {{{ RET FailedV; r_t1 ↦ᵣ WInt 0%Z ∗ r_t2 ↦ᵣ WInt 0%Z ∗ r_t3 ↦ᵣ WInt 0%Z ∗ (∃ z, r ↦ᵣ WInt z ∧ ⌜z ≠ 0⌝)
         ∗ PC ↦ᵣ WCap RX f_b f_e (f_a_first ^+ (length assert_fail_instrs - 1))%a
         ∗ codefrag a_first (assert_r_z_instrs f_a r z)
         ∗ codefrag f_a_first assert_fail_instrs
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry ↦ₐ WCap E f_b f_e f_a_first
         ∗ a_env ↦ₐ WCap flag_p flag_b flag_e flag_a ∗ flag_a ↦ₐ WInt 1%Z }}}.
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
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a
         ∗ codefrag a_first (malloc_instrs f_m size)
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
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
    { set_solver+ Hrmap_dom. }
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
      iFrameMapSolve+ Hrmap_dom "Hregs". }
    { iIntros (v) "[Hφ|Hφ] /=". iApply "Hψ". iFrame. iSimplifyEq. eauto. }
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec φ size cont pc_p pc_b pc_e a_first
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a
         ∗ codefrag a_first (malloc_instrs f_m size)
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
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

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) :=
    encodeInstrsW (map (λ r_i, Mov r_i 0) r).

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = encodeInstrW (Mov rr 0) :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Lemma rclear_spec (r: list RegName) (rmap : gmap RegName Word) pc_p pc_b pc_e a_first φ :
    PC ∉ r →
    r ≠ [] →
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (rclear_instrs r))%a →
    list_to_set r = dom (gset RegName) rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ codefrag a_first (rclear_instrs r)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (rclear_instrs r))%a
            ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ WInt 0%Z)
            ∗ codefrag a_first (rclear_instrs r)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hne Hnnil Hepc Hbounds Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iRevert (Hbounds Hrdom).
    iInduction (r) as [| r0 r'] "IH" forall (rmap a_first).
    { congruence. }

    iIntros (? Hrdom). cbn [list_to_set] in Hrdom.
    assert (is_Some (rmap !! r0)) as [r0v Hr0].
    { apply elem_of_gmap_dom. rewrite -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r0 with "Hreg") as "[Hr0 Hreg]". by eauto.
    codefrag_facts "Hrclear".
    iInstr "Hrclear". transitivity (Some (a_first ^+ 1)%a); auto. solve_addr.
    destruct (decide (r' = [])).
    { subst r'. iApply "Hφ". iFrame. iApply (big_sepM_delete _ _ r0); eauto. iFrame.
      rewrite (_: delete r0 rmap = ∅) //. apply dom_empty_inv_L.
      rewrite dom_delete_L -Hrdom. set_solver. }

    iAssert (codefrag (a_first ^+ 1)%a (rclear_instrs r') ∗
             (codefrag (a_first ^+ 1)%a (rclear_instrs r') -∗ codefrag a_first (rclear_instrs (r0 :: r'))))%I
    with "[Hrclear]" as "[Hrclear Hcont]".
    { cbn. unfold codefrag. rewrite (region_mapsto_cons _ (a_first ^+ 1)%a). 2,3: solve_addr.
      iDestruct "Hrclear" as "[? Hr]".
      rewrite (_: ((a_first ^+ 1) ^+ (length (rclear_instrs r')))%a =
                    (a_first ^+ (S (length (rclear_instrs r'))))%a). 2: solve_addr.
      iFrame. eauto. }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: (a_first ^+ (length (rclear_instrs (r0 :: r'))))%a =
                  ((a_first ^+ 1)%a ^+ length (rclear_instrs r'))%a) in H |- *
    end.
    2: unfold rclear_instrs; cbn; solve_addr.

    destruct (decide (r0 ∈ r')).
    { iDestruct (big_sepM_insert _ _ r0 with "[Hr0 $Hreg]") as "Hreg".
      by rewrite lookup_delete//. by iFrame.
      iApply ("IH" with "[] [] Hreg HPC Hrclear [Hφ Hcont]"); eauto.
      { iPureIntro. set_solver. }
      { iNext. iIntros "(? & Hreg & Hcode)". iApply "Hφ".
        iFrame. iDestruct ("Hcont" with "Hcode") as "Hcode". iFrame.
        iDestruct (big_sepM_insert with "Hreg") as "[? ?]". by rewrite lookup_delete//.
        iApply (big_sepM_delete _ _ r0). done. iFrame. }
      { iPureIntro. solve_pure_addr. }
      { rewrite insert_delete. iPureIntro. set_solver. } }
    { iApply ("IH" with "[] [] Hreg HPC Hrclear [Hφ Hcont Hr0]"); eauto.
      { iPureIntro. set_solver. }
      { iNext. iIntros "(? & Hreg & Hcode)". iApply "Hφ".
        iFrame. iDestruct ("Hcont" with "Hcode") as "Hcode". iFrame.
        iApply (big_sepM_delete _ _ r0). done. iFrame. }
      { iPureIntro. solve_pure_addr. }
      {  iPureIntro. set_solver. } }
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- CRTCLS ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* encodings of closure activation code *)
  (* CHANGE: the following code is changed to use r_t20 as a temp register rather than r_t1 *)
  (* TODO: use this convention across more examples, with a fixed choice of param registers and temp registers *)
  Definition v1 := encodeInstr (Mov r_t20 (inr PC)).
  Definition v2 := encodeInstr (Lea r_t20 (inl 7%Z)).
  Definition v3 := encodeInstr (Load r_env r_t20).
  Definition v4 := encodeInstr (Lea r_t20 (inl (-1)%Z)).
  Definition v5 := encodeInstr (Load r_t20 r_t20).
  Definition v6 := encodeInstr (Jmp r_t20).

  Definition activation_code : list Word :=
    encodeInstrsW [ Mov r_t20 PC ; Lea r_t20 7 ; Load r_env r_t20 ; Lea r_t20 (-1)%Z ; Load r_t20 r_t20 ; Jmp r_t20].
  Definition activation_instrs wcode wenv : list Word :=
    activation_code ++ [ wcode; wenv ].

  Definition scrtcls_instrs (rcode rdata: RegName) :=
    encodeInstrsW [ Store r_t1 v1
                  ; Lea r_t1 1
                  ; Store r_t1 v2
                  ; Lea r_t1 1
                  ; Store r_t1 v3
                  ; Lea r_t1 1
                  ; Store r_t1 v4
                  ; Lea r_t1 1
                  ; Store r_t1 v5
                  ; Lea r_t1 1
                  ; Store r_t1 v6
                  ; Lea r_t1 1
                  ; Store r_t1 rcode
                  ; Mov rcode 0
                  ; Lea r_t1 1
                  ; Store r_t1 rdata
                  ; Mov rdata 0
                  ; Lea r_t1 (-7)%Z
                  ; Restrict r_t1 e
                  ].

  Definition crtcls_instrs f_m :=
    encodeInstrsW [ Mov r_t6 r_t1
                  ; Mov r_t7 r_t2
                  ] ++ malloc_instrs f_m 8%nat
                  ++ scrtcls_instrs r_t6 r_t7.

  Lemma scrtcls_spec rcode rdata wvar wcode pc_p pc_b pc_e a_first act_b act_e act φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (scrtcls_instrs rcode rdata))%a →

    (act_b + 8)%a = Some act_e →

    ▷ codefrag a_first (scrtcls_instrs rcode rdata)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    (* register state *)
    ∗ ▷ r_t1 ↦ᵣ WCap RWX act_b act_e act_b
    ∗ ▷ rcode ↦ᵣ wcode
    ∗ ▷ rdata ↦ᵣ wvar
    (* memory for the activation record *)
    ∗ ▷ ([[act_b,act_e]] ↦ₐ [[ act ]])
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (scrtcls_instrs rcode rdata))%a
         ∗ codefrag a_first (scrtcls_instrs rcode rdata)
         ∗ r_t1 ↦ᵣ WCap E act_b act_e act_b
         ∗ [[act_b,act_e]] ↦ₐ [[ activation_instrs wcode wvar ]]
         ∗ rcode ↦ᵣ WInt 0%Z
         ∗ rdata ↦ᵣ WInt 0%Z
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hact) "(>Hprog & >HPC & >Hr_t1 & >Hrcode & >Hrdata & >Hact & Hφ)".

    (* TODO: This part is needed to have a concrete list, but could be automated as in codefrag_lookup_acc
       to avoid this *)
    assert (act_b < act_e)%a as Hlt;[solve_addr|].
    feed pose proof (contiguous_between_region_addrs act_b act_e) as Hcont_act. solve_addr.
    unfold region_mapsto.
    remember (region_addrs act_b act_e) as acta.
    assert (Hact_len_a : length acta = 8).
    { rewrite Heqacta region_addrs_length. by apply incr_addr_region_size_iff. }
    iDestruct (big_sepL2_length with "Hact") as %Hact_len.
    rewrite Hact_len_a in Hact_len. symmetry in Hact_len.
    repeat (destruct act as [| ? act]; try by inversion Hact_len). clear Hact_len.
    assert (∀ i a', acta !! i = Some a' → withinBounds act_b act_e a' = true) as Hwbact.
    { intros i a' Hsome. apply andb_true_intro. subst acta.
      apply contiguous_between_incr_addr with (i:=i) (ai:=a') in Hcont_act. 2: done.
      apply lookup_lt_Some in Hsome. split;[apply Z.leb_le|apply Z.ltb_lt]; solve_addr. }
    repeat (destruct acta as [|? acta]; try by inversion Hact_len_a). clear Hact_len_a.
    replace a with act_b in * by (symmetry; eapply contiguous_between_cons_inv_first; eauto).

    iDestruct "Hact" as "[Hact_b Hact]".
    iDestruct "Hact" as "[Ha0 Hact]".
    iDestruct "Hact" as "[Ha1 Hact]".
    iDestruct "Hact" as "[Ha2 Hact]".
    iDestruct "Hact" as "[Ha3 Hact]".
    iDestruct "Hact" as "[Ha4 Hact]".
    iDestruct "Hact" as "[Ha5 Hact]".
    iDestruct "Hact" as "[Ha6 Hact]".
    destruct (contiguous_between_cons_inv _ _ _ _ Hcont_act) as [_ [? [? HA0] ] ].
    destruct (contiguous_between_cons_inv _ _ _ _ HA0) as [<- [? [? HA1] ] ]; clear HA0.
    destruct (contiguous_between_cons_inv _ _ _ _ HA1) as [<- [? [? HA0] ] ]; clear HA1.
    destruct (contiguous_between_cons_inv _ _ _ _ HA0) as [<- [? [? HA1] ] ]; clear HA0.
    destruct (contiguous_between_cons_inv _ _ _ _ HA1) as [<- [? [? HA0] ] ]; clear HA1.
    destruct (contiguous_between_cons_inv _ _ _ _ HA0) as [<- [? [? HA1] ] ]; clear HA0.
    destruct (contiguous_between_cons_inv _ _ _ _ HA1) as [<- [? [? HA0] ] ]; clear HA1.
    destruct (contiguous_between_cons_inv _ _ _ _ HA0) as [<- [? [? HA1] ] ]; clear HA0 HA1 H6 x.
    generalize (contiguous_between_last _ _ _ a6 Hcont_act ltac:(reflexivity)); intros.

    codefrag_facts "Hprog".
    iInstr "Hprog". eapply (Hwbact 0); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 1); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 2); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 3); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 4); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 5); reflexivity.
    iInstr "Hprog".
    iInstr "Hprog". eapply (Hwbact 6); reflexivity.
    iGo "Hprog". eapply (Hwbact 7); reflexivity.
    iGo "Hprog". instantiate (1:= act_b). solve_addr.
    iInstr "Hprog". rewrite /e decode_encode_perm_inv //.
    iApply "Hφ". iFrame. rewrite /e decode_encode_perm_inv //.
  Qed.

  Lemma crtcls_spec_alt f_m wvar wcode pc_p pc_b pc_e
        a_first b_link a_link e_link a_entry b_m e_m mallocN EN rmap cont φ ψ:
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (crtcls_instrs f_m))%a →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    ↑mallocN ⊆ EN →

    ▷ codefrag a_first (crtcls_instrs f_m)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (crtcls_instrs f_m))%a
         ∗ codefrag a_first (crtcls_instrs f_m)
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ WCap E b e b
         ∗ [[b,e]] ↦ₐ [[ activation_instrs wcode wvar ]]
         ∗ r_t0 ↦ᵣ cont
         ∗ r_t2 ↦ᵣ WInt 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=WInt 0%Z]>
                               (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]>
                                 (<[r_t6:=WInt 0%Z]>
                                  (<[r_t7:=WInt 0%Z]> rmap)))), r_i ↦ᵣ w_i))
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN)
            "(>Hprog & >HPC & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    assert (is_Some (rmap !! r_t6)) as [rv6 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t7)) as [rv7 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]". by rewrite lookup_delete_ne //.

    focus_block_0 "Hprog" as "Hsetup" "Hcont".
    iGo "Hsetup".
    unfocus_block "Hsetup" "Hcont" as "Hprog".

    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hregs $Hr_t6]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs".
      simplify_map_eq. eapply not_elem_of_dom. set_solver.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      simplify_map_eq. eapply not_elem_of_dom. set_solver.
    map_simpl "Hregs".

    focus_block 1 "Hprog" as amid1 Hamid1 "Hmallocprog" "Hcont".
    iApply malloc_spec_alt; iFrameCapSolve; eauto; try iFrame "∗ #".
    { rewrite !dom_insert_L. rewrite Hrmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. clear; set_solver. }
    { lia. }
    iNext. iIntros "(HPC & Hmallocprog & Hpc_b & Ha_entry & Hbe & Hr_t0 & Hna & Hregs)".
    unfocus_block "Hmallocprog" "Hcont" as "Hprog".

    iDestruct "Hbe" as (b e Hbe) "(Hr_t1 & Hbe)".
    focus_block 2 "Hprog" as amid2 Hmid2 "Hscrtcls" "Hcont".
    map_simpl "Hregs".

    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]"; eauto.
      by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]"; eauto.
      by simplify_map_eq.
    map_simpl "Hregs".

    iApply scrtcls_spec; iFrameCapSolve; iFrame "∗".
    iNext. iIntros "(HPC & Hscrtcls & Hr_t1 & Hbe & Hr_t6 & Hr_t7)".
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hregs $Hr_t6]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_insert _ _ r_t7 with "[$Hregs $Hr_t7]") as "Hregs".
      by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]"; eauto.
      by simplify_map_eq.
    map_simpl "Hregs".
    unfocus_block "Hscrtcls" "Hcont" as "Hprog".
    changePCto (a_first ^+ length (crtcls_instrs f_m))%a.
    iApply "Hφ". iFrame "∗".
    iExists _,_. iSplitR; [eauto|]. iFrame "∗".
    clear; iFrameMapSolve "Hregs".
  Qed.

  Lemma crtcls_spec f_m wvar wcode pc_p pc_b pc_e
        a_first b_link a_link e_link a_entry b_m e_m mallocN EN rmap cont φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (crtcls_instrs f_m))%a →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    ↑mallocN ⊆ EN →

    ▷ codefrag a_first (crtcls_instrs f_m)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (crtcls_instrs f_m))%a
         ∗ codefrag a_first (crtcls_instrs f_m)
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ WCap E b e b
         ∗ [[b,e]] ↦ₐ [[ activation_instrs wcode wvar ]]
         ∗ r_t0 ↦ᵣ cont
         ∗ r_t2 ↦ᵣ WInt 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=WInt 0%Z]>
                               (<[r_t4:=WInt 0%Z]>
                                (<[r_t5:=WInt 0%Z]>
                                 (<[r_t6:=WInt 0%Z]>
                                  (<[r_t7:=WInt 0%Z]> rmap)))), r_i ↦ᵣ w_i))
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN)
            "(>Hprog & >HPC & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hφ)".
    iApply crtcls_spec_alt; iFrameCapSolve; eauto. iFrame. iFrame "Hmalloc".
    iSplitL. iNext. eauto. eauto.
  Qed.

  (* ------------------------------- Closure Activation --------------------------------- *)

  Lemma closure_activation_spec pc_p b_cls e_cls r1v renvv wcode wenv φ :
    ExecPCPerm pc_p →

    PC ↦ᵣ WCap pc_p b_cls e_cls b_cls
    ∗ r_t20 ↦ᵣ r1v
    ∗ r_env ↦ᵣ renvv
    ∗ [[b_cls, e_cls]]↦ₐ[[ activation_instrs wcode wenv ]]
    ∗ ▷ (  PC ↦ᵣ updatePcPerm wcode
       ∗ r_t20 ↦ᵣ wcode
       ∗ r_env ↦ᵣ wenv
       ∗ [[b_cls, e_cls]]↦ₐ[[ activation_instrs wcode wenv ]]
       -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hrpc) "(HPC & Hr1 & Hrenv & Hprog & Hcont)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hprog") as %Hcls_len. simpl in Hcls_len.
    assert (b_cls + 8 = Some e_cls)%a as Hbe.
    { rewrite region_addrs_length /region_size in Hcls_len.
      revert Hcls_len; clear; solve_addr. }
    assert (∃ b_end, b_cls + 6 = Some b_end)%a as [b_end Hbend];[destruct (b_cls + 6)%a eqn:HH;eauto;exfalso;solve_addr|].
    assert (∃ b_mid, b_cls + 7 = Some b_mid)%a as [b_mid Hbmid];[destruct (b_cls + 7)%a eqn:HH;eauto;exfalso;solve_addr|].

    iAssert (codefrag b_cls (activation_code) ∗ b_end ↦ₐ wcode ∗ b_mid ↦ₐ wenv)%I with "[Hprog]" as "[Hprog [Henv Henv']]".
    { rewrite /codefrag (_: b_cls ^+ length activation_code = b_end)%a /=; [|solve_addr].
      rewrite /activation_instrs.
      rewrite (region_addrs_split _ b_end);[|solve_addr].
      iDestruct (big_sepL2_app_inv with "Hprog") as "[Hprog Henv]". simpl. rewrite region_addrs_length /region_size. left. solve_addr.
      iFrame. rewrite region_addrs_cons;[|solve_addr]. assert (b_end + 1 = Some b_mid)%a as ->. solve_addr. simpl.
      rewrite region_addrs_cons;[|solve_addr]. assert (b_mid + 1 = Some e_cls)%a as ->. solve_addr. simpl.
      iDestruct "Henv" as "($&$&_)". }

    assert (readAllowed pc_p = true ∧ withinBounds b_cls e_cls b_mid = true) as [Hra Hwb].
    { split;[|solve_addr]. inversion Hrpc;subst;auto. }
    assert ((b_mid + -1)%a = Some b_end);[solve_addr|].
    assert (withinBounds b_cls e_cls b_end = true) as Hwb';[solve_addr|].

    assert (SubBounds b_cls e_cls b_cls (b_cls ^+ length (activation_code))%a). solve_addr.
    codefrag_facts "Hprog".
    iGo "Hprog". auto.
    iGo "Hprog".
    iApply "Hcont". iFrame.
    rewrite /codefrag (_: b_cls ^+ length activation_code = b_end)%a; [| solve_addr]. rewrite /activation_instrs.
    rewrite (region_addrs_split _ b_end);[|solve_addr]. 
    iApply (big_sepL2_app with "Hprog").
    rewrite region_addrs_cons;[|solve_addr]. assert (b_end + 1 = Some b_mid)%a as ->. solve_addr. simpl.
    rewrite region_addrs_cons;[|solve_addr]. assert (b_mid + 1 = Some e_cls)%a as ->. solve_addr. simpl.
    iFrame. rewrite region_addrs_empty;[|solve_addr]. done.
  Qed.

End macros.
