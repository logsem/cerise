From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine Require Export iris_extra addr_reg_sample contiguous malloc assert.
(* From cap_machine Require Export salloc. *)
From cap_machine.proofmode Require Import classes tactics_helpers solve_pure proofmode map_simpl.

Section macros.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {seals:sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) : list LWord :=
    encodeInstrsLW [
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

  Lemma fetch_spec f pc_p pc_b pc_e pc_v a_first b_link e_link a_link v_link entry_a wentry φ w1 w2 w3:
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (fetch_instrs f))%a →
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first pc_v (fetch_instrs f)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (entry_a,v_link) ↦ₐ wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (fetch_instrs f))%a pc_v
         ∗ codefrag a_first pc_v (fetch_instrs f)
         (* the newly allocated region *)
         ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ LInt 0%Z ∗ r_t3 ↦ᵣ LInt 0%Z
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (entry_a,v_link) ↦ₐ wentry
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
  (* ----------------------------------- FETCH BIS ----------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_reg_instrs (f : Z) (r_lt : RegName): list LWord :=
    (* r_lt := (RO, b_lt, e_lt, b_tbl) ; linking table capability *)
    encodeInstrsLW [
        Lea r_lt f; (* r_lt := (RO, b_lt, e_lt, b_tbl + f) *)
        Load r_lt r_lt (* r_lt := mem(b_tbl + f) *)
      ].

  Lemma fetch_reg_spec f r_lt pc_p pc_b pc_e pc_v a_first b_link e_link a_link v_link entry_a wentry φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (fetch_reg_instrs f r_lt))%a →
    withinBounds b_link e_link entry_a = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ codefrag a_first pc_v (fetch_reg_instrs f r_lt)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (entry_a,v_link) ↦ₐ wentry
    ∗ ▷ r_lt ↦ᵣ LCap RO b_link e_link a_link v_link
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (fetch_reg_instrs f r_lt))%a pc_v
         ∗ codefrag a_first pc_v (fetch_reg_instrs f r_lt)
         (* the newly allocated region *)
         ∗ r_lt ↦ᵣ wentry
         ∗ (entry_a,v_link) ↦ₐ wentry
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Ha_entry & >Hr_t1 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog".
    iApply "Hφ"; iFrame.
 Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_instrs f_a :=
    fetch_instrs f_a ++
    encodeInstrsLW [
      Mov r_t2 r_t0;
      Mov r_t0 PC;
      Lea r_t0 3;
      Jmp r_t1;
      Mov r_t0 r_t2;
      Mov r_t1 0;
      Mov r_t2 0
    ].

  (* Spec for assertion success *)
  Lemma assert_success f_a pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link a_entry ba a_flag ea v_assert w0 w1 w2 w3 assertN EN n1 n2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_instrs f_a))%a →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ codefrag a_first pc_v (assert_instrs f_a)
    ∗ na_inv logrel_nais assertN (assert_inv ba a_flag ea v_assert)
    ∗ na_own logrel_nais EN
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ LInt n1
    ∗ ▷ r_t5 ↦ᵣ LInt n2
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (assert_instrs f_a))%a pc_v
         ∗ r_t0 ↦ᵣ w0
         ∗ r_t1 ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z ∗ r_t3 ↦ᵣ LInt 0%Z
         ∗ r_t4 ↦ᵣ LInt 0%Z ∗ r_t5 ↦ᵣ LInt 0%Z
         ∗ codefrag a_first pc_v (assert_instrs f_a)
         ∗ na_own logrel_nais EN
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & Hna & >HPC & >Hpc_b & >Ha_entry & >Hr0 & >Hr1 & >Hr2 & >Hr3
              & >Hr4 & >Hr5 & Hφ)".
    rewrite {1}/assert_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameAutoSolve.
    iNext. iIntros "(HPC & Hfetch & Hr1 & Hr2 & Hr3 & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    do 4 iInstr "Hprog".
    iApply (assert_success_spec with "[- $Hinv $Hna $HPC $Hr0 $Hr4 $Hr5]"); auto.
    iNext. iIntros "(Hna & HPC & Hr0 & Hr4 & Hr5)".
    rewrite updatePcPermL_cap_non_E; [| solve_pure ].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame.
    changePCto (a_first ^+ length (assert_instrs f_a))%a. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------------------- ASSERT BIS ---------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_reg_instrs f_a r_lt :=
    fetch_reg_instrs f_a r_lt ++
    encodeInstrsLW [
      Mov r_t2 r_t0;
      Mov r_t0 PC;
      Lea r_t0 3;
      Jmp r_lt;
      Mov r_t0 r_t2;
      Mov r_lt 0;
      Mov r_t2 0
    ].

  (* Spec for assertion success *)
  Lemma assert_reg_success f_a r_lt pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link a_entry ba a_flag ea v_assert w0 w2 assertN EN n1 n2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (assert_reg_instrs f_a r_lt))%a →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry ->
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ codefrag a_first pc_v (assert_reg_instrs f_a r_lt)
    ∗ na_inv logrel_nais assertN (assert_inv ba a_flag ea v_assert)
    ∗ na_own logrel_nais EN
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_lt ↦ᵣ (LCap RO b_link e_link a_link v_link)
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t4 ↦ᵣ LInt n1
    ∗ ▷ r_t5 ↦ᵣ LInt n2
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (assert_reg_instrs f_a r_lt))%a pc_v
         ∗ r_t0 ↦ᵣ w0
         ∗ r_lt ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z
         ∗ r_t4 ↦ᵣ LInt 0%Z ∗ r_t5 ↦ᵣ LInt 0%Z
         ∗ codefrag a_first pc_v (assert_reg_instrs f_a r_lt)
         ∗ na_own logrel_nais EN
         ∗ (a_entry,v_link) ↦ₐ LCap E ba ea ba v_assert
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & Hna & >HPC & >Ha_entry & >Hr0 & >Hrlt & >Hr2
              & >Hr4 & >Hr5 & Hφ)".
    rewrite {1}/assert_reg_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_reg_spec; iFrameAutoSolve.
    iNext. iIntros "(HPC & Hfetch & Hrlt & Hpc_b & Ha_entry)".
    unfocus_block "Hfetch" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    do 4 iInstr "Hprog".
    iApply (assert_success_spec with "[- $Hinv $Hna $HPC $Hr0 $Hr4 $Hr5]"); auto.
    iNext. iIntros "(Hna & HPC & Hr0 & Hr4 & Hr5)".
    rewrite updatePcPermL_cap_non_E; [| solve_pure ].
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame.
    changePCto (a_first ^+ length (assert_reg_instrs f_a r_lt))%a. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m (size: Z) :=
    fetch_instrs f_m ++
    encodeInstrsLW [
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
  Lemma malloc_spec_alt φ ψ size cont pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link f_m a_entry v_malloc mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first pc_v (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v_malloc)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
    (* register state *)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a pc_v
         ∗ codefrag a_first pc_v (malloc_instrs f_m size)
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ LCap RWX b e b v_malloc
            ∗ [[b,e]] ↦ₐ{v_malloc} [[region_addrs_zeroesL b e v_malloc]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]>
                               (<[r_t3:=LInt 0%Z]>
                                (<[r_t4:=LInt 0%Z]>
                                 (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.

    rewrite {1}/malloc_instrs.
    focus_block_0 "Hprog" as "Hfetch" "Hcont".
    iApply fetch_spec; iFrameAutoSolve.
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
    rewrite updatePcPermL_cap_non_E; [| solve_pure].
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
    { iIntros (w) "[Hφ|Hφ] /=". iApply "Hψ". iFrame. iSimplifyEq. eauto. }
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec φ size cont pc_p pc_b pc_e pc_v a_first
        b_link e_link a_link v_link f_m a_entry v_malloc mallocN b_m e_m EN rmap :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (malloc_instrs f_m size))%a →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    (size > 0)%Z →

    (* malloc program and subroutine *)
    ▷ codefrag a_first pc_v (malloc_instrs f_m size)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v_malloc)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
    ∗ ▷ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
    (* register state *)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (malloc_instrs f_m size))%a pc_v
         ∗ codefrag a_first pc_v (malloc_instrs f_m size)
         ∗ (pc_b,pc_v) ↦ₐ LCap RO b_link e_link a_link v_link
         ∗ (a_entry,v_link) ↦ₐ LCap E b_m e_m b_m v_malloc
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ LCap RWX b e b v_malloc
            ∗ [[b,e]] ↦ₐ{v_malloc} [[region_addrs_zeroesL b e v_malloc]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]>
                               (<[r_t3:=LInt 0%Z]>
                                (<[r_t4:=LInt 0%Z]>
                                 (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)".
    iApply malloc_spec_alt; iFrameAutoSolve; eauto. iFrame. iFrame "Hmalloc".
    iSplitL. iNext. eauto. eauto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- SALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* salloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the salloc capability *)
  (* Definition salloc_instrs f_m (size: Z) := *)
  (*   fetch_instrs f_m ++ *)
  (*   encodeInstrsLW [ *)
  (*    Mov r_t5 r_t0; *)
  (*    Mov r_t3 r_t1; *)
  (*    Mov r_t1 size; *)
  (*    Mov r_t0 PC; *)
  (*    Lea r_t0 3; *)
  (*    Jmp r_t3; *)
  (*    Mov r_t0 r_t5; *)
  (*    Mov r_t5 0 *)
  (* ]. *)

  (* (* salloc spec *) *)
  (* Lemma salloc_spec_alt φ ψ size cont pc_p pc_b pc_e v a_first *)
  (*       b_link e_link a_link f_m a_entry sallocN b_m e_m EN rmap : *)
  (*   ExecPCPerm pc_p → *)
  (*   SubBounds pc_b pc_e a_first (a_first ^+ length (salloc_instrs f_m size))%a → *)
  (*   withinBounds b_link e_link a_entry = true → *)
  (*   (a_link + f_m)%a = Some a_entry → *)
  (*   dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} → *)
  (*   ↑sallocN ⊆ EN → *)
  (*   (size > 0)%Z → *)

  (*   (* salloc program and subroutine *) *)
  (*   ▷ codefrag a_first v (salloc_instrs f_m size) *)
  (*   ∗ na_inv logrel_nais sallocN (salloc_inv b_m e_m v) *)
  (*   ∗ na_own logrel_nais EN *)
  (*   (* we need to assume that the salloc capability is in the linking table at offset f_m *) *)
  (*   ∗ ▷ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v *)
  (*   ∗ ▷ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v *)
  (*   (* register state *) *)
  (*   ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v *)
  (*   ∗ ▷ r_t0 ↦ᵣ cont *)
  (*   ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
  (*   (* failure/continuation *) *)
  (*   ∗ ▷ (∀ v, ψ v -∗ φ v) *)
  (*   ∗ ▷ (φ FailedV) *)
  (*   ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (salloc_instrs f_m size))%a v *)
  (*        ∗ codefrag a_first v (salloc_instrs f_m size) *)
  (*        ∗ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v *)
  (*        ∗ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v *)
  (*        (* the newly allocated region *) *)
  (*        ∗ (∃ (bs es : OType), *)
  (*           ⌜(bs + size)%ot = Some es⌝ *)
  (*           ∗ r_t1 ↦ᵣ LSealRange (true,true) bs es bs *)
  (*           ∗ ([∗ list] o ∈ finz.seq_between bs es, can_alloc_pred o)) *)
  (*        ∗ r_t0 ↦ᵣ cont *)
  (*        ∗ na_own logrel_nais EN *)
  (*        ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]> *)
  (*                              (<[r_t3:=LInt 0%Z]> *)
  (*                               (<[r_t4:=LInt 0%Z]> *)
  (*                                (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i) *)
  (*        (* the newly allocated region is fresh in the current world *) *)
  (*        (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *) *)
  (*        -∗ WP Seq (Instr Executable) {{ ψ }}) *)
  (*   ⊢ *)
  (*     WP Seq (Instr Executable) {{ λ v, φ v }}. *)
  (* Proof. *)
  (*   iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HsallocN Hsize) *)
  (*           "(>Hprog & #Hsalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)". *)
  (*   (* extract necessary registers from regs *) *)
  (*   iDestruct (big_sepL2_length with "Hprog") as %Hlength. *)
  (*   assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver. *)
  (*   iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto. *)
  (*   assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver. *)
  (*   iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //. *)
  (*   assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver. *)
  (*   iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //. *)
  (*   assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver. *)
  (*   iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //. *)

  (*   rewrite {1}/salloc_instrs. *)
  (*   focus_block_0 "Hprog" as "Hfetch" "Hcont". *)
  (*   iApply fetch_spec; iFrameAutoSolve. *)
  (*   iNext. iIntros "(HPC & Hfetch & Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)". *)
  (*   unfocus_block "Hfetch" "Hcont" as "Hprog". *)

  (*   focus_block 1 "Hprog" as amid1 Hamid1 "Hprog" "Hcont". *)
  (*   iGo "Hprog". (* PC is now at b_m *) *)
  (*   (* we are now ready to use the salloc subroutine spec. For this we prepare the registers *) *)
  (*   iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs". *)
  (*     by simplify_map_eq. *)
  (*   iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs". *)
  (*     by simplify_map_eq. *)
  (*   map_simpl "Hregs". *)
  (*   iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs". *)
  (*     by simplify_map_eq. *)
  (*   map_simpl "Hregs". *)
  (*   iApply (wp_wand with "[- Hφfailed Hψ]"). *)
  (*   iApply (simple_salloc_subroutine_spec with "[- $Hsalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto. *)
  (*   { set_solver+ Hrmap_dom. } *)
  (*   iNext. *)
  (*   rewrite updatePcPermL_cap_non_E; [| solve_pure]. *)
  (*   iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=". *)
  (*   iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize'; subst size'. *)
  (*   iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". *)
  (*     simplify_map_eq. eauto. *)
  (*   iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". *)
  (*     simplify_map_eq. eauto. *)
  (*   (* back our program, in the continuation of salloc *) *)
  (*   iGo "Hprog". *)
  (*   unfocus_block "Hprog" "Hcont" as "Hprog". *)
  (*   (* continuation *) *)
  (*   iApply "Hφ". changePCto (a_first ^+ length (salloc_instrs f_m size)%nat)%a. *)
  (*   iFrame. iSplitL "Hr_t1 Hbe". *)
  (*   { iExists _,_. iFrame. iPureIntro; eauto. } *)
  (*   { iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs". *)
  (*       simplify_map_eq. reflexivity. *)
  (*     iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs". *)
  (*     simplify_map_eq. reflexivity. *)
  (*     iFrameMapSolve+ Hrmap_dom "Hregs". } *)
  (*   { iIntros (w) "[Hφ|Hφ] /=". iApply "Hψ". iFrame. iSimplifyEq. eauto. } *)
  (* Qed. *)

  (* (* salloc spec - alternative formulation *) *)
  (* Lemma salloc_spec φ size cont pc_p pc_b pc_e v a_first *)
  (*       b_link e_link a_link f_m a_entry sallocN b_m e_m EN rmap : *)
  (*   ExecPCPerm pc_p → *)
  (*   SubBounds pc_b pc_e a_first (a_first ^+ length (salloc_instrs f_m size))%a → *)
  (*   withinBounds b_link e_link a_entry = true → *)
  (*   (a_link + f_m)%a = Some a_entry → *)
  (*   dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} → *)
  (*   ↑sallocN ⊆ EN → *)
  (*   (size > 0)%Z → *)

  (*   (* salloc program and subroutine *) *)
  (*   ▷ codefrag a_first v (salloc_instrs f_m size) *)
  (*   ∗ na_inv logrel_nais sallocN (salloc_inv b_m e_m v) *)
  (*   ∗ na_own logrel_nais EN *)
  (*   (* we need to assume that the salloc capability is in the linking table at offset f_m *) *)
  (*   ∗ ▷ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v *)
  (*   ∗ ▷ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v *)
  (*   (* register state *) *)
  (*   ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v *)
  (*   ∗ ▷ r_t0 ↦ᵣ cont *)
  (*   ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i) *)
  (*   (* continuation *) *)
  (*   ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (salloc_instrs f_m size))%a v *)
  (*        ∗ codefrag a_first v (salloc_instrs f_m size) *)
  (*        ∗ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v *)
  (*        ∗ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v *)
  (*        (* the newly allocated region *) *)
  (*        ∗ (∃ (bs es : OType), *)
  (*           ⌜(bs + size)%ot = Some es⌝ *)
  (*           ∗ r_t1 ↦ᵣ LSealRange (true,true) bs es bs *)
  (*           ∗ ([∗ list] o ∈ finz.seq_between bs es, can_alloc_pred o)) *)
  (*        ∗ r_t0 ↦ᵣ cont *)
  (*        ∗ na_own logrel_nais EN *)
  (*        ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=LInt 0%Z]> *)
  (*                              (<[r_t3:=LInt 0%Z]> *)
  (*                               (<[r_t4:=LInt 0%Z]> *)
  (*                                (<[r_t5:=LInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i) *)
  (*        (* the newly allocated region is fresh in the current world *) *)
  (*        (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *) *)
  (*        -∗ WP Seq (Instr Executable) {{ φ }}) *)
  (*   ⊢ *)
  (*     WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}. *)
  (* Proof. *)
  (*   iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HsallocN Hsize) *)
  (*           "(>Hprog & #Hsalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)". *)
  (*   iApply salloc_spec_alt; iFrameAutoSolve; eauto. iFrame. iFrame "Hsalloc". *)
  (*   iSplitL. iNext. eauto. eauto. *)
  (* Qed. *)

  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)

  (* ------------------------------- *)
  Definition reqperm_instrs r z :=
    encodeInstrsLW [
        GetWType r_t1 r;
        Sub r_t1 r_t1 (encodeLWordType lwt_cap);
        Mov r_t2 PC;
        Lea r_t2 11;
        Jnz r_t2 r_t1;
        GetP r_t1 r;
         Sub r_t1 r_t1 z
        ; Mov r_t2 PC
        ; Lea r_t2 6
        ; Jnz r_t2 r_t1
        ; Mov r_t2 PC
        ; Lea r_t2 4
        ; Jmp r_t2
        ; Fail
        ; Mov r_t1 0
        ; Mov r_t2 0].

  Lemma reqperm_spec r perm w pc_p pc_b pc_e v a_first w1 w2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (reqperm_instrs r (encodePerm perm)))%a →

      ▷ codefrag a_first v (reqperm_instrs r (encodePerm perm))
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if isPermLWord w perm then
           ∃ b e a', ⌜w = LCap perm b e a' v⌝ ∧
           (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (reqperm_instrs r (encodePerm perm)))%a v
            ∗ codefrag a_first v (reqperm_instrs r (encodePerm perm)) ∗
            r ↦ᵣ LCap perm b e a' v ∗ r_t1 ↦ᵣ LInt 0%Z ∗ r_t2 ↦ᵣ LInt 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    codefrag_facts "Hprog".
    iGo "Hprog".
    eapply getwtype_denote ; reflexivity .
    do 3 iInstr "Hprog".
    destruct (is_log_cap w) eqn:Hcap; cycle 1.
    {
      assert (isPermLWord w perm = false) as ->. {destruct_lword w; auto. inversion Hcap. }

      (* if w is not a capability we jump to the failure case *)
      iInstr "Hprog".
      (* TODO maybe I could generalize this next sub-proof ? *)
     { rewrite -/(encodeLWordType w).
       intros Hcontr; clear -Hcap Hcontr.
        destruct w; [| (destruct sb; [by simpl in Hcap|]) |]
        ; unfold lwt_cap in Hcontr
        ; injection Hcontr
        ; clear Hcontr; intro Hcontr
        ; apply Zminus_eq in Hcontr
        ; match goal with
          | H: encodeLWordType ?x = encodeLWordType ?y |- _ =>
              pose proof (encodeLWordType_correct x y) as Hcontr2 ; cbn in Hcontr2
          end
        ; auto.
      }
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)). rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      by wp_end. }
    {
    (* now we know that w is a capability *)
    assert (∃ p b e a v, w = LCap p b e a v)  as (pc & bc & ec & ac & vc & ->).
    {destruct_lword w ; inversion Hcap. eexists _,_,_,_,_; eauto. }
    rewrite -/(encodeLWordType _).
    simpl_encodeLWordType; rewrite Z.sub_diag.
    do 5 iInstr "Hprog".
    destruct (isPermLWord (LCap pc bc ec ac vc) perm) eqn:Hperm.
    {
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      wp_instr.
      assert (encodePerm pc - encodePerm perm = 0)%Z as ->.
      { inversion Hperm as [Hp]. apply bool_decide_eq_true_1 in Hp as ->. lia. }
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");iFrameAutoSolve.
      iNext. iIntros "(HPC & Hi & Hr_t2 & Hr_t1)". wp_pure.
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iGo "Hprog".
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)).
      rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      iDestruct "Hφ" as (b' e' a' Heq) "Hφ". inv Heq.
      iApply "Hφ"; iFrame. }
    {
      iGo "Hprog".
      inversion Hperm as [Hp]. apply bool_decide_eq_false_1 in Hp. intros Hcontr; inversion Hcontr as [Heq].
      apply Zminus_eq,encodePerm_inj in Heq. subst pc. done.
      rewrite -/(updatePcPermL (LCap _ _ _ _ _)%a).
      rewrite updatePcPermL_cap_non_E;[|inv Hvpc;auto].
      iGo "Hprog".
      iApply wp_value. iFrame. } }
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) exactly equal to [minsize]. *)

  Definition reqsize_exact_instrs r (exsize : Z) :=
    encodeInstrsLW
      [ GetB r_t1 r ;
      GetE r_t2 r;
      Sub r_t1 r_t2 r_t1;
      Sub r_t1 r_t1 exsize;
      Mov r_t2 PC;
      Lea r_t2 6;
      Jnz r_t2 r_t1;
      Mov r_t2 PC;
      Lea r_t2 4;
      Jmp r_t2;
      Fail].

  Lemma reqsize_spec r minsize pc_p pc_b pc_e v a_first r_p r_b r_e r_a w1 w2 φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (reqsize_exact_instrs r minsize))%a →

      ▷ codefrag a_first v (reqsize_exact_instrs r minsize)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ r ↦ᵣ LCap r_p r_b r_e r_a v
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if (minsize =? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            codefrag a_first v (reqsize_exact_instrs r minsize)
            ∗ PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (reqsize_exact_instrs r minsize))%a v
            ∗ r ↦ᵣ LCap r_p r_b r_e r_a v
            ∗ r_t1 ↦ᵣ w1
            ∗ r_t2 ↦ᵣ w2)
           -∗ WP Seq (Instr Executable) {{ φ }}
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    codefrag_facts "Hprog".
    do 6 iInstr "Hprog".

    destruct (minsize =? r_e - r_b)%Z eqn:Hsize.
    { iInstr_lookup "Hprog" as "Hi" "Hcont".
      wp_instr.
      assert (r_e - r_b - minsize = 0)%Z as ->.
      { solve_addr. }
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");iFrameAutoSolve.
      iNext. iIntros "(HPC & Hi & Hr_t2 & Hr_t1)". wp_pure.
      iDestruct ("Hcont" with "Hi") as "Hprog".
      iGo "Hprog".
      rewrite -/(updatePcPermL (LCap pc_p pc_b pc_e (a_first ^+ 11)%a v)).
      rewrite updatePcPermL_cap_non_E;[|by inv Hvpc].
      iApply "Hφ". iExists _,_. iFrame. }
    { iGo "Hprog". intros Hcontr. inv Hcontr. solve_addr.
      rewrite -/(updatePcPermL ((LWSealable (LSCap pc_p pc_b pc_e (a_first ^+ 10)%a v)))).
      rewrite updatePcPermL_cap_non_E;[|by inv Hvpc].
      iGo "Hprog". iApply wp_value. iFrame. }
  Qed.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) :=
    encodeInstrsLW (map (λ r_i, Mov r_i 0) r).

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = encodeInstrWL (Mov rr 0) :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Lemma rclear_spec (r: list RegName) (rmap : gmap RegName LWord) pc_p pc_b pc_e v a_first φ :
    PC ∉ r →
    r ≠ [] →
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (rclear_instrs r))%a →
    list_to_set r = dom rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ ▷ codefrag a_first v (rclear_instrs r)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (rclear_instrs r))%a v
            ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ LInt 0%Z)
            ∗ codefrag a_first v (rclear_instrs r)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hne Hnnil Hepc Hbounds Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iRevert (Hbounds Hrdom).
    iInduction (r) as [| r0 r'] "IH" forall (rmap a_first).
    { congruence. }

    iIntros (? Hrdom). cbn [list_to_set] in Hrdom.
    assert (is_Some (rmap !! r0)) as [r0v Hr0].
    { apply elem_of_dom. rewrite -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r0 with "Hreg") as "[Hr0 Hreg]". by eauto.
    codefrag_facts "Hrclear".
    iInstr "Hrclear". transitivity (Some (a_first ^+ 1)%a); auto. solve_addr.
    destruct (decide (r' = [])).
    { subst r'. iApply "Hφ". iFrame. iApply (big_sepM_delete _ _ r0); eauto. iFrame.
      rewrite (_: delete r0 rmap = ∅) //. apply dom_empty_inv_L.
      rewrite dom_delete_L -Hrdom. set_solver. }

    iAssert (codefrag (a_first ^+ 1)%a v (rclear_instrs r') ∗
             (codefrag (a_first ^+ 1)%a v (rclear_instrs r') -∗ codefrag a_first v (rclear_instrs (r0 :: r'))))%I
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
      { rewrite insert_delete_insert. iPureIntro. set_solver. } }
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

  Definition activation_code : list LWord :=
    encodeInstrsLW [ Mov r_t20 PC ; Lea r_t20 7 ; Load r_env r_t20 ; Lea r_t20 (-1)%Z ; Load r_t20 r_t20 ; Jmp r_t20].
  Definition activation_instrs wcode wenv : list LWord :=
    activation_code ++ [ wcode; wenv ].

  Definition scrtcls_instrs (rcode rdata: RegName) :=
    encodeInstrsLW [ Store r_t1 v1
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
    encodeInstrsLW [ Mov r_t6 r_t1
                  ; Mov r_t7 r_t2
                  ] ++ malloc_instrs f_m 8%nat
                  ++ scrtcls_instrs r_t6 r_t7.

  Lemma scrtcls_spec rcode rdata wvar wcode pc_p pc_b pc_e v a_first act_b act_e act φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (scrtcls_instrs rcode rdata))%a →

    (act_b + 8)%a = Some act_e →

    ▷ codefrag a_first v (scrtcls_instrs rcode rdata)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    (* register state *)
    ∗ ▷ r_t1 ↦ᵣ LCap RWX act_b act_e act_b v
    ∗ ▷ rcode ↦ᵣ wcode
    ∗ ▷ rdata ↦ᵣ wvar
    (* memory for the activation record *)
    ∗ ▷ ([[act_b,act_e]] ↦ₐ{v} [[ act ]])
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (scrtcls_instrs rcode rdata))%a v
         ∗ codefrag a_first v (scrtcls_instrs rcode rdata)
         ∗ r_t1 ↦ᵣ LCap E act_b act_e act_b v
         ∗ [[act_b,act_e]] ↦ₐ{v} [[ activation_instrs wcode wvar ]]
         ∗ rcode ↦ᵣ LInt 0%Z
         ∗ rdata ↦ᵣ LInt 0%Z
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hact) "(>Hprog & >HPC & >Hr_t1 & >Hrcode & >Hrdata & >Hact & Hφ)".

    (* TODO: This part is needed to have a concrete list, but could be automated as in codefrag_lookup_acc
       to avoid this *)
    assert (act_b < act_e)%a as Hlt;[solve_addr|].
    opose proof (contiguous_between_region_addrs act_b act_e _) as Hcont_act; first solve_addr.
    unfold region_mapsto.
    remember (finz.seq_between act_b act_e) as acta.
    assert (Hact_len_a : length acta = 8).
    { rewrite Heqacta finz_seq_between_length. by apply finz_incr_iff_dist. }
    iDestruct (big_sepL2_length with "Hact") as %Hact_len.
    rewrite map_length Hact_len_a in Hact_len. symmetry in Hact_len.
    repeat (destruct act as [| ? act]; try by inversion Hact_len). clear Hact_len.
    assert (∀ i a', acta !! i = Some a' → withinBounds act_b act_e a' = true) as Hwbact.
    { intros i a' Hsome. apply andb_true_intro. subst acta.
      apply contiguous_between_incr_addr with (i:=i) (ai:=a') in Hcont_act. 2: done.
      apply lookup_lt_Some in Hsome. split;[apply Z.leb_le|apply Z.ltb_lt]; solve_addr. }
    repeat (destruct acta as [|? acta]; try by inversion Hact_len_a). clear Hact_len_a.
    replace f with act_b in * by (symmetry; eapply contiguous_between_cons_inv_first; eauto).

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
    generalize (contiguous_between_last _ _ _ f6 Hcont_act ltac:(reflexivity)); intros.

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

  Lemma crtcls_spec_alt f_m wvar wcode pc_p pc_b pc_e v
        a_first b_link a_link e_link a_entry b_m e_m mallocN EN rmap cont φ ψ:
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (crtcls_instrs f_m))%a →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    ↑mallocN ⊆ EN →

    ▷ codefrag a_first v (crtcls_instrs f_m)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v
    ∗ ▷ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (φ FailedV)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (crtcls_instrs f_m))%a v
         ∗ codefrag a_first v (crtcls_instrs f_m)
         ∗ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v
         ∗ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ LCap E b e b v
         ∗ [[b,e]] ↦ₐ{v} [[ activation_instrs wcode wvar ]]
         ∗ r_t0 ↦ᵣ cont
         ∗ r_t2 ↦ᵣ LInt 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=LInt 0%Z]>
                               (<[r_t4:=LInt 0%Z]>
                                (<[r_t5:=LInt 0%Z]>
                                 (<[r_t6:=LInt 0%Z]>
                                  (<[r_t7:=LInt 0%Z]> rmap)))), r_i ↦ᵣ w_i))
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN)
            "(>Hprog & >HPC & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    assert (is_Some (rmap !! r_t6)) as [rv6 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t7)) as [rv7 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
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
    iApply malloc_spec_alt; iFrameAutoSolve; eauto; try iFrame "∗ #".
    { rewrite !dom_insert_L. rewrite Hrmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. }
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

    iApply scrtcls_spec; iFrameAutoSolve; iFrame "∗".
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
    rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hrmap_dom; set_solver].
    rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hrmap_dom; set_solver].
    clear -Hrmap_dom; iFrameMapSolve "Hregs".
  Qed.

  Lemma crtcls_spec f_m wvar wcode pc_p pc_b pc_e v
        a_first b_link a_link e_link a_entry b_m e_m mallocN EN rmap cont φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (crtcls_instrs f_m))%a →

    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    ↑mallocN ⊆ EN →

    ▷ codefrag a_first v (crtcls_instrs f_m)
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first v
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m v)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v
    ∗ ▷ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length (crtcls_instrs f_m))%a v
         ∗ codefrag a_first v (crtcls_instrs f_m)
         ∗ (pc_b,v) ↦ₐ LCap RO b_link e_link a_link v
         ∗ (a_entry,v) ↦ₐ LCap E b_m e_m b_m v
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ LCap E b e b v
         ∗ [[b,e]] ↦ₐ{v} [[ activation_instrs wcode wvar ]]
         ∗ r_t0 ↦ᵣ cont
         ∗ r_t2 ↦ᵣ LInt 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=LInt 0%Z]>
                               (<[r_t4:=LInt 0%Z]>
                                (<[r_t5:=LInt 0%Z]>
                                 (<[r_t6:=LInt 0%Z]>
                                  (<[r_t7:=LInt 0%Z]> rmap)))), r_i ↦ᵣ w_i))
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN)
            "(>Hprog & >HPC & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hφ)".
    iApply crtcls_spec_alt; iFrameAutoSolve; eauto. iFrame. iFrame "Hmalloc".
    iSplitL. iNext. eauto. eauto.
  Qed.

  (* ------------------------------- Closure Activation --------------------------------- *)

  Lemma closure_activation_spec pc_p b_cls e_cls v r1v renvv wcode wenv φ :
    ExecPCPerm pc_p →

    PC ↦ᵣ LCap pc_p b_cls e_cls b_cls v
    ∗ r_t20 ↦ᵣ r1v
    ∗ r_env ↦ᵣ renvv
    ∗ [[b_cls, e_cls]] ↦ₐ{v} [[ activation_instrs wcode wenv ]]
    ∗ ▷ (  PC ↦ᵣ updatePcPermL wcode
       ∗ r_t20 ↦ᵣ wcode
       ∗ r_env ↦ᵣ wenv
       ∗ [[b_cls, e_cls]] ↦ₐ{v} [[ activation_instrs wcode wenv ]]
       -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hrpc) "(HPC & Hr1 & Hrenv & Hprog & Hcont)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hprog") as %Hcls_len. simpl in Hcls_len.
    assert (b_cls + 8 = Some e_cls)%a as Hbe.
    { rewrite map_length finz_seq_between_length /finz.dist in Hcls_len.
      revert Hcls_len; clear; solve_addr. }
    assert (∃ b_end, b_cls + 6 = Some b_end)%a as [b_end Hbend];[destruct (b_cls + 6)%a eqn:HH;eauto;exfalso;solve_addr|].
    assert (∃ b_mid, b_cls + 7 = Some b_mid)%a as [b_mid Hbmid];[destruct (b_cls + 7)%a eqn:HH;eauto;exfalso;solve_addr|].

    iAssert (codefrag b_cls v (activation_code) ∗ (b_end,v) ↦ₐ wcode ∗ (b_mid,v) ↦ₐ wenv)%I with "[Hprog]" as "[Hprog [Henv Henv']]".
    { rewrite /codefrag (_: b_cls ^+ length activation_code = b_end)%a /=; [|solve_addr].
      rewrite /activation_instrs.
      rewrite (finz_seq_between_split _ b_end);[|solve_addr].
      rewrite map_app.
      iDestruct (big_sepL2_app_inv with "Hprog") as "[Hprog Henv]". simpl.
      rewrite map_length finz_seq_between_length /finz.dist. left. solve_addr.
      iFrame. rewrite finz_seq_between_cons;[|solve_addr]. assert (b_end + 1 = Some b_mid)%a as ->%addr_incr_eq. solve_addr. simpl.
      rewrite finz_seq_between_cons;[|solve_addr]. assert (b_mid + 1 = Some e_cls)%a as ->%addr_incr_eq. solve_addr. simpl.
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
    rewrite (finz_seq_between_split _ b_end);[|solve_addr].
      rewrite map_app.
    iApply (big_sepL2_app with "Hprog").
    rewrite finz_seq_between_cons;[|solve_addr]. assert (b_end + 1 = Some b_mid)%a as ->%addr_incr_eq. solve_addr. simpl.
    rewrite finz_seq_between_cons;[|solve_addr]. assert (b_mid + 1 = Some e_cls)%a as ->%addr_incr_eq. solve_addr. simpl.
    iFrame. rewrite finz_seq_between_empty;[|solve_addr]. done.
  Qed.

End macros.
