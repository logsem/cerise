From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import malloc macros.
From cap_machine Require Import fundamental logrel macros_helpers rules proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine Require Import register_tactics.
From cap_machine.exercises Require Import subseg_buffer.
Open Scope Z_scope.

(** Secondly, the other approach is to dynamically allocate the region with
    the `malloc` macro. *)
Section malloc_program.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg : sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition prog_malloc_instrs f_m (size : nat) secret_off secret_val : list Word :=
    (* code: *)
    malloc_instrs f_m size ++ (prog_code secret_off secret_val).

  Definition prog_malloc_code a_prog f_m size secret_off secret_val :=
    ([∗ list] a_i;w ∈ a_prog;(prog_malloc_instrs f_m size secret_off secret_val), a_i ↦ₐ w)%I.

  (** We define the needed invariant *)

  Definition malloc_versionN : namespace := nroot .@ "malloc_version".

  (* Program invariant *)
  Definition malloc_codeN := (malloc_versionN.@"code").
  Definition prog_malloc_inv a f_m size secret_off secret_val  :=
    na_inv logrel_nais malloc_codeN (prog_malloc_code a f_m size secret_off secret_val ).

  (* Malloc invariant *)
  Definition mallocN := (malloc_versionN.@"malloc").
  Definition malloc_nainv b_m e_m :=
    na_inv logrel_nais mallocN (malloc_inv b_m e_m).

  (* Linking table invariant *)
  Definition link_tableN := (malloc_versionN.@"link_table").
  Definition link_table_inv
             table_addr b_link e_link a_link
             malloc_entry b_m e_m :=
    na_inv logrel_nais link_tableN
    (table_addr ↦ₐ WCap RO b_link e_link a_link
    ∗ malloc_entry ↦ₐ WCap E b_m e_m b_m)%I.


  (* This spec re-uses the specification defined in the previous section *)
  Lemma prog_malloc_spec
        (a_prog : Addr)
        wadv w0
        rmap (* resources *)
        a p b e a_first a_last (* pc *)
        f_m b_m e_m (* malloc *)
        b_link a_link e_link a_entry (* linking *)
        (size : nat) secret_off secret_val
        EN
        φ :

    let rmap_post :=
    (∃ b_l e_l,
     ([∗ map] r_i↦w_i ∈ (<[r_t1:=WCap RWX (b_l ^+ (secret_off+1))%a e_l (b_l ^+ secret_off)%a]>
                           (<[r_t2:=WInt (b_l + (secret_off+1))]>
                              (<[r_t3:=WInt e_l]>
                                 (<[r_t4:=WInt 0]> (<[r_t5:=WInt 0]> rmap))))),
       r_i ↦ᵣ w_i)
       ∗ [[(b_l ^+ (secret_off+1))%a,e_l]]↦ₐ[[region_addrs_zeroes (b_l ^+ (secret_off+1))%a e_l]]
    )%I
    in

    ExecPCPerm p →
    SubBounds b e a_first a_last ->
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    (0 <= secret_off < size %a) ->


    dom rmap = all_registers_s ∖ {[ PC; r_t0 ; r_t30 ]} →
    ↑malloc_versionN ⊆ EN ->

    ⊢ (( prog_malloc_inv a f_m size secret_off secret_val
          ∗ malloc_nainv b_m e_m
          ∗ link_table_inv b b_link e_link a_link a_entry b_m e_m
          ∗ PC ↦ᵣ WCap p b e a_first
          ∗ r_t0 ↦ᵣ w0
          ∗ r_t30 ↦ᵣ wadv
          ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
          ∗ na_own logrel_nais EN
          ∗ ▷ ( PC ↦ᵣ updatePcPerm wadv
                ∗ r_t30 ↦ᵣ wadv
                ∗ r_t0 ↦ᵣ w0
                ∗ rmap_post
                ∗ na_own logrel_nais EN
                -∗ WP Seq (Instr Executable) {{λ v, φ v ∨ ⌜v = FailedV⌝ }}))
        -∗ WP Seq (Instr Executable) {{λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros rmap_post ; subst rmap_post.
    iIntros
      (Hpc_perm Hpc_bounds Hcont Hwb Hlink Hsecret_size Hdom Hna_malloc)
      "(#Hinv_prog & #Hinv_malloc & #Hinv_link & HPC& Hr0& Hr30& Hrmap& Hna& Post)".
    simpl in *.

    (* Open the invariants *)
    iMod (na_inv_acc with "Hinv_prog Hna") as "(>Hprog & Hna & Hinv_close_prog)"
    ; auto ; try solve_ndisj.
    rewrite {1}/prog_malloc_code {1}/prog_malloc_instrs.
    iMod (na_inv_acc with "Hinv_link Hna") as "(>[Hb Ha_entry] & Hna & Hinv_close_link)"
    ; auto ; try solve_ndisj.

    (* Prepare the ressources for the use of malloc_spec *)
    (* Extract malloc from the program *)
    iDestruct (contiguous_between_program_split with "Hprog") as
      (malloc_prog rest1 link1) "(Hmalloc_prog & Hprog & #Hcont1)"
    ;[apply Hcont|].
    iDestruct "Hcont1" as %(Hcont1 & Hcont2 & Heqapp1 & Hlink1).

    (* Insert r30 in rmap *)
    assert (dom (<[r_t30:=wadv]> rmap) =
              all_registers_s ∖ {[PC; r_t0]}) as Hdomeq.
    { rewrite dom_insert_L.
      rewrite Hdom.
      rewrite - difference_difference_l_L.
      rewrite -union_difference_L; auto.
      set_solver.
    }
    iInsert "Hrmap" r_t30.

    (* Malloc spec *)
    rewrite -/(malloc _ _ _).
    iApply (wp_wand_l _ _ _ (λ v, ((φ v ∨ ⌜v = FailedV⌝) ∨ ⌜v = FailedV⌝)))%I. iSplitR.
    { iIntros (v) "[H|H] /=";auto. }
    iApply (malloc_spec _ size with
             "[- $Hmalloc_prog $Hinv_malloc $Hna $Hb $Ha_entry $HPC $Hr0 $Hrmap]")
    ; auto ; try solve_ndisj ; try lia.
    { rewrite /contiguous.isCorrectPC_range; intros.
      apply isCorrectPC_ExecPCPerm_InBounds ; auto.
      apply contiguous_between_bounds in Hcont2.
      solve_addr.
    }
    iNext.
    iIntros "(HPC & Hmalloc & Hb & Ha_entry & Hregion & Hr0 & Hna & Hgen)"
    ; iDestruct "Hregion" as (b_l e_l Hmem_size) "(Hr1 & Hmem)".

    (* Prepare ressources for the use of prof_spec_CPS *)
    (* Extract some registers *)
    iExtractList "Hgen" [r_t2;r_t3;r_t30] as ["Hr2";"Hr3";"Hadv"].

    (* Convert the [* list] of instructions into a codefrag *)
    set (prog_instrs := (encodeInstrsW
                      [Lea r_t1 secret_off; Store r_t1 secret_val; GetB r_t2 r_t1; GetE r_t3 r_t1;
                       Add r_t2 r_t2 (secret_off+1); Subseg r_t1 r_t2 r_t3; Jmp r_t30]) ).
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    iAssert (codefrag link1 prog_instrs) with "[Hprog]" as "Hprog".
    { rewrite /codefrag. simpl. rewrite /region_mapsto.
      simpl in *.
      replace rest1 with (finz.seq_between link1 (link1 ^+ 7%nat)%a).
      done.
      symmetry.
      apply region_addrs_of_contiguous_between.
      replace (link1 ^+ 7%nat)%a with a_last. done.
      apply contiguous_between_length in Hcont2.
      rewrite Hlength_prog in Hcont2.
      solve_addr. }

    (* Apply the prog_spec *)
    iApply (prog_spec_CPS with "[- $HPC $Hprog $Hr1 $Hr2 $Hr3 $Hmem $Hadv]")
    ; auto ; try solve_addr.
    { simpl in *.
      apply contiguous_between_length in Hcont2.
      rewrite Hlength_prog /= in Hcont2.
      solve_addr.
    }
    iNext.
    iIntros "(HPC& Hr1& Hr2& Hr3& Hr30& Hprog& Hmem)".

    (* Close the invariants *)
    iMod ("Hinv_close_link" with "[$Hb $Ha_entry $Hna]") as "Hna".

    iMod ("Hinv_close_prog" with "[Hprog Hmalloc $Hna]") as "Hna".
    {
    subst a.
    rewrite /prog_code /codefrag /malloc.
    iAssert (([∗ list] a_i;w ∈ (malloc_prog ++ rest1)
              ;(malloc_instrs f_m size ++ prog_instrs), a_i ↦ₐ w)%I)
            with "[Hprog Hmalloc]"
      as "Hprog'" .
    {iApply (big_sepL2_app with "[Hmalloc]") ; [done|].
      simpl. rewrite /region_mapsto.
      simpl in *.
      replace rest1 with (finz.seq_between link1 (link1 ^+ 7%nat)%a).
      done.
      symmetry.
      apply region_addrs_of_contiguous_between.
      replace (link1 ^+ 7%nat)%a with a_last. done.
      apply contiguous_between_length in Hcont2.
      rewrite Hlength_prog in Hcont2.
      solve_addr.
    }
    iFrame.
    }

    (* Apply the continuation *)
    iApply "Post". iFrame.
    replace ((b_l ^+ secret_off) ^+ 1)%a with (b_l ^+ (secret_off+1))%a by solve_addr.

    iExists _, _.
    iFrame.

    iInsertList "Hgen" [r_t3;r_t2;r_t1].
    rewrite (delete_notin); [ | apply not_elem_of_dom_1; clear -Hdom; set_solver].
    iAssumption.
  Qed.

  Lemma prog_malloc_full_run_spec
        wadv w0
        rmap (* register map *)
        a p b e a_first a_last (* pc *)
        f_m b_m e_m (* malloc *)
        b_link a_link e_link a_entry (* linking *)
        (size : nat) secret_off secret_val :

      ExecPCPerm p →
      SubBounds b e a_first a_last ->
      contiguous_between a a_first a_last →
      withinBounds b_link e_link a_entry = true →
      (a_link + f_m)%a = Some a_entry →
      (0 <= secret_off < size %a) ->

      dom rmap = all_registers_s ∖ {[ PC; r_t0 ; r_t30 ]} →

      ⊢ (( malloc_nainv b_m e_m
            ∗ prog_malloc_inv a f_m size secret_off secret_val
            ∗ link_table_inv b b_link e_link a_link a_entry b_m e_m

            ∗ PC ↦ᵣ WCap p b e a_first
            ∗ r_t0 ↦ᵣ w0
            ∗ r_t30 ↦ᵣ wadv
            ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i ∗ interp w_i )
            ∗ na_own logrel_nais ⊤

            ∗ interp wadv
            ∗ interp w0
            )
          -∗ WP Seq (Instr Executable) {{λ v,
                  (⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)%I
                  ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros *.
    iIntros
      (Hpc_perm Hpc_bounds Hcont Hwb Hlink Hsize_secret Hdom)
      "(#Hinv_malloc& #Hinv_prog& #Hinv_link& HPC& Hr0 &Hr30& Hrmap& Hown& #Hadv & #Hw0)".

    (* First and foremost, we prove that wadv is safe to execute *)
    iDestruct (jmp_to_unknown with "Hadv") as "Cont"; eauto.

    (* Apply the specification of the program *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_interp]".
    iApply (prog_malloc_spec with "[-]") ; eauto.
    iFrame ; iFrame "#".
    iNext ; iIntros "(HPC & Hr30 & Hr0 & Hrmap & Hna)"
    ; iDestruct "Hrmap" as (b_mem e_mem) "[Hrmap Hmem]".


    (* After the specificatio, the PC points to the adversary code.
       Since it is safe to share, we have a continuation that prove the full
       safe execution. But we need to manipulate the resources in order to
       use this continuation *)
    set ( rmap' := (<[r_t1:=WCap RWX (b_mem ^+ (secret_off+1))%a e_mem (b_mem ^+ secret_off)%a]>
                      (<[r_t2:=WInt (b_mem + (secret_off+1))]>
                         (<[r_t3:=WInt e_mem]>
                            (<[r_t4:=WInt 0]> (<[r_t5:=WInt 0]> rmap)))))
        ).
    (* Insert the registers r0 and r30 in the register map *)
    assert (dom (<[r_t0 := w0]> (<[r_t30:=wadv]> rmap'))
            = all_registers_s ∖ {[PC]}).
    { rewrite !dom_insert_L. rewrite Hdom.
      replace (all_registers_s ∖ {[PC]})
              with
              ({[r_t0; r_t30]} ∪ all_registers_s ∖ {[PC; r_t0; r_t30]})
      ; [set_solver|].
      rewrite - !difference_difference_l_L.
      rewrite (difference_difference_l_L _ {[r_t0]}).
      rewrite -union_difference_L; auto.
      set_solver.
    }

    (* r1 is safe to share *)
    iDestruct (region_integers_alloc' _ _ _ (b_mem ^+ secret_off)%a _ RWX  with "Hmem") as ">#Hmem"
    ; [rewrite /region_addrs_zeroes; apply Forall_replicate; auto|].

    iApply (wp_wand with "[-]").
    2: {iIntros (v) "Hv" ; by iLeft. }
    iApply ("Cont" with "[]") ; eauto ; iFrame.
    subst rmap'.

    (* We need to prove that all the registers are r -> v and interp v.
       But, the register maps is split, such that some of them are known a interp,
       but the one that have been modified by the specification are not.
       Thus, we have to extract all the new register from the map,
       recombine the [* map] over rmap, and re-insert the new registers
       into the rmap, proving both points_to and interp.
     *)
    (* First, extract the new registers *)
    iApply (big_sepM_sep_2 with "[- Hrmap_interp]").
    - by iInsertList "Hrmap" [r_t30;r_t0].
    - iApply big_sepM_intro. iDestruct "Hrmap_interp" as "#Hmap_interp".
      iIntros "!>" (r w).
      consider_next_reg r r_t0; [iIntros (Hr0) ; by inversion Hr0 |].
      consider_next_reg r r_t30; [iIntros (Hr0) ; by inversion Hr0 |].
      consider_next_reg r r_t1; [iIntros (Hr0) ; by inversion Hr0 |].
      consider_next_reg r r_t2; [iIntros (Hr0) ; inversion Hr0; by rewrite !fixpoint_interp1_eq /= |].
      consider_next_reg r r_t3; [iIntros (Hr0) ; inversion Hr0; by rewrite !fixpoint_interp1_eq /= |].
      consider_next_reg r r_t4; [iIntros (Hr0) ; inversion Hr0; by rewrite !fixpoint_interp1_eq /= |].
      consider_next_reg r r_t5; [iIntros (Hr0) ; inversion Hr0; by rewrite !fixpoint_interp1_eq /= |].
      iIntros (Hr).
      iDestruct (big_sepM_delete _ _ r with "Hmap_interp") as "[Hr_t7 Hregs]"; eauto.
Qed.

  Lemma prog_malloc_safe_to_share
        pc_b pc_e
        a a_first a_last f_m b_m e_m
        b_link e_link a_link a_entry
        (size : nat) secret_off secret_val :

    SubBounds pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    (0 <= secret_off < size %a) ->

    ⊢ prog_malloc_inv a f_m size secret_off secret_val
      ∗ malloc_nainv b_m e_m
      ∗ link_table_inv pc_b b_link e_link a_link a_entry b_m e_m

    -∗ interp (WCap E pc_b pc_e a_first).
  Proof.
    iIntros (Hpc_bounds Hcont HlinkB HlinkE Hsize) "(#Hinv_prog& #Hinv_malloc& #Hinv_link)".
    simpl.
    rewrite !fixpoint_interp1_eq /=.
    iIntros (regs).
    iNext. iModIntro.
    iIntros "(Hrsafe& Hregs& Hna)".
    iDestruct "Hrsafe" as "[%Hrfull #Hrsafe]".
    rewrite /interp_conf.
    rewrite {1}/registers_mapsto.

    (* Extract the registers from the map *)
    apply regmap_full_dom in Hrfull as Hrfull'.
    assert (is_Some (regs !! r_t0)) as [w0 Hw0];[set_solver|].
    assert (is_Some (regs !! r_t30)) as [w30 Hw30];[set_solver|].
    iExtractList "Hregs" [PC;r_t0;r_t30] as ["HPC";"Hr0";"Hr30"].

    iAssert (interp w0) as "Hw0" ; first (iApply ("Hrsafe" $! r_t0 w0) ; eauto).
    iAssert (interp w30) as "Hw30" ; first (iApply ("Hrsafe" $! r_t30 w30) ; eauto).

    iApply (wp_wand _ _ _
                    (λ v0 : language.val cap_lang,
                        (⌜v0 = HaltedV⌝ →
                         ∃ r : Reg, full_map r
                                    ∧ registers_mapsto r ∗ na_own logrel_nais ⊤)
                        ∨ ⌜v0 = FailedV⌝)%I
             with "[-]").
    2:{ iIntros (v) "Hv"; iDestruct "Hv" as "[Hv|->]" ; auto.
      iIntros ; done. }

    (* Apply the full run spec *)
    iApply (prog_malloc_full_run_spec _ _
                                      (delete r_t30 (delete r_t0 (delete PC regs)))
             with "[-]")
    ; try (iFrame ; iFrame "#")
    ; try apply ExecPCPerm_RX
    ; eauto.
    - rewrite !dom_delete_L.
      rewrite (difference_difference_l_L _ {[PC]}).
      rewrite (difference_difference_l_L _ _ {[r_t30]}).
      apply regmap_full_dom in Hrfull.
      rewrite Hrfull.
      set_solver.
    - iDestruct (big_sepM_sep _ (λ k v, interp v)%I with "[Hregs]") as "Hregs".
      { iSplitL. by iApply "Hregs". iApply big_sepM_intro. iModIntro.
        iIntros (r' ? HH). repeat eapply lookup_delete_Some in HH as [? HH].
        iApply ("Hrsafe" $! r'); auto. }
      simpl.
      iFrame.
Qed.

End malloc_program.
