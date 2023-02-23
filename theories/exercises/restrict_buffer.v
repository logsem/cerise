From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import malloc macros.
From cap_machine Require Import fundamental logrel macros_helpers rules proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine Require Import register_tactics.
Open Scope Z_scope.

(** Variant of the `subseg_buffer` where we don't restrict the range
    of the buffer, but we restrict the permission *)
Section program_ro.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.

  Definition prog_ro_code secret_off secret_val : list Word :=
    (* code: *)
    encodeInstrsW [
      Lea r_t1 secret_off ;
      Store r_t1 secret_val ;
      Restrict r_t1 (encodePerm RO) ;
      Jmp r_t30
      ].

  Definition roN := nroot .@ "roN".
  Definition prog_roN := roN .@ "prog".
  Definition prog_ro_inv a_prog secret_off secret_val :=
    na_inv logrel_nais prog_roN (codefrag a_prog (prog_ro_code secret_off secret_val)).

  Definition inv_secret secret secret_val :=
    inv (logN.@secret%a)
        (∃ w : leibnizO Word, secret ↦ₐ w ∗ (⌜w = WInt 0⌝ ∨ ⌜w = WInt secret_val⌝ ))%I.

  Definition inv_buffer addr_buffer :=
    inv (logN.@addr_buffer%a)
        (∃ w : leibnizO Word, addr_buffer ↦ₐ w ∗ (⌜w = WInt 0⌝)).

  Lemma prog_ro_spec_base
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w_adv
        (secret_off secret_val : Z)
        φ :
    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_ro_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->
    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ⊢ (( inv_secret secret secret_val
         ∗ PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
         ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
         ∗ r_t30 ↦ᵣ w_adv
         ∗ codefrag a_prog (prog_ro_code secret_off secret_val)
         ∗ ▷ ( PC ↦ᵣ updatePcPerm w_adv
               ∗ r_t1 ↦ᵣ WCap RO b_mem e_mem secret%a
               ∗ r_t30 ↦ᵣ w_adv
               ∗ codefrag a_prog (prog_ro_code secret_off secret_val)
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hlen_mem Hp_mem.
    iIntros "(#Hinv_secret& HPC& Hr1& Hr30& Hprog& Post)".
    subst secret len_p.

    codefrag_facts "Hprog".
    simpl in *.
    rewrite /prog_ro_code.
    assert (Hp_mem': ~ p_mem = E)
           by (intros -> ; simpl in Hp_mem ; discriminate).
    iGo "Hprog".
    { transitivity (Some (b_mem ^+secret_off)%a) ; auto. solve_addr. }

    (* open the invariant inv_secret, execute the instruction, close the invariant *)
    wp_instr.
    iInv "Hinv_secret" as (w_secret) ">[Hsecret [->|->]]" "Hinv_close_secret".

    all: iInstr "Hprog" ; try solve_addr.
    all:
      iMod ("Hinv_close_secret" with "[Hsecret]") as "_"
    ; try ( iNext ; iExists _ ; iFrame ; iRight ; done ) ; iModIntro.
    all: wp_pure.
    all: iInstr "Hprog";
    try (rewrite decode_encode_perm_inv;
      rewrite /writeAllowed in Hp_mem;
         destruct p_mem ; try discriminate; auto).
    all: iInstr "Hprog".

    all: iApply "Post".
    all: replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off +1))%a by solve_addr.
    all: iFrame.
  Qed.


  Lemma prog_ro_spec
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w_adv
        (secret_off secret_val : Z)
        EN φ :
    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_ro_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->
    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ↑prog_roN ⊆ EN ->

    ⊢ (( prog_ro_inv a_prog secret_off secret_val
         ∗ inv_secret secret secret_val
         ∗ PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
         ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
         ∗ r_t30 ↦ᵣ w_adv
         ∗ na_own logrel_nais EN
         ∗ ▷ ( PC ↦ᵣ updatePcPerm w_adv
               ∗ r_t1 ↦ᵣ WCap RO b_mem e_mem secret%a
               ∗ r_t30 ↦ᵣ w_adv
               ∗ na_own logrel_nais EN
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hlen_mem Hp_mem Hnainv_prog.
    iIntros "(#Hinv_prog& #Hinv_secret& HPC& Hr1& Hr30& Hna& Post)".
    subst secret len_p.

    iMod (na_inv_acc with "Hinv_prog Hna") as "(>Hprog& Hna& Hinv_close_prog)"
    ; auto.

    iApply (prog_ro_spec_base with "[-]") ; iFrameAutoSolve ; iFrame "#".
    iNext ; iIntros "(HPC & Hr1 & Hr30 & Hprog)".
    iMod ("Hinv_close_prog" with "[$Hprog $Hna]") as "Hna".
    iApply "Post".
    iFrame.
  Qed.

  (* TODO: ask if I can do diffently, I mean by defining on-the-fly
           in the proof *)
  Program Definition inv_secret_ne secret : leibnizO Word -n> iPropO Σ :=
    λne w, (⌜w = WInt 0⌝ ∨ ⌜w = WInt secret⌝)%I.
  Program Definition inv_buffer_ne : leibnizO Word -n> iPropO Σ :=
    λne w, ⌜w = WInt 0⌝%I.

  Lemma prog_ro_spec_full
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w_adv
        (secret_off secret_val : Z)
        rmap :

    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_ro_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->
    (* the adversary code contains only instructions *)
    dom rmap = all_registers_s ∖ {[ PC; r_t1; r_t30 ]} →

    ⊢ (( prog_ro_inv a_prog secret_off secret_val
         ∗ inv_secret secret secret_val
         ∗ ([∗ list] a ∈ (finz.seq_between b_mem secret), inv_buffer a )
         ∗ ([∗ list] a ∈ (finz.seq_between (secret ^+1)%a e_mem), inv_buffer a)
         ∗ PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
         ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
         ∗ r_t30 ↦ᵣ w_adv
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
         ∗ na_own logrel_nais ⊤
         ∗ interp w_adv)
       -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hvsecret Hp_mem Hrmap_dom.
    iIntros "(#Hinv_prog & #Hinv_secret & #Hinv_mem & #Hinv_mem' & HPC & Hr1 & Hr30 & Hrmap & Hna & #Hinterp_adv)".

    (* Prove that the capability pointing to the adversary code is safe to
       execute using the FTLR. *)

    iDestruct (jmp_to_unknown with "Hinterp_adv") as "Cont".

    iApply (prog_ro_spec with "[-]") ; eauto.
    iFrame ; iFrame "#".
    iNext ; iIntros "(HPC & Hr1 & Hr30 & Hna)".
    (* Show that the contents of r1 are safe *)
    iAssert ( interp (WCap RO b_mem e_mem (b_mem ^+ secret_off)%a))
      as "#Hmem_safe".
    {
     rewrite /interp /=.
     rewrite (fixpoint_interp1_eq (WCap RO b_mem e_mem _)) /=.
     rewrite (finz_seq_between_split b_mem (b_mem ^+secret_off)%a e_mem)
     ; [|subst secret ; solve_addr].
     rewrite (finz_seq_between_cons (b_mem ^+secret_off)%a e_mem)
     ; [|subst secret ; auto].
     replace ((b_mem ^+ secret_off) ^+ 1)%a
       with (b_mem ^+ (secret_off+1))%a
            by (subst secret ; by solve_addr).
     iApply big_sepL_app.
     iSplitL ; cycle 1.
     iApply big_sepL_cons.
     iSplitL.
     {
     iClear "Cont Hinterp_adv Hinv_mem Hinv_prog".
     rewrite /inv_secret; subst secret.
     iExists (inv_secret_ne secret_val). rewrite /inv_secret_ne.
     iFrame "#".
     iNext ; iModIntro.
     iIntros (w) "[->|->]" ; iApply interp_int.
     }
     3: solve_addr.
     all: subst secret;
       replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr.
     1: iApply (big_sepL_mono with "Hinv_mem'").
     2: iApply (big_sepL_mono with "Hinv_mem").
     all: iIntros (???) "Hinv_buffer".
     all:
       iExists inv_buffer_ne
     ; rewrite /inv_buffer /=
     ; iSplitL ; try iApply "Hinv_buffer".
     all: iNext ; iModIntro; iIntros (w) "->" ; iApply interp_int.
    }

    (* TODO tactic to do that automatically ? *)
    (* put the registers woth capability back into the register map *)
    iDestruct (big_sepM_insert _ _ r_t30 with "[$Hrmap Hr30]") as "Hrmap".
    { apply not_elem_of_dom.
    rewrite Hrmap_dom. set_solver+. }
    { by iFrame. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap Hr1]") as "Hrmap".
    { rewrite !lookup_insert_ne //. apply not_elem_of_dom.
    rewrite Hrmap_dom. set_solver+. }
    { by iFrame ; iFrame "#". }

    iApply "Cont"; cycle 1. iFrame. iPureIntro. rewrite !dom_insert_L Hrmap_dom.
    rewrite !singleton_union_difference_L. set_solver+.
  Qed.

 (** As the subseg variant, we can't prove that this program is safe to share.
     We have to create a closure around both buffer and program, or dynamically
     allocate the memory. *)

End program_ro.


Section program_closure_ro.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.
  Definition closure_roN : namespace := nroot .@ "closure_ro".

  (* TODO: the load section already exists in `subseg_buffer.v`,
           I shouldn't rewrite it here *)

  (* we assume pc_b contains the capability pointing the allocated buffer
     this code load the capability in R1 *)
  Definition load_code :=
   encodeInstrsW [
        Mov r_t1 PC; (* r1 => (RWX, pc_b, pc_e, a_first) *)
        GetB r_t2 r_t1; (* r2 => pc_b *)
        GetA r_t3 r_t1; (* r3 => a_first *)
        Sub r_t2 r_t2 r_t3; (* r2 => (pc_b - a_first) *)
        Lea r_t1 r_t2; (* r1 => (RWX, pc_b, pc_e, pc_b) *)
        Load r_t1 r_t1 (* r1 => (p_mem, b_mem, e_mem, b_mem) *)
     ].

  Definition closure_ro_code secret_off secret_val :=
    load_code ++ prog_ro_code secret_off secret_val.

  (** We define the invariants *)
  (* cap_addr points to the capability for the buffer *)
  Definition cap_memN := roN.@"cap_mem".
  Definition cap_mem_inv p_mem b_mem e_mem cap_addr :=
    na_inv logrel_nais cap_memN
           (cap_addr ↦ₐ WCap p_mem b_mem e_mem b_mem).

  (** Specifications *)

  (* We specify the closure program in a modular way, so we firstly specifie
     the part of the code that load the capability *)
  Lemma load_spec p_pc b_pc e_pc s_load (* pc *)
        p_mem b_mem e_mem (* mem *)
        w1 w2 w3
        EN φ :

    let e_load := (s_load ^+ length load_code)%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_load e_load ->

    writeAllowed p_mem = true ->

    ↑cap_memN ⊆ EN ->

    ⊢ ( cap_mem_inv p_mem b_mem e_mem b_pc
        ∗ PC ↦ᵣ WCap p_pc b_pc e_pc s_load
        ∗ r_t1 ↦ᵣ w1
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        ∗ codefrag s_load load_code
        ∗ na_own logrel_nais EN
        ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_load
              ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
              ∗ (∃ n2, r_t2 ↦ᵣ WInt n2)
              ∗ (∃ n3, r_t3 ↦ᵣ WInt n3)
              ∗ codefrag s_load load_code
              ∗ na_own logrel_nais EN
              -∗
                WP Seq (Instr Executable) {{ φ }}
            )
        -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros end_load ; subst end_load.
    iIntros (Hpc_perm Hpc_bounds Hp_mem Hnainv_cap)
            "(#Hinv_cap & HPC & Hr1 & Hr2 & Hr3 & Hprog & Hna & Post)".
    simpl in *.
    codefrag_facts "Hprog".
    iMod (na_inv_acc with "Hinv_cap Hna") as "(>Hcap& Hna& Hinv_close)" ; auto.
    iGo "Hprog".
    { transitivity (Some b_pc); eauto. solve_addr. }
    iGo "Hprog".
    iMod ("Hinv_close" with "[Hcap Hna]") as "Hna" ; iFrame.
    iApply "Post". iFrame.
    iSplitL "Hr2" ; iExists _ ; iFrame.
  Qed.


  Definition code_closure_roN := roN .@ "prog_closure".
  Definition code_closure_ro_inv a_prog secret_off secret_val :=
    na_inv logrel_nais code_closure_roN (codefrag a_prog (closure_ro_code secret_off secret_val)).

  Lemma closure_ro_spec
        pc_p pc_b pc_e s_closure_ro
        p_mem b_mem e_mem
        w1 w2 w3 w_adv
        (secret_off secret_val : Z)
        EN
        φ :

    let secret := (b_mem^+secret_off)%a in
    let e_closure_ro := (s_closure_ro ^+ length (closure_ro_code secret_off secret_val))%a in

    ExecPCPerm pc_p ->
    SubBounds pc_b pc_e s_closure_ro e_closure_ro ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ↑roN ⊆ EN ->

    ⊢ ( inv_secret secret secret_val
        ∗ code_closure_ro_inv s_closure_ro secret_off secret_val
        ∗ cap_mem_inv p_mem b_mem e_mem pc_b
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e s_closure_ro
        ∗ r_t1 ↦ᵣ w1
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        ∗ r_t30 ↦ᵣ w_adv
        ∗ na_own logrel_nais EN
        ∗ ▷ ( PC ↦ᵣ updatePcPerm w_adv
              ∗ r_t1 ↦ᵣ WCap RO b_mem e_mem secret%a
              ∗ (∃ n2, r_t2 ↦ᵣ WInt n2)
              ∗ (∃ n3, r_t3 ↦ᵣ WInt n3)
              ∗ r_t30 ↦ᵣ w_adv
              ∗ na_own logrel_nais EN
              -∗ WP Seq (Instr Executable) {{ φ }})
        -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros secret e_closure_ro ; subst secret e_closure_ro.
    iIntros (Hpc_perm Hpc_bounds Hvsecret Hp_mem Hnainv)
            "(#Hinv_secret & #Hinv_code & #Hinv_cap & HPC & Hr1 & Hr2 & Hr3 & Hr30 & Hna & Post)".
    rewrite /code_closure_ro_inv.

    iMod (na_inv_acc with "Hinv_code Hna")
      as "(>Hprog & Hna & Hprog_close)"
    ; auto ; try solve_ndisj.
    rewrite {2}/closure_ro_code.

    focus_block_0 "Hprog" as "Hload" "Hcont".
    iApply (load_spec with "[-]")
    ; try (iFrame ; iFrame "#")
    ; eauto
    ; try solve_ndisj.
    iNext.
    iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hload & Hna)".
    clear w2 w3.
    iDestruct "Hr2" as (n2) "Hr2"; iDestruct "Hr3" as (n3) "Hr3".
    unfocus_block "Hload" "Hcont" as "Hprog" .

    focus_block 1%nat "Hprog" as a_mid Ha_mid "Hprog" "Hcont".
    iApply (prog_ro_spec_base with "[-]")
    ; try (iFrame; iFrame "#")
    ; eauto
    ; try solve_ndisj.
    iNext.
    iIntros "(HPC & Hr1 & Hr30 &Hprog)".
    unfocus_block "Hprog" "Hcont" as "Hprog" .

    iMod ("Hprog_close" with "[$Hprog $Hna]") as "Hna".
    iApply "Post" ; iFrame ; iFrame "#".
    iSplitL "Hr2" ; iExists _ ; iFrame.
  Qed.

  Lemma closure_ro_spec_full
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w_adv
        (secret_off secret_val : Z)
        rmap :

    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (closure_ro_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->
    dom rmap = all_registers_s ∖ {[ PC; r_t30 ]} →

    ⊢ (( inv_secret secret secret_val
        ∗ code_closure_ro_inv a_prog secret_off secret_val
        ∗ cap_mem_inv p_mem b_mem e_mem b_pc
         ∗ ([∗ list] a ∈ (finz.seq_between b_mem secret), inv_buffer a )
         ∗ ([∗ list] a ∈ (finz.seq_between (secret ^+1)%a e_mem), inv_buffer a)

         ∗ PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
         ∗ r_t30 ↦ᵣ w_adv
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
         ∗ na_own logrel_nais ⊤
         ∗ interp w_adv)
       -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hvsecret Hp_mem Hrmap_dom.
    iIntros
      "(#Hinv_secret & #Hinv_prog & #HCap & #Hinv_mem & #Hinv_mem' & HPC & Hr30 & Hrmap & Hna & #Hinterp_adv)".

    (* FTLR on V(w_adv) *)
    iDestruct (jmp_to_unknown with "Hinterp_adv") as "Cont".

    (* Preparation resources for `closure_ro_spec` *)

    iExtractList "Hrmap" [r_t1;r_t2;r_t3] as ["[Hr1 _]";"[Hr2 _]";"[Hr3 _]"].
    (* Extract the register r_t1 - r_t3 *)

    iApply (closure_ro_spec with "[-]")
    ; try (iFrame "∗ #") ; eauto.
    iNext
    ; iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hr30 & Hna)"
    ; iDestruct "Hr2" as (n2) "Hr2"
    ; iDestruct "Hr3" as (n3) "Hr3".

    (* In order to use the continuation, we have to re-insert the registers
       r3, r2, r1 and r30 in the map, and thus to prove that they are safe to share.
       For r3, r2 and r30 it's trivial, but there is some work to do for r1. *)

    (* r1 is safe to share *)
    iAssert ( interp (WCap RO b_mem e_mem (b_mem ^+ secret_off)%a))
      as "#Hmem_safe".
    {
     rewrite /interp /=.
     rewrite (fixpoint_interp1_eq (WCap RO b_mem e_mem (b_mem ^+ secret_off)%a)) /=.
     rewrite (finz_seq_between_split b_mem (b_mem ^+secret_off)%a e_mem)
     ; [|subst secret ; solve_addr].
     rewrite (finz_seq_between_cons (b_mem ^+secret_off)%a e_mem)
     ; [|subst secret ; auto].
     replace ((b_mem ^+ secret_off) ^+ 1)%a
       with (b_mem ^+ (secret_off+1))%a
            by (subst secret;solve_addr).
     iApply big_sepL_app.
     iSplitL ; cycle 1.
     iApply big_sepL_cons.
     iSplitL.
     {
     iClear "Cont Hinterp_adv Hinv_mem Hinv_prog".
     rewrite /inv_secret; subst secret.
     iExists (inv_secret_ne secret_val). rewrite /inv_secret_ne.
     iFrame "#".
     iNext ; iModIntro.
     iIntros (w) "[->|->]" ; iApply interp_int.
     }
     3: solve_addr.
     all: subst secret;
       replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr.
     1: iApply (big_sepL_mono with "Hinv_mem'").
     2: iApply (big_sepL_mono with "Hinv_mem").
     all: iIntros (???) "Hinv_buffer".
     all:
       iExists inv_buffer_ne
     ; rewrite /inv_buffer /=
     ; iSplitL ; try iApply "Hinv_buffer".
     all: iNext ; iModIntro; iIntros (w) "->" ; iApply interp_int.
    }

    iCombine "Hr1 Hmem_safe" as "Hr1".
    iPoseProof (interp_int n2)%I as "Hr2_safe"; iCombine "Hr2 Hr2_safe" as "Hr2".
    iPoseProof (interp_int n3)%I as "Hr3_safe"; iCombine "Hr3 Hr3_safe" as "Hr3".
    iCombine "Hr30 Hinterp_adv" as "Hr30".
    iInsertList "Hrmap" [r_t1;r_t2;r_t3;r_t30].

    (* Apply the continuation *)
    iApply "Cont" ; [|iFrame].
    iPureIntro.
    rewrite !dom_insert_L Hrmap_dom.
    rewrite !singleton_union_difference_L. set_solver+.
  Qed.

  Lemma closure_ro_safe_to_share
        b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        (secret_off secret_val : Z) :

    let secret := (b_mem^+secret_off)%a in
    SubBounds b_pc e_pc a_prog (a_prog ^+ length (closure_ro_code secret_off secret_val))%a ->
    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ⊢ ((inv_secret secret secret_val
        ∗ code_closure_ro_inv a_prog secret_off secret_val
        ∗ cap_mem_inv p_mem b_mem e_mem b_pc
        ∗ ([∗ list] a ∈ (finz.seq_between b_mem secret), inv_buffer a )
        ∗ ([∗ list] a ∈ (finz.seq_between (secret ^+1)%a e_mem), inv_buffer a))
       -∗ interp (WCap E b_pc e_pc a_prog)).
  Proof.
    intro secret ; subst secret ; simpl.
    iIntros (Hpc_bounds Hvsecret Hp_mem)
            "(#Hinv_secret & #Hinv_code & #Hinv_cap & #Hinv_mem & #Hinv_mem')".
    rewrite fixpoint_interp1_eq /= /interp_conf.
    iIntros (regs) ; iNext ; iModIntro.
    iIntros "([%Hrfull #Hrsafe] & Hregs & Hna)".
    rewrite /registers_mapsto.

    (* Prepare the resources for closure_ro_spec_full *)

    iDestruct (big_sepM_insert_delete with "Hregs") as "[HPC Hregs]".
    assert (is_Some (regs !! r_t30)) as [w30 Hw30] by apply Hrfull.
    iDestruct (big_sepM_delete _ _ r_t30  with "Hregs") as "[Hr30 Hregs]".
    { rewrite !lookup_delete_ne ; eauto. }
    iAssert (interp w30) as "Hw30".
    { iApply ("Hrsafe" $! r_t30 w30) ; eauto.  }

    iApply (closure_ro_spec_full
              RX b_pc e_pc a_prog
              p_mem b_mem e_mem
              w30
              secret_off secret_val
              (delete r_t30 (delete PC regs))
             with "[-]")
    ; eauto
    ; try apply ExecPCPerm_RX
    ; try (iFrame ; iFrame "#").
   - rewrite !dom_delete_L.
     rewrite difference_difference_L.
     apply regmap_full_dom in Hrfull; rewrite Hrfull.
     set_solver.
   - iDestruct (big_sepM_sep _ (λ k v, interp v)%I with "[Hregs]") as "Hregs".
     { iSplitL. by iApply "Hregs". iApply big_sepM_intro. iModIntro.
       iIntros (r' ? HH). repeat eapply lookup_delete_Some in HH as [? HH].
       iApply ("Hrsafe" $! r'); auto. }
     simpl.
     iFrame.
Qed.

End program_closure_ro.
