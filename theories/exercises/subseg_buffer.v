From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import malloc macros.
From cap_machine Require Import fundamental logrel macros_helpers rules proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine.exercises Require Import register_tactics.
Open Scope Z_scope.


(** Exercise - the region is already allocated and the capability pointing to this
    region is in R1. As a first step, the adversary code is known and just halts. *)
Section base_program.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (** r_mem is the register that contains the capability pointing to
      the allocated buffer
      secret_off is the offset of the secret in the buffer
      secret is the value stored in the buffer
   *)
  Definition prog_base_instrs r_mem (secret_off secret : Z) : list Word :=
    encodeInstrsW [
      Lea r_mem secret_off ;
      Store r_mem secret ;
      GetB r_t2 r_mem ;
      GetE r_t3 r_mem ;
      Add r_t2 r_t2 (secret_off + 1) ;
      Subseg r_mem r_t2 r_t3
      ].

  (** Jump to the adversary in register r30 at the end of the program *)
  Definition prog_code secret_off secret_val: list Word :=
    prog_base_instrs r_t1 secret_off secret_val ++ encodeInstrsW [Jmp r_t30].

  (** The adversary code is known --- it just halts *)
  Definition adv_code : list Word :=
    encodeInstrsW [ Halt ].

  (** Specification of :
      - executes the first part
      - jump to the adversary
      - halts
   *)
  Lemma prog_spec (a_adv: Addr)
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        secret_off secret_val
        w2 w3 :
    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ⊢ ( (* PC points to prog_code*)
        PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ codefrag a_prog (prog_code secret_off secret_val)
        (* r1 points to the allocated memory*)
        ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
        (* which is filled by zeroes *)
        ∗ [[b_mem, e_mem]] ↦ₐ [[ region_addrs_zeroes b_mem e_mem ]]
        (* r30 point to the adversary code *)
        ∗ r_t30 ↦ᵣ WCap E a_adv (a_adv ^+ (length adv_code))%a a_adv
        ∗ codefrag a_adv adv_code
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        -∗ WP Seq (Instr Executable) {{
                λ v, ⌜v = HaltedV⌝ -∗ (* The machine is halted after the adversary *)
                     r_t1 ↦ᵣ WCap p_mem (b_mem^+(secret_off+1))%a e_mem secret%a
                     ∗ r_t2 ↦ᵣ WInt (b_mem+(secret_off +1))
                     ∗ r_t3 ↦ᵣ WInt e_mem
                     ∗ codefrag a_prog (prog_code secret_off secret_val)
                     ∗ codefrag a_adv adv_code
                     ∗ secret ↦ₐ WInt secret_val
                     ∗ [[b_mem, secret]] ↦ₐ [[ region_addrs_zeroes b_mem secret]]
                     ∗ [[(secret ^+1)%a, e_mem]] ↦ₐ [[ region_addrs_zeroes (secret^+1)%a e_mem ]]
      }})%I.

  Proof.
    intros * Hpc_perm Hpc_bounds Hlen_mem Hp_mem.
    iIntros "(HPC& Hprog& Hr1& Hmem& Hr30& Hadv& Hr2& Hr3)".

    (* 1 - prepare the assertions for the proof *)
    subst secret len_p.
    (* Derives the facts from the codefrag *)
    codefrag_facts "Hprog".
    codefrag_facts "Hadv".
    simpl in *.
    rewrite /prog_code.
    (* This assertion will be helpful seeral times during the proof *)
    assert (Hp_mem': ~ p_mem = E)
           by (intros -> ; simpl in Hp_mem ; discriminate).

    (* 2 - Use the WP rules for each instructions *)
    (* Lea r_t1 3 *)
    iInstr "Hprog".
    { transitivity (Some (b_mem ^+secret_off)%a) ; auto. solve_addr. }
    (* Store r_t1 42 , where r_t1 = (RWX, b, e, secret) *)
    (* The store requires the resource `secret ↦ₐ w` for some w,
       we thus extract the resource from the memory buffer *)
    rewrite (region_addrs_zeroes_split b_mem (b_mem ^+secret_off)%a e_mem)
    ; [| solve_addr].
    iDestruct (region_mapsto_split
                 b_mem e_mem
                 (b_mem ^+secret_off)%a
                 (region_addrs_zeroes b_mem (b_mem ^+secret_off)%a)
                 (region_addrs_zeroes (b_mem ^+secret_off)%a e_mem)
                with "Hmem") as "[Hmem Hmem']".
    { solve_addr. }
    { unfold region_addrs_zeroes. by rewrite replicate_length. }
    unfold region_addrs_zeroes at 2.
    rewrite finz_dist_S ; [|solve_addr].
    rewrite replicate_S.
    iDestruct (region_mapsto_cons (b_mem ^+secret_off)%a _ e_mem (WInt 0)
                                   (region_addrs_zeroes _ e_mem)
                with "Hmem'") as "[Hsecret Hmem']".
    { transitivity (Some (b_mem ^+(secret_off +1))%a) ; auto. solve_addr. }
    { solve_addr. }
    (* Now that we have the secret address, we can continue *)
    iInstr "Hprog".
    { solve_addr. }
    (* getB, getE, add, subseg *)
    iGo "Hprog".
    { transitivity (Some (b_mem ^+(secret_off+1))%a) ; auto. solve_addr. }
    { solve_addr. }
    (* jmp *)
    iInstr "Hprog".
    (* halts in the adversary code *)
    rewrite /adv_code.
    iInstr "Hadv".

    (* 3 - The machine is halted, prove that the post condition holds *)
    wp_end.
    iIntros "_".
    replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr.
    iFrame.
  Qed.

End base_program.

(** We use a CPS specification. We don't know the adversary code,
    thus we stop the specification after the jump. We give only the necessary
    ressources. *)
Section base_program_CPS.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  Local Ltac solve_addr' :=
    repeat match goal with x := _ |- _ => subst x end
    ; solve_addr.

  Local Ltac iGo' hprog :=
    repeat
    (iGo hprog ;
    try (
    match goal with
    | h: _ |- isCorrectPC _ =>
        apply isCorrectPC_ExecPCPerm_InBounds ; auto; solve_addr'
    end)
    ; try solve_addr').

  (** Specification of the program before the jump to the adversary.
      The specification and the proof are essentially the same as the
      previous one. *)
  Lemma prog_base_spec
        r_mem secret_off secret (* instantiation prog_base *)
        p_pc b_pc e_pc s_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w2 w3
        φ :

    let e_prog := (s_prog ^+ length (prog_base_instrs r_mem secret_off secret))%a in
    let a_secret := (b_mem ^+ secret_off)%a in

    (* Validity pc *)
    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_prog e_prog ->

    (* Validity buffer *)
    ( b_mem <= a_secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    (* Specification *)
    ⊢ (( PC ↦ᵣ WCap p_pc b_pc e_pc s_prog
         ∗ r_mem ↦ᵣ WCap p_mem b_mem e_mem b_mem
         ∗ r_t2 ↦ᵣ w2
         ∗ r_t3 ↦ᵣ w3
         ∗ [[b_mem, e_mem]] ↦ₐ [[ region_addrs_zeroes b_mem e_mem ]]
         ∗ codefrag s_prog (prog_base_instrs r_mem secret_off secret)
         ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_prog
               ∗ r_mem ↦ᵣ WCap p_mem (a_secret^+1)%a e_mem a_secret
               ∗ r_t2 ↦ᵣ WInt (b_mem+secret_off+1)
               ∗ r_t3 ↦ᵣ WInt e_mem
               ∗ [[b_mem, a_secret]] ↦ₐ [[ region_addrs_zeroes b_mem a_secret ]]
               ∗ a_secret ↦ₐ WInt secret
               ∗ [[(a_secret ^+1)%a, e_mem]] ↦ₐ [[ region_addrs_zeroes (a_secret^+1)%a e_mem ]]
               ∗ codefrag s_prog (prog_base_instrs r_mem secret_off secret)
               -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof with (try solve_addr').
    intros e_prog a_secret.
    iIntros (Hpc_perm Hpc_bounds Hsecret_bounds Hp_mem)
            "(HPC & Hr_mem & Hr2 & Hr3 & Hmem & Hprog & Post)".
    rewrite /region_mapsto.
    codefrag_facts "Hprog".
    iGo' "Hprog".
    { transitivity (Some (b_mem ^+ secret_off)%a) ; auto ; solve_addr'. }
    { intros -> ; simpl in Hp_mem ; discriminate. }

    rewrite (region_addrs_zeroes_split b_mem a_secret e_mem)...
    iDestruct (region_mapsto_split
                 b_mem e_mem
                 a_secret
                 (region_addrs_zeroes b_mem a_secret)
                 (region_addrs_zeroes a_secret e_mem)
                with "Hmem") as "[Hmem Hmem']"...
    { unfold region_addrs_zeroes. by rewrite replicate_length. }
    unfold region_addrs_zeroes at 4.
    rewrite finz_dist_S...
    rewrite replicate_S.
    iDestruct (region_mapsto_cons a_secret (a_secret ^+1)%a e_mem (WInt 0)
                                   (region_addrs_zeroes _ e_mem)
                with "Hmem'") as "[Hsecret Hmem']"...
    iGo' "Hprog".
    (* getB getE add subseg *)
    { transitivity (Some (b_mem ^+ (secret_off + 1))%a) ; auto... }
    { intros -> ; simpl in Hp_mem ; discriminate. }
    { solve_addr'. }

    (* Post condition *)
    iApply "Post".
    subst e_prog; simpl in *.
    replace (b_mem ^+ (secret_off + 1))%a with (a_secret ^+ 1)%a by solve_addr'.
    replace (b_mem + secret_off + 1) with (b_mem + (secret_off + 1)) by lia.
    iFrame.
  Qed.
    

  (** Specification of the program until the jump to the unknown adversary code *)
  Lemma prog_spec_CPS
        wadv
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w2 w3
        secret_off secret_val
        φ :
    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ⊢ ( (* PC points to prog_code*)
        ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
        ∗ codefrag a_prog (prog_code secret_off secret_val)
          (* r1 points to the allocated memory*)
          ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
          (* which is filled by zeroes *)
          ∗ [[b_mem, e_mem]] ↦ₐ [[ region_addrs_zeroes b_mem e_mem ]]
          (* r30 point to the adversary code *)
          ∗ r_t30 ↦ᵣ wadv
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          ∗ ▷ ( PC ↦ᵣ updatePcPerm wadv (* The specification stops after the jump *)
                ∗ r_t1 ↦ᵣ WCap p_mem (b_mem^+(secret_off+1))%a e_mem secret%a
                ∗ r_t2 ↦ᵣ WInt (b_mem+(secret_off +1))
                ∗ r_t3 ↦ᵣ WInt e_mem
                ∗ r_t30 ↦ᵣ wadv
                ∗ codefrag a_prog (prog_code secret_off secret_val)
                ∗ [[(secret ^+1)%a, e_mem]] ↦ₐ [[ region_addrs_zeroes (secret^+1)%a e_mem ]]
                -∗ WP Seq (Instr Executable) {{ φ }}))
        -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hlen_mem Hp_mem.
    iIntros "(HPC& Hprog& Hr1& Hmem& Hr30& Hr2& Hr3& Post)".
    rewrite /prog_code.
    codefrag_facts "Hprog".
    focus_block_0 "Hprog" as "Hprog" "Hcont".
    (* 1 - Specification from Lea to Subsug *)
    iApply (prog_base_spec with "[-]")
    ; try (iFrame ; iFrame "#")
    ; eauto
    ; try solve_addr'.
    iNext ; iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hmem & Hsecret & Hmem' & Hprog)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    (* 2 - Jump to the adversary *)
    (* jmp *)
    iInstr "Hprog".
    (* 3 - Post condition *)
    iApply "Post".
    subst secret.
    replace ((b_mem ^+ secret_off) ^+ 1)%a with (b_mem ^+ (secret_off+1))%a by solve_addr.
    replace  (b_mem + secret_off + 1)%Z with (b_mem + (secret_off + 1))%Z by lia.
    iFrame.
  Qed.

  Context {nainv: logrel_na_invs Σ}.

  (** Assuming that the word of the adversary is safe to share,
     the machine executes safely and completely.
     The assumption makes sense, because we consider adversary programs containing
     no capabilities. *)
  Lemma prog_spec_CPS_full
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w_adv
        secret_off secret_val
        rmap :

    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_code secret_off secret_val))%a in

      (* Validity PC*)
      ExecPCPerm p_pc ->
      SubBounds b_pc e_pc a_prog len_p ->

      (* Validity buffer *)
      (b_mem <= secret < e_mem)%a ->
      writeAllowed p_mem = true ->

      (* Register map for the big_sep of registers *)
      dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t1; r_t30 ]} →

      ⊢ ( PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
          ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
          ∗ r_t30 ↦ᵣ w_adv
          ∗ codefrag a_prog (prog_code secret_off secret_val)
          ∗ [[b_mem, e_mem]] ↦ₐ [[ region_addrs_zeroes b_mem e_mem ]]
          (* All the registers contains integers *)
          ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
          (* The NA token is required for the post condition *)
          ∗ na_own logrel_nais ⊤
          (* The adversary word is safe to share *)
          ∗ interp w_adv
          (* Post condition of the corollary of the FTLR *)
          -∗ WP Seq (Instr Executable)
                {{ v, ⌜v = HaltedV⌝ → (* if the machine halts *)
                     (* we own all the registers *)
                      ∃ r : Reg, full_map r ∧ registers_mapsto r
                      (* all the NA invariants are closed*)
                      ∗ na_own logrel_nais ⊤}})%I.

  Proof.
    intros * Hpc_perm Hpc_bounds Hvsecret Hp_mem Hrmap_dom.
    iIntros "(HPC & Hr1 & Hr30 & Hprog & Hregion & Hrmap & Hna & #Hadv)".


    (* Using the FLTR corollary, w_adv is safe to execute and we can specify
       what happens after the jump: safe and complete execution *)
    (* It is required to do it _before_ the specification, because it introduces a
       later modality *)
    iDestruct (jmp_to_unknown with "Hadv") as "Cont".

    (* 1 - Specification of the known program *)
    (* Extract the register r_t2 and r_t3, required for `prog_spec_CPS` *)
    extract_register r_t2 with "Hrmap" as (w2 Hw2) "[[Hr2 _] Hrmap]".
    extract_register r_t3 with "Hrmap" as (w3 Hw3) "[[Hr3 _] Hrmap]".

    iApply (prog_spec_CPS with "[-]") ; try eassumption.
    iFrame "HPC Hr1 Hr30 Hregion Hr2 Hr3 Hprog".
    iNext ; iIntros "(HPC& Hr1& Hr2& Hr3 & Hr30 & Hprog & Hmem)".

    (* 2 - The continuation requires all the registers to be safe to share *)
    (* Show that the contents of r1 are safe *)
    replace ((b_mem ^+ secret_off) ^+ 1)%a
      with (b_mem ^+ (secret_off+1))%a by (subst secret ; by solve_addr).
    rewrite /region_mapsto.
    iDestruct (region_integers_alloc' _ _ _ (b_mem ^+ secret_off)%a _ p_mem with "Hmem")
      as ">#Hmem_safe".
    { rewrite /region_addrs_zeroes. apply Forall_replicate. auto. }

    (* put the other registers back into the register map *)
    insert_register r_t3 with "[$Hrmap Hr3]" as "Hrmap".
    insert_register r_t2 with "[$Hrmap Hr2]" as "Hrmap".

    (* Show that the contents of unused registers is safe *)
    set (rmap' :=  <[r_t2:=WInt _]> (<[r_t3:= _]> rmap)).
    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp w)%I with "[Hrmap]" as "Hrmap".
    { subst rmap'.
      iApply (big_sepM_mono with "Hrmap"). intros r w Hr'. cbn. iIntros "[? %Hw]". iFrame.
      destruct w; [| by inversion Hw]. rewrite fixpoint_interp1_eq //. }

    (* put the registers with capability back into the register map *)
    insert_register r_t30 with "[$Hrmap Hr30]" as "Hrmap".
    insert_register r_t1 with "[$Hrmap Hr1]" as "Hrmap".

    (* 3 - Use the continuation *)

    (* Prepare the resources *)
    set (rmap'' := <[r_t1:=WCap p_mem (b_mem ^+ (secret_off + 1))%a e_mem (b_mem ^+ secret_off)%a]>
                     (<[r_t30:= w_adv]> rmap')).
    assert (dom (gset RegName) rmap'' = all_registers_s ∖ {[PC]}) as Hdomeq.
    { do 2 (rewrite dom_insert_L).
      assert (all_registers_s ∖ {[PC]} =
                ({[r_t1; r_t30]} ∪ all_registers_s ∖ {[PC; r_t1; r_t30]})) as ->.
      { rewrite - !difference_difference_L.
        assert ( all_registers_s ∖ {[PC]} ∖ {[r_t1]} ∖ {[r_t30]} =
                   all_registers_s ∖ {[PC]} ∖ {[r_t1; r_t30]})
          as -> by (rewrite - !difference_difference_L ; set_solver).
        rewrite -union_difference_L; auto.
        apply subseteq_difference_r;[set_solver|].
        apply all_registers_subseteq. }
      set_solver. }
    iApply "Cont" ; eauto. iFrame.

    (* Alternative for (3) *)
    (* iApply (wp_wand with "[-]"). *)
    (* { iApply "Cont"; cycle 1. iFrame. iPureIntro. rewrite !dom_insert_L Hrmap_dom. *)
    (*   rewrite !singleton_union_difference_L. set_solver+. } *)
    (* iIntros (?) "?" ; done. *)
  Qed.

(** The encapsulation of the program is safe-to-share
    By unfolding the definition of V(E,-,-,-) , we can use only persistent
    proposition. Thus, all the required resources of the memory have to be
    encapsulated in invariants. *)

  Definition N : namespace := nroot .@ "secret".
  Definition start_memN := (N.@"start_mem").
  Definition secretN := (N.@"secret").
  Definition end_memN := (N.@"end_mem").
  Definition codeN := (N.@"code").

  (* The first part of the buffer, before the secret, is always zeroes *)
  Definition start_mem_inv (b_mem e_mem : Addr) secret_off:=
    let secret_addr := (b_mem ^+ secret_off)%a in
    na_inv logrel_nais start_memN
           ([[b_mem, secret_addr]] ↦ₐ [[ region_addrs_zeroes b_mem secret_addr ]]).

  (* The secret is either equal to 0 -- at the initialisation -- or equal to
     42 -- after the secret was stored *)
  Definition secret_inv (b_mem : Addr) secret_off secret :=
    let secret_addr := (b_mem ^+ secret_off)%a in
    na_inv logrel_nais secretN
           ((secret_addr ↦ₐ WInt 0) ∨ (secret_addr ↦ₐ WInt secret)).

  (* The code instruction is stored in an invariant as well *)
  Definition code_inv a_prog secret_off secret :=
    na_inv logrel_nais codeN (codefrag a_prog (prog_code secret_off secret)).

  Definition end_mem_inv b_mem e_mem secret_off :=
    let n_secret_addr := (b_mem ^+ (secret_off +1))%a in
    na_inv logrel_nais end_memN
           ([∗ list] a ∈ finz.seq_between n_secret_addr e_mem,
            ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp)%I.


  (** Currently, we cannot prove the closure, because we need more information
      about the buffer. Since the closure means "called in any context",
      we cannot assume that the buffer is correctly set up in the context,
      i.e. we cannot assume that the register r1 contains the capability
      pointing to the buffer.

      In order to get the right context, we may change our code. Here is 2
      solutions:
      - we assume that our program contains a capability pointing to our buffer,
        we need to load the capability in R1 before our program. It corresponds
        to a closure around the code and the buffer
      - we dynamically allocate the buffer, by using the `malloc` macro.
        It is different from the previous solution, because it allocates a new
        buffer each time our program is called

   *)
  Lemma prog_CPS_safe_to_share b_pc e_pc a_prog b_mem e_mem secret_off secret :

    (* The instructions of the code are in the memory closure of the PCC *)
    SubBounds b_pc e_pc a_prog (a_prog ^+ length (prog_code secret_off secret))% a ->
    (* The secret offset fits in the memory buffer *)
    (b_mem <= b_mem ^+ secret_off < e_mem)%a ->

    ⊢ ( code_inv a_prog secret_off secret
       ∗ start_mem_inv b_mem e_mem secret_off
       ∗ end_mem_inv b_mem e_mem secret_off
       ∗ secret_inv b_mem secret_off secret)

   -∗ interp (WCap E b_pc e_pc a_prog).
  Abort.

End base_program_CPS.
