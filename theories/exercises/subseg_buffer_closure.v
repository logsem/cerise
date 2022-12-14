From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import malloc macros.
From cap_machine Require Import fundamental logrel macros_helpers rules proofmode.
From cap_machine.examples Require Import template_adequacy.
From cap_machine.exercises Require Import register_tactics subseg_buffer.
Open Scope Z_scope.

(** Firtly, we create a closure around our code and buffer. The capability
    pointing to the allocated buffer is stored in memory. We thus have to load
    it in the register. This part of code sets up the context, allowing to use
    the previous specification.
 *)
Section closure_program.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.
  Context {nainv: logrel_na_invs Σ}.
  Definition Nclosure : namespace := nroot .@ "closure".

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

  Definition closure_code secret_off secret_val:=
    load_code ++ (prog_code secret_off secret_val).

  (** As we will prove that the encapsulation of the program
      in a sentry capability is safe-to-share, the memory
      propositions have to be in invariant. *)
  (** We define the invariants *)
  (* cap_addr points to the capability for the buffer *)
  Definition cap_memN := Nclosure.@"cap_mem".
  Definition cap_mem_inv p_mem b_mem e_mem cap_addr :=
    na_inv logrel_nais cap_memN
           (cap_addr ↦ₐ WCap p_mem b_mem e_mem b_mem).

  (* The first part of the buffer, before the secret, is always zeroes *)
  Definition start_memN := (Nclosure.@"start_mem").
  Definition start_mem_inv b_mem secret_off :=
    let secret_addr := (b_mem ^+ secret_off)%a in
    na_inv logrel_nais start_memN
           ([[b_mem, secret_addr]] ↦ₐ [[ region_addrs_zeroes b_mem secret_addr ]]).

  (* The secret is either equal to 0 -- at the initialisation -- or equal to
     42 -- after the secret was stored *)
  Definition secretN := (Nclosure.@"secret").
  Definition secret_inv (b_mem : Addr) secret_off secret_val :=
    let secret_addr := (b_mem ^+ secret_off)%a in
    na_inv logrel_nais secretN
           ((secret_addr ↦ₐ WInt 0) ∨ (secret_addr ↦ₐ WInt secret_val)).

  (* The code instruction is stored in an invariant as well *)
  Definition codeN := (Nclosure.@"code").
  Definition code_closure_inv a_prog secret_off secret_val :=
    na_inv logrel_nais codeN (codefrag a_prog (closure_code secret_off secret_val)).

  (** Specifications *)

  (* We specifie the closure program in a modular way, so we firstly specifie
     the part of the code that load the capability *)
  Lemma load_spec p_pc b_pc e_pc s_load (* pc *)
        p_mem b_mem e_mem (* mem *)
        w1 w2 w3
        EN φ :

    let e_load := (s_load ^+ length load_code)%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc s_load e_load ->

    writeAllowed p_mem = true ->

    ↑ cap_memN ⊆ EN ->

    ⊢ ( cap_mem_inv p_mem b_mem e_mem b_pc
        ∗ PC ↦ᵣ WCap p_pc b_pc e_pc s_load
        ∗ r_t1 ↦ᵣ w1
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        ∗ codefrag s_load load_code
        ∗ na_own logrel_nais EN
        ∗ ▷ ( PC ↦ᵣ WCap p_pc b_pc e_pc e_load
              ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
              ∗ (∃ w2, r_t2 ↦ᵣ w2)
              ∗ (∃ w3, r_t3 ↦ᵣ w3)
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


  (* We specifie the part of the program that store the secret, using the
     invariant. *)
  Lemma prog_closure_spec
        wadv
        p_pc b_pc e_pc a_prog (* pc *)
        p_mem b_mem e_mem (* mem *)
        w2 w3
        secret_off secret_val
        EN
        φ :
    let secret := (b_mem^+secret_off)%a in
    let len_p := (a_prog ^+ length (prog_code secret_off secret_val))%a in

    ExecPCPerm p_pc ->
    SubBounds b_pc e_pc a_prog len_p ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ↑secretN ⊆ EN ->

    ⊢ ( (* PC points to prog_code*)
        ( secret_inv b_mem secret_off secret_val
          ∗ PC ↦ᵣ WCap p_pc b_pc e_pc a_prog
          ∗ r_t1 ↦ᵣ WCap p_mem b_mem e_mem b_mem
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          ∗ r_t30 ↦ᵣ wadv

          ∗ codefrag a_prog (prog_code secret_off secret_val)
          ∗ na_own logrel_nais EN

          ∗ ▷ ( PC ↦ᵣ updatePcPerm wadv
                ∗ r_t1 ↦ᵣ WCap p_mem (b_mem^+(secret_off+1))%a e_mem secret%a
                ∗ r_t2 ↦ᵣ WInt (b_mem+(secret_off +1))
                ∗ r_t3 ↦ᵣ WInt e_mem
                ∗ r_t30 ↦ᵣ wadv
                ∗ codefrag a_prog (prog_code secret_off secret_val)
                ∗ na_own logrel_nais EN
                -∗ WP Seq (Instr Executable) {{ φ }})%I
              )

          -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros * Hpc_perm Hpc_bounds Hlen_mem Hp_mem Hnainv.
    iIntros "(#Hinv_secret & HPC& Hr1& Hr2& Hr3& Hr30& Hprog& Hna & Post)".
    subst secret len_p.
    codefrag_facts "Hprog".

    iMod (na_inv_acc logrel_nais with "Hinv_secret Hna") as
      "(>Hsecret & Hna & Hclose_secret)" ; auto. (* inclusion namespace *)

    simpl in *.
    rewrite /prog_code.
    assert (Hp_mem': ~ p_mem = E)
           by (intros -> ; simpl in Hp_mem ; discriminate).
    (* Lea r_t1 secret_off *)
    iInstr "Hprog".
    { transitivity (Some (b_mem ^+secret_off)%a) ; auto. solve_addr. }
    (* Store r_t1 42 , where r_t1 = (RWX, b, e, secret) *)
    (* Regarding the invariant, the secret can be either 0 or 42 *)
    iDestruct "Hsecret" as "[Hsecret | Hsecret]".
    all: iInstr "Hprog" ; [solve_addr|].
    (* getB getE add subseg *)
    all: iGo "Hprog"
    ; try transitivity (Some (b_mem ^+(secret_off+1))%a) ; auto
    ; try solve_addr .
    (* jmp *)
    all: iInstr "Hprog".
    (* halts in the adversary code *)
    all: iMod ("Hclose_secret" with "[Hsecret $Hna]") as "Hna"
         ; [iNext ; iRight ; iFrame |].
    all: iApply "Post".
    all: iFrame ; iFrame "#".
  Qed.

  (* Specification of the full program, stops after the jump to the adversary *)
  Lemma closure_spec
        pc_p pc_b pc_e s_closure
        p_mem b_mem e_mem
        w1 w2 w3 w_adv
        secret_off secret_val
        EN
        φ :

    let secret := (b_mem^+secret_off)%a in
    let e_closure := (s_closure ^+ length (closure_code secret_off secret_val))%a in

    ExecPCPerm pc_p ->
    SubBounds pc_b pc_e s_closure e_closure ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    ↑secretN ⊆ EN ->
    ↑codeN ⊆ EN ->
    ↑cap_memN ⊆ EN ->

    ⊢ ( secret_inv b_mem secret_off secret_val
        ∗ code_closure_inv s_closure secret_off secret_val
        ∗ cap_mem_inv p_mem b_mem e_mem pc_b
        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e s_closure
        ∗ r_t1 ↦ᵣ w1
        ∗ r_t2 ↦ᵣ w2
        ∗ r_t3 ↦ᵣ w3
        ∗ r_t30 ↦ᵣ w_adv
        ∗ na_own logrel_nais EN
        ∗ ▷ ( PC ↦ᵣ updatePcPerm w_adv
              ∗ r_t1 ↦ᵣ WCap p_mem (b_mem^+(secret_off+1))%a e_mem secret%a
              ∗ r_t2 ↦ᵣ WInt (b_mem+(secret_off +1))
              ∗ r_t3 ↦ᵣ WInt e_mem
              ∗ r_t30 ↦ᵣ w_adv
              ∗ na_own logrel_nais EN
              -∗ WP Seq (Instr Executable) {{ φ }})
        -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros secret e_closure ; subst secret e_closure.
    iIntros (Hpc_perm Hpc_bounds Hvsecret Hp_mem Hnainv_secret Hnainv_code Hnainv_cap)
            "(#Hinv_secret & #Hinv_code & #Hinv_cap & HPC & Hr1 & Hr2 & Hr3 & Hr30 & Hna & Post)".

    rewrite /code_closure_inv.
    iMod (na_inv_acc with "Hinv_code Hna")
      as "(>Hprog & Hna & Hprog_close)"
    ; auto.
    rewrite /closure_code.
    focus_block_0 "Hprog" as "Hload" "Hcont".
    iApply (load_spec with "[-]")
    ; try (iFrame ; iFrame "#")
    ; eauto
    ; try solve_ndisj.
    iNext.

    iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hload & Hna)".
    clear w2 w3.
    iDestruct "Hr2" as (w2) "Hr2"; iDestruct "Hr3" as (w3) "Hr3".
    unfocus_block "Hload" "Hcont" as "Hprog" .
    focus_block 1%nat "Hprog" as a_mid Ha_mid "Hprog" "Hcont".
    iApply (prog_closure_spec with "[-]")
    ; try (iFrame; iFrame "#")
    ; eauto
    ; try solve_ndisj.
    iNext.

    iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hr30 & Hprog &Hna)".
    unfocus_block "Hprog" "Hcont" as "Hprog" .
    iMod ("Hprog_close" with "[$Hprog $Hna]") as "Hna".
    iApply "Post" ; iFrame ; iFrame "#".
  Qed.

  (* Invariant on the shared part of the buffer *)
  Definition end_memN := (Nclosure.@"end_mem").
  Definition end_mem_inv b_mem e_mem secret_off :=
    let n_secret_addr := (b_mem ^+ (secret_off + 1))%a in
    na_inv logrel_nais end_memN
           ([∗ list] a ∈ finz.seq_between n_secret_addr e_mem,
            ∃ P, inv (logN .@ a) (interp_ref_inv a P) ∗ read_cond P interp
                                                          ∗ write_cond P interp)%I.

  (* Assuming that the word of the adversary is safe to share,
     the machine executes safely and completely. *)
  Lemma closure_full_run_spec
        pc_p pc_b pc_e s_closure
        p_mem b_mem e_mem
        secret_off secret_val
        w_adv
        rmap :

    let secret := (b_mem^+secret_off)%a in
    let e_closure := (s_closure ^+ length (closure_code secret_off secret_val))%a in

    ExecPCPerm pc_p ->
    SubBounds pc_b pc_e s_closure e_closure ->

    (b_mem <= secret < e_mem)%a ->
    writeAllowed p_mem = true ->

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC ; r_t30 ]} →

    ⊢ ( code_closure_inv s_closure secret_off secret_val
        ∗ start_mem_inv b_mem secret_off
        ∗ end_mem_inv b_mem e_mem secret_off
        ∗ secret_inv b_mem secret_off secret_val
        ∗ cap_mem_inv p_mem b_mem e_mem pc_b

        ∗ PC ↦ᵣ WCap pc_p pc_b pc_e s_closure
        ∗ r_t30 ↦ᵣ w_adv
        ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)

        ∗ na_own logrel_nais ⊤
        ∗ interp w_adv

        -∗ WP Seq (Instr Executable)
              {{ v, ⌜v = HaltedV⌝
                    → ∃ r : Reg, full_map r ∧ registers_mapsto r ∗ na_own logrel_nais ⊤ }})%I.
  Proof.
    intros secret e_closure ; subst secret e_closure.
    iIntros (Hpc_perm Hpc_bounds Hvsecret Hp_mem Hrmap_dom)
            "(#Hinv_prog & #Hinv_mem & #Hinv_mem' & #Hinv_secret & #Hinv_cap & HPC & Hr30 & Hrmap & Hna & #Hvadv)".

    (* FTLR on V(w_adv) *)
    iDestruct (jmp_to_unknown with "Hvadv") as "Cont".

    (* We open the invariant on the shared buffer,
       needed to prove that r1 is safe to share *)
    rewrite /end_mem_inv.
    iMod (na_inv_acc with "Hinv_mem' Hna")
      as "(Hmem'& Hna& Hnainv_close)" ; auto.

    (* Extract the register r_t1 - r_t3 *)
    extract_register r_t1 with "Hrmap" as (w1 Hw1) "[[Hr1 _] Hrmap]".
    extract_register r_t2 with "Hrmap" as (w2 Hw2) "[[Hr2 _] Hrmap]".
    extract_register r_t3 with "Hrmap" as (w3 Hw3) "[[Hr3 _] Hrmap]".

    (* Apply the spec *)
    iApply (closure_spec with "[-]")
    ; try iFrame "HPC Hr1 Hr2 Hr3 Hr30 Hna"
    ; try iFrame "#"
    ; eauto
    ; try solve_ndisj.
    iNext.
    iIntros "(HPC & Hr1 & Hr2 & Hr3 & Hr30 & Hna)".

    (* We also need to prove that Hr1 is safe to share *)
    iAssert (interp (WCap p_mem (b_mem ^+(secret_off+1))%a e_mem (b_mem ^+ secret_off)%a))
      with "[Hmem']"
      as "#Hinterp_r1" .
    { unfold interp.
      destruct p_mem ; try discriminate.
      all: simpl.
      all: rewrite (fixpoint_interp1_eq
                      (WCap _ (b_mem ^+ (secret_off+1))%a e_mem (b_mem ^+ secret_off)%a)) .
      all: simpl.
      all: iFrame.
    }

    rewrite /interp.

    (* Re-insert the registers *)
    insert_register r_t3 with "[$Hrmap Hr3]" as "Hrmap".
    insert_register r_t2 with "[$Hrmap Hr2]" as "Hrmap".
    insert_register r_t30 with "[$Hrmap Hr30]" as "Hrmap".
    insert_register r_t1 with "[$Hrmap Hr1]" as "Hrmap".

    (* Close the invariant *)
    iMod ("Hnainv_close" with "[$Hna]") as "Hna".
    { iNext.
      rewrite /interp /=.
      destruct p_mem eqn:Heq; try discriminate.
      all: rewrite (fixpoint_interp1_eq (WCap _ _ e_mem _)) .
      all: simpl.
      all: iFrame "#".
    }

    (* Apply the continuation *)
    iApply "Cont" ; [|iFrame].
    iPureIntro.
    rewrite !dom_insert_L Hrmap_dom.
    rewrite !singleton_union_difference_L. set_solver+.
  Qed.

  (* The encapsulation of the program in a sentry-capability is safe to share *)
  Lemma closure_prog_safe_to_share
        b_pc e_pc a_prog
        p_mem b_mem e_mem
        secret_off secret_val :

    SubBounds b_pc e_pc a_prog (a_prog ^+ length (closure_code secret_off secret_val))%a ->
    (b_mem <= b_mem ^+ secret_off < e_mem)%a ->
    writeAllowed p_mem = true ->

    ⊢ (code_closure_inv a_prog secret_off secret_val
       ∗ start_mem_inv b_mem secret_off
       ∗ end_mem_inv b_mem e_mem secret_off
       ∗ secret_inv b_mem secret_off secret_val
       ∗ cap_mem_inv p_mem b_mem e_mem b_pc
      )

   -∗ interp (WCap E b_pc e_pc a_prog).
 Proof.
   iIntros (Hbounds Hb_mem Hp_mem)
     "(#Hnainv_code & #Hnainv_mem & #Hinv_mem' & #Hinv_secret & #Hinv_cap)".
   (* 1 - unfold the definitions *)
   rewrite !fixpoint_interp1_eq /=.
   iIntros (regs).
   iNext; iModIntro.
   iIntros "(Hrsafe& Hregs& Hna)".
   iDestruct "Hrsafe" as "[%Hrfull #Hrsafe]".
   rewrite /interp_conf.
   rewrite {1}/registers_mapsto.

   (* 2 - prepare the registers for closure_full_run_spec *)
   extract_register PC with "Hregs" as "[HPC Hregs]".
   extract_register r_t30 with "Hregs" as (w30 Hw30) "[Hr30 Hregs]".
   iAssert (interp w30) as "Hw30".
   { iApply ("Hrsafe" $! r_t30 w30) ; eauto.  }
   set (rmap:= delete r_t30 (delete PC regs)).

   (* 3 - use the full specification to show that the program executes safely and completely *)
   iApply (closure_full_run_spec
             RX b_pc e_pc a_prog
             p_mem b_mem e_mem
             secret_off secret_val
             w30
             rmap
            with "[-]")
   ; eauto
   ; try apply ExecPCPerm_RX
   ; try (iFrame ; iFrame "#").
   - subst rmap.
     rewrite !dom_delete_L.
     rewrite difference_difference_L.
     apply regmap_full_dom in Hrfull; rewrite Hrfull.
     set_solver.
   - subst rmap.
     iDestruct (big_sepM_sep _ (λ k v, interp v)%I with "[Hregs]") as "Hregs".
     { iSplitL. by iApply "Hregs". iApply big_sepM_intuitionistically_forall. iModIntro.
       iIntros (r' ? HH). repeat eapply lookup_delete_Some in HH as [? HH].
       iApply ("Hrsafe" $! r'); auto. }
     simpl.
     iFrame.
 Qed.

 (** Adequecy theorem - the template of the adequacy theorem defined in Cerise
    requires the memory invariant being in the memory of the program.
    However, the memory buffer is not inside the memory closure of the program.
    Therefore, we cannot apply the adequacy theorem on this instance. *)

 (** Remarks : We could apply the adequacy theorem on this instance,
               but not using the template defined in Cerise. We could
               use the adequacy theorem of Cerise, but it is out-of-scope
               here *)
End closure_program.
