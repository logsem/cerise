From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone.
From cap_machine Require Import solve_pure proofmode map_simpl register_tactics.
Import uPred. (* exist_persistent *)

(* Architectural variant of the sealing/unsealing functionality in the dynamic_sealing file. *)
Section sealing.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {seals:sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters} .

  (* Resources used as local state in the sealing and unsealing code. Concretely, we need one specific sealing capability with a proof that the predicate used is the right one. Named seal_state for consistency with architectural case. *)
  (* Note that the otype o replaces the function of the gname γ from OCPL *)
  (* Note2: leave seal_pred outside of invariant, because it is persistent and does not depend on o_e *)
  Definition seal_state ι ll o (Φ : Word -> iProp Σ) {Hpers : ∀ w, Persistent (Φ w)} : iProp Σ
    := na_inv logrel_nais ι (∃ o_e, ll ↦ₐ WSealRange (true,true) o o_e o
                             ∗ ⌜ (o < o_e)%ot ⌝)%I ∗ seal_pred o Φ.

  (* Note: this is just the unfolded version of `interp_sb`, but with an outwardly visible predicate Φ, i.e. it is not existentially quantified. *)
  Definition valid_sealed w o (Φ : Word -> iProp Σ) := (∃ sb, ⌜w = WSealed o sb⌝ ∗  ⌜∀ w : leibnizO Word, Persistent (Φ w)⌝ ∗ seal_pred o Φ ∗ Φ (WSealable sb))%I.

  (* Having the Persistent above allows us to prove the following instance: *)
  Global Instance valid_sealed_persistent w o Φ: Persistent (valid_sealed w o Φ).
  Proof.
    apply exist_persistent; intros sb.
    unfold Persistent. iIntros "(%Hw & %Hpers & #Hs & HP)".
    (* use knowledge about persistence *)
    iAssert (<pers> Φ (WSealable sb))%I with "[ HP ]" as "HP".
    { by iApply Hpers.  }
    repeat (iApply persistently_sep_2; iSplitR); auto.
  Qed.

  (* Knowing something is sealed is enough for it to validly satisfy a predicate phi. *)
  Lemma interp_valid_sealed sb o:
    interp (WSealed o sb) -∗ ∃ Φ, ▷ valid_sealed (WSealed o sb) o Φ.
  Proof.
    iIntros "Hsl /=". rewrite fixpoint_interp1_eq /= /valid_sealed.
    iDestruct "Hsl" as (P) "(%Hpers & Hpred & HP)".
    iExists P, sb; repeat iSplit; [auto | auto | iFrame.. ].
  Qed.

  (* Knowing something is validly sealed is enough for it to be valid *)
  Lemma valid_sealed_interp sb o Φ:
    valid_sealed (WSealed o sb) o Φ -∗ interp (WSealed o sb).
  Proof.
    iIntros "Hvs". iDestruct "Hvs" as (x) "(%Heq & %Hpers' & #Hsp & HΦ')".
    inversion Heq; subst x.
    rewrite fixpoint_interp1_eq /=.
    iExists _; iFrame "% ∗ #".
  Qed.

  Lemma sealLL_valid_sealed_pred_eq ι ll o w Φ Φ' {Hpers : ∀ w, Persistent (Φ w)}: seal_state ι ll o Φ -∗ valid_sealed w o Φ' -∗  (∀ x, ▷ (Φ x ≡ Φ' x)).
  Proof.
    iIntros "HsealLL Hvs".
    iDestruct "HsealLL" as "[_ Hsp]".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

  Lemma sealLL_pred_interp ι ll o w Φ {Hpers : ∀ w, Persistent (Φ w)}: seal_state ι ll o Φ -∗ Φ (WSealable w) -∗ interp (WSealed o w).
  Proof. iIntros "Hss HΦ".
         iDestruct "Hss" as "[ Hss #Hpred ]".
         iAssert (valid_sealed (WSealed o w) o Φ) with "[HΦ]" as "Hvals".
         { iExists _. iFrame "∗ #". auto. }
         by iApply valid_sealed_interp.
  Qed.

  (* USE the sealing capability in the environment to unseal the argument. Fails if the otypes do not match, or if the argument is not sealed.
     Result is returned in r_t1; clear r_env for security and return. *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env  *)
  Definition unseal_instrs :=
    encodeInstrsW [ Load r_env r_env
                  ; UnSeal r_t1 r_env r_t1
                  ; Mov r_env (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition unseal_instrs_length := Eval cbn in length (unseal_instrs).

  (* Assume r_t1 contains the word to seal.
     Seal it using the sealing capability in r_env.
     clear r_env and return *)
  (* Arguments: r_t1
     Return point: r_t0
     Uses: r_env *)
  Definition seal_instrs :=
    encodeInstrsW [ Load r_env r_env
                  ; Seal r_t1 r_env r_t1
                  ; Mov r_env (inl 0%Z) (* Clearing *)
                  ; Jmp r_t0
                  ].

  Definition seal_instrs_length := Eval cbn in length seal_instrs.

  (* Create two closures for sealing and unsealing assuming that their code is preceding this one.
     Specifically, we assume the memory layout is [unseal_instrs][seal_instrs][make_seal_preamble] *)
  (* This works by:
     1. Malloc a location to store the sealing capability in, thus obtaining some capability c. Store an appropriate sealing capability in this location, using salloc.
     2. Create a closure with access to c, and containing the code unseal_instr.
     3. Create a closure with access to c, and containing the code seal_instr.
     4. Return closure for unsealing in r_t1 and sealing in r_t2. *)
  (* Arguments: None
     Return point: rt_0
     Uses: r_t1 r_t2 r_t8 r_t9 r_t10 *)
  Definition make_seal_preamble_instrs f_m f_m' :=
    encodeInstrsW [ Mov r_t8 PC (* Copy PC into r_t8 *)
                  ; Lea r_t8 (- (Z.of_nat seal_instrs_length))%Z (* Capability pointing to code for seal_instrs *)
                  ]
    ++ malloc_instrs f_m 1 (* Malloc a cell for sealing capability *)
    ++ encodeInstrsW [ Mov r_t9 r_t1 ] (* Keep a copy of the capability to the cell *)
    ++ salloc_instrs f_m' 1 (* Generate a fresh seal *)
    ++ encodeInstrsW [ Store r_t9 r_t1 (* Store the fresh seal in the cell *)
                  ; Mov r_t2 r_t9 (* Prepare for creating closure, r_t2 must contain environment *)
                  ; Mov r_t1 r_t8 (* Prepare for creating closure, r_t1 must contain code *)
                  ]
    ++ crtcls_instrs f_m ++ (* Create the closure for seal, result in r_t1 *)
    encodeInstrsW [ Mov r_t10 r_t1 (* Closure for seal now in r_t10 *)
                  ; Lea r_t8 (inl (- (Z.of_nat unseal_instrs_length))%Z) (* Capability pointing to code for seal_instrs *)
                  ; Mov r_t1 r_t8 (* Prepare for creating closure for unseal, code *)
                  ; Mov r_t2 r_t9 (* Prepare for creating closure for unseal, environment *)
                  ]
    ++ crtcls_instrs f_m ++ (* Create the closure for unseal, result in r_t1 *)
    encodeInstrsW [ Mov r_t2 r_t10 (* Closure for seal now in r_t2 *)
                  ; Mov r_t8 (inl 0%Z) (* Clearing registers *)
                  ; Mov r_t9 (inl 0%Z)
                  ; Mov r_t10 (inl 0%Z)
                  ; Jmp r_t0 (* Return *)
                  ].

  Definition make_seal_preamble f_m f_m' ai :=
    ([∗ list] a_i;w_i ∈ ai;(make_seal_preamble_instrs f_m f_m'), a_i ↦ₐ w_i)%I.

  (* TODO: move this to the rules_Get.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)

  Definition is_sealed_with_o w o :=
    match w with
    | WSealed o' sb => (o =? o')%ot
    | _ => false end.


  Lemma wp_Get_fail_same E get_i dst pc_p pc_b pc_e pc_a w zsrc :
    decodeInstrW w = get_i →
    is_Get get_i dst dst →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ dst ↦ᵣ WInt zsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

 (* TODO: move this to unseal rules file *)
 Lemma wp_unseal_nomatch_r2 E pc_p pc_b pc_e pc_a w r1 r2 p b e a wsealed pc_a' :
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealed_with_o wsealed a = false →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange p b e a
        ∗ ▷ r2 ↦ᵣ wsealed }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hfalse ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; last by iApply "Hφ".
    { destruct wsealed as [| | o' sb']; try by simplify_map_eq.
      exfalso.
      rewrite /is_sealed_with_o //= in Hfalse.
      destruct (decide (o' = a)) as [->| Hne]; [solve_addr | simplify_map_eq]. }
  Qed.

  Local Existing Instance interp_weakening.if_persistent.

  Lemma unseal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        wsealed o (* input cap *)
        ll ll' (* sealing cap bounds *)
        a_first (* special adresses *)
        ι φ Ep (* invariant/gname names *)
        Φ Φ' {Hpers : ∀ w, Persistent (Φ w)} (* this predicate is chosen by the client at creation *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length unseal_instrs)%a →

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ Ep →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX ll ll' ll
      ∗ r_t1 ↦ᵣ wsealed
      (* invariant for d *)
      ∗ seal_state ι ll o Φ
      (* proof that the provided value has been validly sealed *)
      ∗ ▷ (if is_sealed_with_o wsealed o then valid_sealed wsealed o Φ' else True)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais Ep
      (* trusted code *)
      ∗ codefrag a_first unseal_instrs
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_env ↦ᵣ WInt 0%Z
          ∗ (∃ sb, ⌜wsealed = WSealed o sb⌝ ∗ r_t1 ↦ᵣ WSealable sb ∗ Φ (WSealable sb))
          ∗ codefrag a_first unseal_instrs
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hd Hnclose) "(HPC & Hr_t0 & Hr_env & Hr_t1 & #[Hseal_inv #HsealP] & #Hseal_valid & Hown & Hprog & Hφfailed & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.

    iMod (na_inv_acc with "Hseal_inv Hown") as "(HisList & Hown & Hcls')";auto.
    iDestruct "HisList" as (o_e) "[>Hll >%Hlt]".

    codefrag_facts "Hprog".
    iInstr "Hprog". { solve_pure_addr. }

    destruct (is_sealed_with_o wsealed o) eqn:HisSl; cycle -1.
    { (* Handle failure cases manually *)
      wp_instr.
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iApply (wp_unseal_nomatch_r2 with "[$HPC $Hr_t1 $Hr_env $Hi]"); try solve_pure.
      iIntros "!> _".
      cbn. iApply wp_pure_step_later; auto. iNext.
      iApply wp_value. auto. }
    destruct wsealed as [| | o' sb]; try by exfalso.
    (* If o ≠ o', we also have failure *)
    destruct (decide (o = o')) as [-> | Hne]; cycle -1.
    { rewrite /= in HisSl. destruct o, o'; solve_addr. }

    unshelve iDestruct (sealLL_valid_sealed_pred_eq with "[$Hseal_inv $HsealP] Hseal_valid") as "Heqv"; [auto | ].

    iInstr "Hprog". { auto. } {solve_pure_addr. }
    iGo "Hprog".

    iMod ("Hcls'" with "[Hll $Hown]") as "Hown".
    { iNext. iExists _; iFrame "∗ % #". }

    iAssert (Φ (WSealable sb)) as "Hsb".
    { iDestruct "Hseal_valid" as (x) "(%Heq & %Hpers' & _ & HΦ')".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (WSealable x)).
      by iRewrite "Heqv". }
    iApply "Hφ". iFrame "∗".
    iExists _. iFrame "∗ #".
    eauto.
  Qed.

 (* TODO: move this to unseal rules file *)
 Lemma wp_seal_nosb_r2 E pc_p pc_b pc_e pc_a w r1 r2 p b e a w2 pc_a' :
    decodeInstrW w = Seal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealb w2 = false →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange p b e a
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hfalse ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; last by iApply "Hφ".
    { by simplify_map_eq. }
  Qed.

  Lemma seal_spec
        pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w o (* input z *)
        ll ll' (* sealing cap bounds *)
        a_first (* special adresses *)
        ι Ep φ (* invariant/gname names *)
        Φ {Hpers : ∀ w, Persistent (Φ w)} (* the client chosen predicate is persistent *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length seal_instrs)%a →

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ Ep →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_env ↦ᵣ WCap RWX ll ll' ll
       ∗ r_t1 ↦ᵣ w
       ∗ Φ w
       ∗ r_t0 ↦ᵣ wret
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first seal_instrs
       (* linked list invariants *)
       ∗ seal_state ι ll o Φ
       ∗ ▷ φ FailedV
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ WInt 0%Z
          ∗ r_t0 ↦ᵣ wret
          ∗ (∃ sb, ⌜ w = WSealable sb⌝ ∗ r_t1 ↦ᵣ WSealed o sb ∗ valid_sealed (WSealed o sb) o Φ)
          ∗ codefrag a_first seal_instrs
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hhd Hnclose) "(HPC & Hr_env & Hr_t1 & HΦw & Hr_t0 & Hown & Hprog & #[Hseal_inv #HsealP] & Hφfailed & Hφ)".

    iMod (na_inv_acc with "Hseal_inv Hown") as "(HisList & Hown & Hcls')";auto.
    iDestruct "HisList" as (o_e) "[>Hll >%Hlt]".

    codefrag_facts "Hprog".
    iInstr "Hprog". { solve_pure_addr. }

    destruct (is_sealb w) eqn:HisSb; cycle -1.
    { (* Handle failure cases manually *)
      wp_instr.
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iApply (wp_seal_nosb_r2 with "[$HPC $Hr_t1 $Hr_env $Hi]"); try solve_pure.
      iIntros "!> _".
      cbn. iApply wp_pure_step_later; auto. iNext.
      iApply wp_value. auto. }
    destruct w as [| sb |]; try by exfalso.

    iInstr "Hprog". {solve_pure_addr. }
    iGo "Hprog".

    iMod ("Hcls'" with "[Hll $Hown]") as "Hown".
    { iNext. iExists _; iFrame "∗ % #". }

    iApply "Hφ". iFrame "∗".
    iExists _. iFrame. iSplitR; first auto.
    iExists _; iFrame "∗ #".
    iSplit; auto.
  Qed.

  Lemma sealLL_alloc ι Φ ll o o_e Ep {Hpers : ∀ w, Persistent (Φ w)} :
    (o < o_e)%ot → ll ↦ₐ WSealRange (true,true) o o_e o -∗ can_alloc_pred o -∗
    |={Ep}=> seal_state ι ll o Φ.
  Proof.
    iIntros (Hooe) "Hll Hsp".
    iMod (seal_store_update_alloc with "Hsp") as "#Hsp".
    iMod (na_inv_alloc logrel_nais _ ι _ with "[Hll Hsp]")%I as "Hinv"; last by iFrame "∗ #".
    iExists _; iFrame "∗ %".
  Qed.

  Lemma make_seal_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        a_first (* special adresses *)
        rmap (* register map *)
        f_m f_m' b_m e_m b_s e_s (* m/salloc addrs *)
        b_r e_r a_r a_r' a_r'' (* environment table addrs *)
        ι ι1 ι2 Ep φ (* invariant/gname names *)
        Φ {Hpers: ∀ w, Persistent (Φ w)} (* The spec for make seal works for any seal predicate Φ
             that the client must choose upon creation *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ (length (unseal_instrs) + length (seal_instrs) + length (make_seal_preamble_instrs f_m f_m')))%a →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0]} →

    (* environment table: malloc and salloc in bounds *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →
    withinBounds b_r e_r a_r'' = true →
    (a_r + f_m')%a = Some a_r'' →

    (* managing invariants *)
    up_close (B:=coPset) ι1 ⊆ Ep →
    up_close (B:=coPset) ι2 ⊆ Ep →
    (up_close (B:=coPset) ι2 ## ↑ι1) →

    PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ (length (unseal_instrs) + length (seal_instrs)))%a
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first (unseal_instrs ++ seal_instrs ++ make_seal_preamble_instrs f_m f_m')
       (* malloc *)
       ∗ na_inv logrel_nais ι1 (malloc_inv b_m e_m)
       (* salloc *)
       ∗ na_inv logrel_nais ι2 (salloc_inv b_s e_s)
       ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
       ∗ a_r' ↦ₐ WCap E b_m e_m b_m
       ∗ a_r'' ↦ₐ WCap E b_s e_s b_s
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
          ∗ a_r' ↦ₐ WCap E b_m e_m b_m
          ∗ a_r'' ↦ₐ WCap E b_s e_s b_s
          ∗ (∃ b1 e1 b2 e2 ll ll', let wvar := WCap RWX ll ll' ll in
                                   let wcode1 := WCap pc_p pc_b pc_e a_first in
                                   let wcode2 := WCap pc_p pc_b pc_e (a_first ^+ length (unseal_instrs))%a in
                                   r_t1 ↦ᵣ WCap E b1 e1 b1 ∗ r_t2 ↦ᵣ WCap E b2 e2 b2
                                   ∗ ⌜(b1 + 8)%a = Some e1⌝ ∗ ⌜(b2 + 8)%a = Some e2⌝
                                   ∗ [[b1,e1]]↦ₐ[[activation_instrs wcode1 wvar]]
                                   ∗ [[b2,e2]]↦ₐ[[activation_instrs wcode2 wvar]]
                                   (* linked list invariants *)
                                   ∗ ⌜(ll + 1)%a = Some ll'⌝
                                   ∗ ∃ o, seal_state ι ll o Φ)
          ∗ ([∗ map] r↦w ∈ (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]> (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> (<[r_t7:=WInt 0%Z]> (<[r_t8:=WInt 0%Z]> (<[r_t9:=WInt 0%Z]> (<[r_t10:=WInt 0%Z]> (delete r_t1 (delete r_t2 rmap)))))))))), r ↦ᵣ w)
          ∗ codefrag a_first (unseal_instrs ++ seal_instrs ++ make_seal_preamble_instrs f_m f_m')
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hdom Hbounds_m Hf_m Hbounds_r Hf_r Hnclose' Hnclose'' Hndisj) "(HPC & Hr_t0 & Hregs & Hown & Hprog & #Hmalloc & #Hsalloc & Hpc_b & Ha_r' & Ha_r'' & Hφ)".

    focus_block 2 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iExtract "Hregs" r_t8 as "Hr_t8".
    iGo "Hprog".
    { rewrite /seal_instrs_length. instantiate (1 := (a_first ^+ length (unseal_instrs))%a).
      solve_addr. }
    iInsert "Hregs" r_t8. clear vr_t8.
    unfocus_block "Hprog" "Hcont" as "Hprog".

    rewrite /make_seal_preamble_instrs.

    focus_block 3 "Hprog" as a_middle1 Ha_middle1 "Hprog" "Hcont".
    iApply malloc_spec_alt; iFrameAutoSolve. 4: iFrame "# ∗".
    solve_map_dom. auto. lia.
    iSplitL "". iNext. auto.
    iSplitL "". iNext. iRight. auto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hll & Hr_t0 & Hown & Hregs)".
    iDestruct "Hll" as (lla lla') "(%Heqb & Hr_t1 & Hll)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    (* Allocated one address *)
    iAssert (lla ↦ₐ _)%I with "[Hll]" as "Hll".
    { rewrite /region_mapsto. rewrite finz_seq_between_singleton; auto.
      rewrite /region_addrs_zeroes. rewrite (proj2 (proj1 (finz_incr_iff_dist lla lla' 1) ltac:(auto))). simpl replicate. iDestruct "Hll" as "[$ _]". }

    focus_block 4 "Hprog" as a_middle1' Ha_middle1' "Hprog" "Hcont".
    iExtract "Hregs" r_t9 as "Hr_t9".
    iInstr "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iInsertList "Hregs" [r_t9;r_t1]. clear vr_t9.

    focus_block 5 "Hprog" as a_middle1'' Ha_middle1'' "Hprog" "Hcont".
    iApply salloc_spec_alt; iFrameAutoSolve. 4: iFrame "# ∗".
    solve_map_dom. auto. lia.
    iSplitL "". iNext. auto.
    iSplitL "". iNext. iRight. auto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r'' & Hll' & Hr_t0 & Hown & Hregs)".
    iDestruct "Hll'" as (lls lls') "(%Heqb' & Hr_t1 & Hll')".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    (* Allocated one sealpred *)
    iAssert (can_alloc_pred lls)%I with "[Hll']" as "Hll'".
    { rewrite /region_mapsto. rewrite finz_seq_between_singleton; auto.
      iDestruct "Hll'" as "[$ _]". }

    focus_block 6 "Hprog" as a_middle2 Ha_middle2 "Hprog" "Hcont".
    iExtractList "Hregs" [r_t8;r_t2;r_t9] as ["Hr_t8";"Hr_t2";"Hr_t9"].
    iInstr "Hprog". { clear -Heqb; solve_pure_addr . }
    iGo "Hprog".
    iInsertList "Hregs" [r_t8;r_t9].
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 7 "Hprog" as a_middle3 Ha_middle3 "Hprog" "Hcont".
    iApply crtcls_spec_alt; iFrameAutoSolve. 3: iFrame "# ∗".
    solve_map_dom. auto.
    iSplitL ""; eauto. iSplitL ""; eauto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hseal)".
    iDestruct "Hseal" as (b1 e1) "(Hb1eq & Hr_t1 & Hseal & Hr_t0 & Hr_t2 & Hown & Hregs)".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 8 "Hprog" as a_middle4 Ha_middle4 "Hprog" "Hcont".
    iExtractList "Hregs" [r_t8;r_t10;r_t9] as ["Hr_t8";"Hr_t10";"Hr_t9"].
    iGo "Hprog". instantiate (1 := a_first). rewrite /unseal_instrs_length. solve_addr.
    iGo "Hprog".
    iInsertList "Hregs" [r_t8;r_t9;r_t10]. clear vr_t10.
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 9 "Hprog" as a_middle5 Ha_middle5 "Hprog" "Hcont".
    iApply crtcls_spec; iFrameAutoSolve. 3: iFrame "# ∗".
    solve_map_dom. auto.
    iNext. iIntros "(HPC & Hprog & Hpc_b & Ha_r' & Hunseal)".
    iDestruct "Hunseal" as (b2 e2) "(Hb2eq & Hr_t1 & Hunseal & Hr_t0 & Hr_t2 & Hown & Hregs)".
    iExtractList "Hregs" [r_t8;r_t10;r_t9] as ["Hr_t8";"Hr_t10";"Hr_t9"].
    unfocus_block "Hprog" "Hcont" as "Hprog".

    clear dependent a_middle1 a_middle1' a_middle1'' a_middle2. (* TODO: investigate stack overflow bug *)
    focus_block 10 "Hprog" as a_middle6 Ha_middle6 "Hprog" "Hcont".
    iGo "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    iMod (sealLL_alloc ι Φ with "Hll Hll'") as "Healing". { clear -Heqb'; solve_addr. }
    iInsertList "Hregs" [r_t8;r_t9;r_t10].
    iApply "Hφ"; iFrame "∗ #".
    iSplitR "Hregs".
    { iExists b2, e2, b1, e1, lla, lla'. iFrame "% ∗".
 iExists _. iFrame. }
    { rewrite delete_commute //.
      rewrite !(insert_commute _ r_t3) // !(insert_commute _ r_t4) // !(insert_commute _ r_t5) // !(insert_commute _ r_t6) // !(insert_commute _ r_t7) // !(insert_commute _ r_t8) // !(insert_commute _ r_t9) // !(insert_commute _ r_t10) //. }
Qed.

End sealing.
