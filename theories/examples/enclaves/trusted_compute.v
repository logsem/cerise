From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import macros_new.
Open Scope Z_scope.

(* TODO move in finz *)
Lemma finz_incr_minus_id
  {finz_bound : Z}
  (f : finz finz_bound) (z : Z)
  (finz_lt : (z <? finz_bound)%Z = true)
  (finz_nonneg : (0 <=? z)%Z = true) :
  (f + (z - f))%f = Some (finz.FinZ z finz_lt finz_nonneg).
Proof.
  induction z; cbn in *; try done.
  - replace (0 - f) with (-f); solve_finz.
  - destruct (Z.pos p - f) eqn:H.
    + assert ( Z.pos p = f ) by lia.
      solve_finz.
    + assert ( Z.pos p = f + Z.pos p0) by lia.
      solve_finz.
    + assert ( Z.pos p = f + Z.neg p0) by lia.
      solve_finz.
Qed.

(* TODO move logical_mapsto? *)
Definition sealable_to_lsealable (sb : Sealable) (v : Version) :=
  match sb with
  | SCap p b e a => LSCap p b e a v
  | SSealRange p b e a => LSSealRange p b e a
  end.

Definition word_to_lword (w : Word) (v : Version) :=
  match w with
  | WInt z => LInt z
  | WSealable sb => LWSealable (sealable_to_lsealable sb v)
  | WSealed ot sb => LWSealed ot (sealable_to_lsealable sb v)
  end.

(* TODO move in common file for sealing *)
(* This section redefines useful definitions from `arch_sealing` along with further explanations. *)
Section invariants.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Definition valid_sealed w o (Φ : LWord -> iProp Σ) :=
    (∃ sb, ⌜w = LWSealed o sb⌝ ∗  ⌜∀ w : leibnizO LWord, Persistent (Φ w)⌝
                                                         ∗ seal_pred o Φ ∗ Φ (LWSealable sb))%I.
  Lemma interp_valid_sealed sb o:
    interp (LWSealed o sb) -∗ ∃ Φ, ▷ valid_sealed (LWSealed o sb) o Φ.
  Proof.
    iIntros "Hsl /=". rewrite fixpoint_interp1_eq /= /valid_sealed.
    iDestruct "Hsl" as (P) "(%Hpers & Hpred & HP)".
    iExists P, sb; repeat iSplit; [auto | auto | iFrame.. ].
  Qed.

  Lemma seal_pred_valid_sealed_eq τ w Φ Φ' {Hpers : ∀ w, Persistent (Φ w)} :
    seal_pred τ Φ -∗ valid_sealed w τ Φ' -∗ (∀ w, ▷ (Φ w ≡ Φ' w)).
  Proof.
    iIntros "Hsp Hvs".
    iDestruct "Hvs" as (sb) "(_ & _ & Hsp' & _)".
    iApply (seal_pred_agree with "Hsp Hsp'").
  Qed.

End invariants.

Section sealed_42.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.


  Definition seal_capN : namespace := nroot .@ "seal_cap".

  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Definition sealed_42 : LWord → iProp Σ :=
    λ w, (∃ b e v, ⌜w = LCap O b e f42 v⌝)%I.
  Definition sealed_42_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_42 w%I.

  Instance sealed_42_persistent w : Persistent (sealed_42 w).
  Proof. apply _. Qed.

  Definition seal_pred_42 τ := seal_pred τ sealed_42.
  Definition valid_sealed_cap w τ := valid_sealed w τ sealed_42.
  Lemma sealed_42_interp lw : sealed_42 lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed". iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.
End sealed_42.


Section trusted_compute_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ} `{MP: MachineParameters}.

  (* Data part, following the directly the main code *)
  Definition trusted_compute_data (linking_table_cap : LWord) : list LWord :=
    [ linking_table_cap ].

  (* Expect:
     - PC := (RWX, main, main_end, main)
     - R0 := (RWX, adv, adv_end, adv) *)
  Definition trusted_compute_main_code_init0 (main callback data : Z) : list LWord :=
    (* main: *)
    encodeInstrsLW [
        Mov r_t1 PC;      (* rt1 := (RWX, main, main_end, main) *)
        Mov r_t2 r_t1;    (* rt2 := (RWX, main, main_end, main) *)

        (* Create callback sentry *)
        Lea r_t1 (callback - main)%Z;       (* rt1 := (RWX, main, main_end, callback) *)
        Restrict r_t1 (encodePerm E);       (* rt1 := (E, main, main_end, callback) *)

        (* Jump to adversary *)
        Mov r_t2 0;
        Jmp r_t0
      ].

  (* Expect PC := (RWX, main, main_end, callback) *)
  Definition trusted_compute_main_code_callback0
    (callback fails : Z)
    (hash_enclave : Z)
    (assert_lt_offset : Z)
    : list LWord :=
      (* callback: *)
      encodeInstrsLW [
        (* until the end, r3 contains the capability that bails out if something is wrong *)
        Mov r_t3 PC ;                 (* r_t3 :=  (RX, main, main_end, callback) *)
        Mov r_t4 r_t3 ;               (* r_t4 :=  (RX, main, main_end, callback) *)
        Lea r_t3 (fails-callback)%Z;  (* r_t3 :=  (RX, main, main_end, fails) *)

        (* sanity check: w_res is a sealed capability *)
        GetOType r_t2 r_t0;
        Sub r_t2 r_t2 (-1)%Z;
        Mov r_t5 PC ;
        Lea r_t5 4 ;
        Jnz r_t5 r_t2;
        Jmp r_t3;

        (*  attestation *)
        GetOType r_t2 r_t0;
        EStoreId r_t4 r_t2;
        (* check otype(w_res) against identity of the enclave *)
        Sub r_t4 r_t4 hash_enclave;
        Jnz r_t3 r_t4;

        (* get returned value and assert it to be 42 *)
        UnSeal r_t1 r_t1 r_t0;
        Mov r_t0 r_t5;
        GetA r_t4 r_t1;
        Mov r_t5 42%Z;
        Mov r_t1 r_t3%Z;
        Lea r_t1 1;
        Load r_t1 r_t1
      ]
      ++ assert_reg_instrs assert_lt_offset r_t1
      ++ encodeInstrsLW [Mov r_t0 0 ; Mov r_t3 0 ; Halt]
      ++ (* fails: *) encodeInstrsLW [Fail].

  Definition trusted_compute_main_init_len : Z :=
    Eval cbv in (length (trusted_compute_main_code_init0 0%Z 0%Z 0%Z)).

  Definition trusted_compute_main_callback_len : Z :=
    Eval cbv in (length (trusted_compute_main_code_callback0 0%Z 0%Z 0%Z 0%Z)).

  Definition trusted_compute_main_data_len : Z :=
    Eval cbv in (length (trusted_compute_data (LInt 0%Z))).

  Definition trusted_compute_enclave_code : list LWord :=
    encodeInstrsLW [
      (* get signing sealing key *)
      Mov r_t1 PC;
      Lea r_t1 (-1)%Z;
      Load r_t1 r_t1;
      GetB r_t2 r_t1;
      GetA r_t3 r_t1;
      Sub r_t2 r_t2 r_t3;
      Lea r_t1 r_t2;
      Load r_t1 r_t1;
      GetE r_t3 r_t1;
      Sub r_t2 r_t3 1;
      Subseg r_t1 r_t2 r_t3;

      (* store the result (42) in a O-permission capability and sign it *)
      Mov r_t2 PC;
      GetA r_t3 r_t2;
      Sub r_t3 42 r_t3;
      Lea r_t2 r_t3;
      Restrict r_t2 (encodePerm O);
      Lea r_t1 1;
      Seal r_t2 r_t1 r_t2;

      (* share the signed value and the unsealing key to the adversary *)
      Restrict r_t1 (encodeSealPerms (false, true)); (* restrict r1 U *)
      Jmp r_t0
    ].

  Definition trusted_compute_enclave (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::trusted_compute_enclave_code.

  Axiom hash_trusted_compute_enclave : Z.

  Definition trusted_compute_main_code (assert_lt_offset : Z) : list LWord :=
    let init     := 0%Z in
    let callback := trusted_compute_main_init_len in
    let data     := trusted_compute_main_init_len + trusted_compute_main_callback_len in
    let fails    := (data - 1)%Z in
    (trusted_compute_main_code_init0 init callback data) ++
    (trusted_compute_main_code_callback0 callback fails hash_trusted_compute_enclave assert_lt_offset).

  Definition trusted_compute_main_code_len : Z :=
    Eval cbv in trusted_compute_main_init_len + trusted_compute_main_callback_len.

  Definition trusted_compute_main_len :=
    Eval cbv in trusted_compute_main_code_len + trusted_compute_main_data_len.


  (** Specification init code *)
  Lemma trusted_compute_main_init_spec
    (b_main : Addr)
    (pc_v adv_v : Version)
    (assert_lt_offset : Z)
    (w0 w1 w2 w3 w4 wadv : LWord)
    φ :

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    ContiguousRegion b_main trusted_compute_main_len ->
    ⊢ ((
          codefrag b_main pc_v trusted_compute_main

          ∗ PC ↦ᵣ LCap RWX b_main e_main b_main pc_v
          ∗ r_t0 ↦ᵣ wadv
          ∗ r_t1 ↦ᵣ w1
          ∗ r_t2 ↦ᵣ w2
          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag b_main pc_v trusted_compute_main
                ∗ PC ↦ᵣ updatePcPermL wadv
                ∗ r_t0 ↦ᵣ wadv
                ∗ r_t1 ↦ᵣ (LCap E b_main e_main a_callback pc_v)
                ∗ r_t2 ↦ᵣ LInt 0
                  -∗ WP Seq (Instr Executable) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.

    (* We define a local version of solve_addr, which subst and unfold every computed addresses  *)
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /trusted_compute_main_len in H
                end)
      ; rewrite !/trusted_compute_main_code_len /trusted_compute_main_len
          /trusted_compute_main_init_len /trusted_compute_main_callback_len
      ; solve_addr.

    intros ???? Hregion.
    iIntros "(Hcode & HPC & Hr0 & Hr1 & Hr2 & Hφ)".
    codefrag_facts "Hcode".
    iGo "Hcode".
    rewrite decode_encode_perm_inv; by cbn.
    rewrite decode_encode_perm_inv.
    iGo "Hcode".
    iApply (wp_wand with "[-]"); last (iIntros (v) "H"; by iLeft).
    iApply "Hφ".
    iFrame.
  Qed.

  (** Specification callback code *)

  Context {nainv: logrel_na_invs Σ} .
  (* Define all the invariants *)
  Definition trusted_computeN : namespace := nroot .@ "trusted_compute".

  (* Linking table invariant *)
  Definition link_tableN := (trusted_computeN.@"link_table").
  Definition link_table_inv
    v_link
    assert_entry b_assert e_assert v_assert :=
    na_inv logrel_nais link_tableN
         ((assert_entry, v_link) ↦ₐ LCap E b_assert e_assert b_assert v_assert)%I.

  (* Assert invariant *)
  Definition assertN := (trusted_computeN.@"assert").
  Definition assert_inv b_a a_flag e_a v_assert :=
    na_inv logrel_nais assertN (assert_inv b_a a_flag e_a v_assert).

  Definition flag_assertN := (trusted_computeN.@"flag_assert").
  Definition flag_inv a_flag v_flag :=
    inv flag_assertN ((a_flag,v_flag) ↦ₐ LInt 0%Z).

  (* TODO move in common file for custom enclave *)
  Record CustomEnclave :=
    MkCustomEnclave {
        code : list LWord;
        code_region : Addr;
        Penc : LWord -> iProp Σ;
        Psign : LWord -> iProp Σ;
      }.

  Definition custom_enclaves_map : Type :=
    gmap EIdentity CustomEnclave.

  Definition custom_enclaves_map_wf (cenclaves : custom_enclaves_map) :=
    map_Forall
      (fun I ce => I = hash_concat (hash (code_region ce)) (hash (code ce)))
      cenclaves.

  Definition custom_enclaveN := (trusted_computeN.@"custom_enclave").
  Definition custom_enclave_inv (cenclaves : custom_enclaves_map) :=
    inv custom_enclaveN
      (
        ⌜ custom_enclaves_map_wf cenclaves ⌝ -∗
        □ ∀ (I : EIdentity) (tid : TIndex) (ot : OType) (ce : CustomEnclave),
          enclave_all tid I
          ∗ ⌜ cenclaves !! I = Some ce ⌝
          ∗ ⌜ has_seal ot tid ⌝ -∗
          if (Z.even (finz.to_z ot))
          then (seal_pred ot (Penc ce) ∗ seal_pred (ot ^+ 1)%ot (Psign ce))
          else (seal_pred (ot ^+ (-1))%ot (Penc ce) ∗ seal_pred ot (Psign ce))
      ).

  Definition custom_enclave_contract
    (cenclaves : custom_enclaves_map)
    :=
    forall
    (I : EIdentity)
    (b e a : Addr) (v : Version)
    (b' e' a' : Addr) (v' : Version)
    (enclave_data : list LWord)
    (ot : OType)
    (ce : CustomEnclave),
    custom_enclaves_map_wf cenclaves ->
    cenclaves !! I = Some ce ->
    (code ce) !! 0%nat = Some (LCap RW b' e' a' v') ->
    enclave_data !! 0%nat = Some (LSealRange (true,true) ot (ot^+2)%ot ot) ->
    (ot + 2)%f = Some (ot ^+ 2)%f -> (* Well-formness: otype does not overflow *)
    (* TODO I think we can derive following from [b',e'] -> .... *)
    b' < e' -> (* Well-formness: data region contains at least one *)
    b < e -> (* Well-formness: code region contains at all the code *)
    I = hash_concat (hash b) (hash (tail (code ce))) ->
    b = (code_region ce) ->
    e = (b ^+ (length (code ce)))%a ->
    (* TODO: either points-to in invariant, or upd modality in implication *)
    na_inv logrel_nais (trusted_computeN.@I)
      ([[ b , e ]] ↦ₐ{ v } [[ (code ce) ]]  ∗
       [[ b' , e' ]] ↦ₐ{ v' } [[ enclave_data ]])
    ∗ seal_pred ot (Penc ce)
    ∗ seal_pred (ot^+1)%ot (Psign ce) -∗
    interp (LCap E b e (b^+1)%a v).

  (* Trusted Compute Custom Predicates *)
  Definition tc_enclave_pred tc_data_cap tc_addr : CustomEnclave :=
   MkCustomEnclave
     (trusted_compute_enclave tc_data_cap)
     tc_addr
     (λ w, False%I)
     sealed_42.

  Definition tcenclaves_map tc_data_cap tc_addr : custom_enclaves_map :=
   {[hash_trusted_compute_enclave := tc_enclave_pred tc_data_cap tc_addr]}.


  Lemma tc_contract tc_data_cap tc_addr :
    custom_enclave_contract (tcenclaves_map tc_data_cap tc_addr).
  Proof.
    rewrite /custom_enclave_contract.
    iIntros (I b e a v b' e' a' v' enclave_data ot ce
      Hwf_cemap Hcode_ce Hdatacap Hdata_seal Hot Hb' Hwfbe HIhash Hb He)
      "(#Htc_inv & #HPenc & #HPsign)".
    rewrite /tcenclaves_map in Hwf_cemap,Hcode_ce.
    rewrite /custom_enclaves_map_wf in Hwf_cemap.
    rewrite map_Forall_insert in Hwf_cemap; last by simplify_map_eq.
    destruct Hwf_cemap as [ Hwf_hash _ ].
    cbn in Hwf_hash.
    destruct (decide (I = hash_trusted_compute_enclave)) as [->|] ; last by simplify_map_eq.
    clear HIhash Hwf_hash.
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext ; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    simplify_map_eq.
    rewrite /interp_conf.
    iMod (na_inv_acc with "Htc_inv Hna") as "(>[Htc_code Htc_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".

    (* Prepare the necessary resources *)
    (* Registers *)
    assert (exists w0, lregs !! r_t0 = Some w0) as Hrt0 by apply (Hfullmap r_t0).
    destruct Hrt0 as [w0 Hr0].
    replace (delete PC lregs)
            with (<[r_t0:=w0]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w1, lregs !! r_t1 = Some w1) as Hrt1 by apply (Hfullmap r_t1).
    destruct Hrt1 as [w1 Hr1].
    replace (delete PC lregs)
            with (<[r_t1:=w1]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w2, lregs !! r_t2 = Some w2) as Hrt2 by apply (Hfullmap r_t2).
    destruct Hrt2 as [w2 Hr2].
    replace (delete PC lregs)
            with (<[r_t2:=w2]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    assert (exists w3, lregs !! r_t3 = Some w3) as Hrt3 by apply (Hfullmap r_t3).
    destruct Hrt3 as [w3 Hr3].
    replace (delete PC lregs)
            with (<[r_t3:=w3]> (delete PC lregs)).
    2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

    iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3] as ["Hr0";"Hr1";"Hr2";"Hr3"].

    (* Code memory *)
    iDestruct (region_mapsto_cons with "Htc_code") as "[Htc_addr Htc_code]"; last iFrame.
    { transitivity (Some (tc_addr ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }
    iAssert (codefrag (tc_addr ^+ 1%nat)%a v trusted_compute_enclave_code)
      with "[Htc_code]" as "Htc_code".
    {
      rewrite /codefrag /=.
      by replace ((tc_addr ^+ 1%nat) ^+ 20%nat)%a with (tc_addr ^+ 21%nat)%a by solve_addr.
    }
    codefrag_facts "Htc_code".

    (* Data memory *)
    assert (exists enclave_data', enclave_data = (LSealRange (true, true) ot (ot ^+ 2)%f ot)::enclave_data')
    as Henclave_data.
    { destruct enclave_data; cbn in *; first done.
      eexists; inv Hdata_seal; f_equal.
    }
    destruct Henclave_data as [enclave_data' ->].
    iDestruct (region_mapsto_cons with "Htc_data") as "[Htc_keys Htc_data]"; last iFrame.
    { transitivity (Some (b' ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }


    (* Prove the spec *)
    iInstr "Htc_code". (* Mov r_t1 PC *)
    admit.
    iInstr "Htc_code". (* Lea r_t1 (-1)%Z *)
    admit.
    transitivity (Some tc_addr); auto ; solve_addr.

    iInstr "Htc_code". (* Load r_t1 r_t1 *)
    admit.
    apply le_addr_withinBounds; solve_addr.
    iInstr "Htc_code". (* GetB r_t2 r_t1 *)
    admit.
    iInstr "Htc_code". (* GetA r_t3 r_t1 *)
    admit.
    iInstr "Htc_code". (* Sub r_t2 r_t2 r_t3 *)
    admit.
    iInstr "Htc_code". (* Lea r_t1 r_t2 *)
    admit.
    transitivity (Some b'); auto ; solve_addr.

    iInstr "Htc_code". (* Load r_t1 r_t1 *)
    admit.
    apply le_addr_withinBounds; solve_addr.
    iInstr "Htc_code". (* GetE r_t3 r_t1 *)
    admit.
    iInstr "Htc_code". (* Sub r_t3 r_t2 1 *)
    admit.
    replace (((ot ^+ 2)%f - 1)) with (ot + 1) by solve_finz.
    iInstr "Htc_code". (* Subseg r_t1 r_t2 r_t3 *)
    admit.
    transitivity (Some (ot ^+1)%ot); auto ; solve_finz.
    apply isWithin_of_le; solve_finz.

    iInstr "Htc_code". (* Mov r_t2 PC *)
    admit.
    iInstr "Htc_code". (* GetA r_t3 r_t2 *)
    admit.
    iInstr "Htc_code". (* Sub r_t3 42 r_t3 *)
    admit.

    assert (
        ((tc_addr ^+ 1) ^+ 11 + (42 - ((tc_addr ^+ 1) ^+ 11)))%a = Some f42)
      as Hoffset by (by rewrite finz_incr_minus_id).
    iInstr "Htc_code". (* Lea r_t2 r_t3 *)
    admit.
    iInstr "Htc_code". (* Restrict r_t2 (encodePerm O) *)
    admit.
    by rewrite decode_encode_perm_inv.
    rewrite decode_encode_perm_inv.
    iInstr "Htc_code". (* Lea r_t1 1 *)
    admit.
    transitivity (Some (ot ^+ 1)%ot); auto ; solve_finz.
    iInstr "Htc_code". (* Seal r_t2 r_t2 r_t1 *)
    admit.
    by cbn.
    apply le_addr_withinBounds; solve_finz.

    (* Restrict r_t1 (encodeSealPerms (false, true)) *)
    iInstr_lookup "Htc_code" as "Hi" "Htc_code".
    wp_instr.
    iApply (wp_restrict_success_z_sr with "[HPC Hr1 Hi]")
    ; try iFrame
    ; try solve_pure
    ; repeat (rewrite decode_encode_seal_perms_inv)
    ; try done.
    admit.
    iNext; iIntros "(HPC & Hi & Hr1)".
    all: wp_pure; iInstr_close "Htc_code".

    (* Prepare the jump to adversary: prove all registers contain safe values *)
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map" ; eauto; done. }

    iAssert (interp (LSealedCap (ot ^+ 1)%f O tc_addr (tc_addr ^+ 21%nat)%a f42 v))
      as "Hinterp_sealed42".
    {
      iClear "Hinterp_map Hinterp_w0".
      rewrite /= fixpoint_interp1_eq /= /interp_sb.
      iExists sealed_42; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_42_persistent. }
      { iNext; by iExists _,_,_. }
    }

    iAssert (interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f))
      as "Hinterp_sign".
    {
      iClear "Hinterp_map Hinterp_w0 Hinterp_sealed42".
      rewrite /= fixpoint_interp1_eq /= /safe_to_unseal.
      iSplit ; first done.
      rewrite finz_seq_between_singleton; cbn ; last solve_finz.
      iSplit ; last done.
      iExists sealed_42_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply sealed_42_interp.
    }
    (* Safe to jump to safe value *)
    iDestruct (jmp_to_unknown with "Hinterp_w0") as "Hjmp"; eauto.

    iInstr "Htc_code". (* Jmp r_t0 *)
    admit.

    (* Close the opened invariant *)
    iDestruct (region_mapsto_cons with "[Htc_addr Htc_code]") as "Htc_code"
    ; try iFrame
    ; try solve_addr.
    iDestruct (region_mapsto_cons with "[Htc_keys Htc_data]") as "Htc_data"
    ; try iFrame
    ; try solve_addr.
    replace ((tc_addr ^+ 1%nat)%a ^+ length trusted_compute_enclave_code)%a with
      (tc_addr ^+ 21%nat)%a by solve_addr.
    iMod ("Hclose" with "[$Hna $Htc_code $Htc_data]") as "Hna".

    (* Wrap up the registers *)
    iInsertList "Hrmap" [r_t0;r_t1;r_t2;r_t3].
    set ( rmap' := <[r_t3:=LInt (42 - ((tc_addr ^+ 1) ^+ 11)%a)]>
                            (<[r_t2:=LSealedCap (ot ^+ 1)%f O tc_addr (tc_addr ^+ 21%nat)%a f42 v]>
                               (<[r_t1:=LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f]>
                                  (<[r_t0:=w0]> (delete PC lregs))))).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
      iApply big_sepM_insert_2; first (iApply interp_int).
      repeat (iApply big_sepM_insert_2; first done).

      iApply big_sepM_intro.
      iIntros "!>" (r w Hrr).
      assert (is_Some (delete PC lregs !! r)) as His_some by auto.
      rewrite lookup_delete_is_Some in His_some.
      destruct His_some as [Hr _].
      rewrite lookup_delete_ne in Hrr; auto.
      iApply ("Hinterp_map" $! r w); auto.
    }
    assert (dom rmap' = all_registers_s ∖ {[PC]}).
    {
      repeat (rewrite dom_insert_L).
      rewrite dom_delete_L.
      rewrite regmap_full_dom; auto.
    }
    iApply ("Hjmp" with "[]") ; eauto ; iFrame.
  Admitted.



  Lemma trusted_compute_callback_code_spec
    (b_main adv adv_end: Addr)
    (pc_v : Version)

    (b_link a_link e_link assert_entry : Addr) (* linking *)
    (assert_lt_offset : Z)
    (b_assert e_assert a_flag : Addr) (v_assert : Version) (* assert *)
    (w0 w1 w2 w3 w4 w5 : LWord)
    tc_data_cap tc_addr
    φ :

    let v_link := pc_v in
    let link_cap := LCap RO b_link e_link a_link v_link in

    let e_main := (b_main ^+ trusted_compute_main_len)%a in
    let a_callback := (b_main ^+ trusted_compute_main_init_len)%a in
    let a_data := (b_main ^+ trusted_compute_main_code_len)%a in

    let trusted_compute_main := trusted_compute_main_code assert_lt_offset in
    ContiguousRegion b_main trusted_compute_main_len ->


    (a_link + assert_lt_offset)%a = Some assert_entry →
    withinBounds b_link e_link assert_entry = true ->

    (* TODO: should be proved *)
    custom_enclaves_map_wf (tcenclaves_map tc_data_cap tc_addr) ->

    (link_table_inv
       v_link
       assert_entry b_assert e_assert v_assert
    ∗ assert_inv b_assert a_flag e_assert v_assert
    ∗ flag_inv a_flag v_assert)
    ∗ custom_enclave_inv (tcenclaves_map tc_data_cap tc_addr)
    ∗ interp w1
    ∗ interp w0

    ⊢ ((
          codefrag b_main pc_v trusted_compute_main
          ∗ ((a_data)%a, pc_v) ↦ₐ link_cap
          ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LCap RWX b_main e_main a_data pc_v)

          ∗ PC ↦ᵣ LCap RX b_main e_main a_callback pc_v
          ∗ r_t0 ↦ᵣ w0
          ∗ r_t1 ↦ᵣ w1
          ∗ r_t2 ↦ᵣ w2
          ∗ r_t3 ↦ᵣ w3
          ∗ r_t4 ↦ᵣ w4
          ∗ r_t5 ↦ᵣ w5
          ∗ na_own logrel_nais ⊤

          (* NOTE this post-condition stops after jumping to the adversary *)
          ∗ ▷ ( codefrag b_main pc_v trusted_compute_main
                ∗ ((a_data)%a, pc_v) ↦ₐ link_cap
                ∗ ((a_data ^+ 1)%a, pc_v) ↦ₐ (LCap RWX b_main e_main a_data pc_v)

                ∗ PC ↦ᵣ LCap RX b_main e_main (a_data ^+ (-2))%a pc_v
                ∗ r_t0 ↦ᵣ LInt 0
                ∗ r_t1 ↦ᵣ LInt 0
                ∗ r_t2 ↦ᵣ LInt 0
                ∗ r_t3 ↦ᵣ LInt 0
                ∗ r_t4 ↦ᵣ LInt 0
                ∗ r_t5 ↦ᵣ LInt 0
                ∗ na_own logrel_nais ⊤

                  -∗ WP (Instr Halted) {{ φ }}))
         -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.

    (* We define a local version of solve_addr, which subst and unfold every computed addresses  *)
    Local Tactic Notation "solve_addr'" :=
      repeat (lazymatch goal with x := _ |- _ => subst x end)
      ; repeat (match goal with
                  | H: ContiguousRegion _ _  |- _ =>
                      rewrite /ContiguousRegion /trusted_compute_main_len in H
                end)
      ; rewrite !/trusted_compute_main_code_len /trusted_compute_main_len
          /trusted_compute_main_init_len /trusted_compute_main_callback_len
      ; solve_addr.

    intros ?????? Hregion Hassert Hlink Hwf_cemap.
    iIntros "#[ [HlinkInv [HassertInv HflagInv] ] [ Hcemap_inv [ Hinterp_w1 Hinterp_w0]] ]
             (Hcode & Hlink_cap & Hdata1 & HPC & Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hna & Hcont)".
    codefrag_facts "Hcode".

    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)

    destruct (is_sealedL w0) eqn:Hsealed_w0 ; cycle 1.
    { (* w0 is not a sealed  *)
      destruct_lword (w0) ; cbn in Hsealed_w0 ; try done.
      all: iInstr "Hcode". (* GetOType *)
      all: iInstr "Hcode". (* Sub *)
      all: replace (-1 - -1) with 0 by lia.
      all: iInstr "Hcode". (* Mov *)
      all: iInstr "Hcode". (* Lea *)
      all: iInstr "Hcode". (* Jnz *)
      all: iInstr "Hcode". (* Jmp *)
      all: iInstr "Hcode". (* Fail *)
      all: by (wp_end; iRight).
    }

    destruct w0 as [ ? | ? | o sw0 ]
    ; cbn in Hsealed_w0 ; try done; clear Hsealed_w0.

    iInstr "Hcode". (* GetOType *)
    iInstr "Hcode". (* Sub *)
    replace (o - -1) with (o + 1) by lia.
    assert (Ho : LInt (o + 1) ≠ LInt 0) by (clear ; intro ; inversion H ; solve_finz).
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)
    iInstr "Hcode". (* Jnz *)
    iInstr "Hcode". (* GetOType *)

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_estoreid_success_unknown with "[HPC Hr2 Hr4 Hi]"); try iFrame; try solve_pure.
    iNext.
    iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr2 & [(-> & HPC & H)|(-> & HPC & Hr4)])".
    iDestruct "H" as (I tid) "(Hr4 & #Htc_env & %Hseal)".
    all: wp_pure; iInstr_close "Hcode".
    2:{ wp_end; by iRight. }

    iInstr "Hcode". (* Sub *)
    destruct (decide (I = hash_trusted_compute_enclave)) as [-> | HnI]
    ; cycle 1.
    { (* Not the right enclave *)
      iInstr "Hcode". (* Jnz *)
      by (injection; intro Hcontra; lia).
      iInstr "Hcode". (* Fail *)
      wp_end; by iRight.
    }
    replace (hash_trusted_compute_enclave - hash_trusted_compute_enclave)
      with 0 by lia.
    iInstr "Hcode". (* Jnz *)
    iDestruct (interp_valid_sealed with "Hinterp_w0") as (Φ) "Hseal_valid".
    rewrite /custom_enclave_inv.


    (* UnSeal *)
    wp_instr.
    iMod (inv_acc with "Hcemap_inv") as "(#Hcemap & Hclose)"; first solve_ndisj.

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr0") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap Hi]"); eauto; simplify_map_eq; eauto;
    try solve_pure.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds Hregs'|]; cycle 1.
    { iMod ("Hclose" with "Hcemap") as "_". iModIntro.
      by wp_pure; wp_end; iRight.
    }
    iMod ("Hclose" with "Hcemap") as "_"; iModIntro.
    incrementLPC_inv as (p''&b_main'&e_main'&a_main'&pc_v'& ? & HPC & Z & Hregs'); simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    replace x with (b_main' ^+ 20)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr0] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hcode".

    iAssert (
        if Z.even a
        then seal_pred a (Penc (tc_enclave_pred tc_data_cap tc_addr))
             ∗ seal_pred (a ^+ 1)%f (Psign (tc_enclave_pred tc_data_cap tc_addr))
        else seal_pred (a ^+ -1)%f (Penc (tc_enclave_pred tc_data_cap tc_addr))
             ∗ seal_pred a (Psign (tc_enclave_pred tc_data_cap tc_addr))
      )%I as "Htc".
    {
      iApply "Hcemap"; iFrame "%#∗".
      iPureIntro.
      rewrite /tcenclaves_map.
      by simplify_map_eq.
    }

    destruct (Z.even (finz.to_z a)) eqn:HEven_a
    ; iDestruct "Htc" as "[Htc_Penc Htc_Psign]"
    ; iEval (cbn) in "Htc_Penc"
    ; iEval (cbn) in "Htc_Psign".
    {
      iDestruct (seal_pred_valid_sealed_eq with "[$Htc_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }

    iDestruct (seal_pred_valid_sealed_eq with "[$Htc_Psign] Hseal_valid") as "Heqv".
    iAssert (▷ sealed_42 (LWSealable sb))%I as (fb fe fv) ">%Hseal42".
    { iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      iRewrite "Heqv".
      iFrame "HΦ". }
    destruct sb ; simplify_eq.
    iClear "Heqv Htc_Penc Hcemap Hcemap_inv".

    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* GetA *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Mov *)
    iInstr "Hcode". (* Lea *)
    iInstr "Hcode". (* Load *)

    subst trusted_compute_main.
    rewrite /trusted_compute_main_code /trusted_compute_main_code_callback0.
    subst a_callback.
    rewrite /trusted_compute_main_init_len.

    focus_block 2%nat "Hcode" as addr_block2 Haddr_block2 "Hblock" "Hcode'".
    cbn in Haddr_block2.
    iMod (na_inv_acc with "HlinkInv Hna") as "(>Hassert_entry & Hna & Hclose)"; [ solve_ndisj.. |].
    iApply assert_reg_success; last iFrame "#∗"; try solve_pure ; try solve_addr'.
    solve_ndisj.
    iIntros "!> (HPC & Hr0 & Hr1 & Hr2 & Hr4 & Hr5 & Hblock & Hna & Hassert_entry)".
    iMod ("Hclose" with "[$Hna $Hassert_entry]") as "Hna".
    iAssert (codefrag addr_block2 pc_v' (assert_reg_instrs assert_lt_offset r_t1)) with "[$Hblock]" as "Hblock".
    unfocus_block "Hblock" "Hcode'" as "Hcode".

    focus_block 3%nat "Hcode" as addr_block3 Haddr_block3 "Hblock" "Hcode'".
    cbn in Haddr_block3.
    iInstr "Hblock". (* Mov *)
    admit. (* TODO why automation doesn't work here? *)
    iInstr "Hblock". (* Mov *)
    admit. (* TODO why automation doesn't work here? *)
    iInstr "Hblock". (* Halt *)
    admit. (* TODO why automation doesn't work here? *)
    unfocus_block "Hblock" "Hcode'" as "Hcode".
    replace (addr_block3 ^+ 2)%a with (a_data ^+ -2)%a by solve_addr'.

    iApply (wp_wand with "[-]") ; [  | iIntros (?) "H"; iLeft ; iApply "H"].
    iApply "Hcont"; iFrame.
    Admitted.

End trusted_compute_example.
