From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
(* From cap_machine Require Import logrel fundamental. *)
From cap_machine Require Import logrel.
From cap_machine Require Import proofmode.
(* From cap_machine Require Import macros_new. *)
Open Scope Z_scope.

Section mutual_attest_example.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context (malloc_entry_point : LWord).
  Context (ma_addr_A ma_addr_B : Addr).

  (* -------------------------------------- *)
  (* ------ MUTUAL ATTEST *ENCLAVES* ------ *)
  (* -------------------------------------- *)

  (* Expects:
     - r_t0 contains return pointer to adv
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  (* Dynamic check:
     data[0] = #A
     data[1] = #A
     data[2] = malloc_entry_point
   *)
  Definition mutual_attest_enclave_A_code_pre : list LWord :=
    encodeInstrsLW [

      (* fetch ?malloc *)
      (* hash ?malloc *)
      (* if #?malloc =! #malloc_entry_point --> fail *)

      (* malloc a buffer b of size 3:
         will be used to communicate
      *)

      (* let idA := hash PC[1::-] *)
      (* let idT := data[0-1] *)

      (* if idA != idT, then fail *)

      (* hash idT *)

      (* let mbA := base(b) % 3 *)
      (* if mbA == 0,
         then we can use
         + mbA[0] for #idT
         + mbA[1] for 42    // attestation of A for B
         + mbA[2] for 1     // attestation of A for main
       *)
      (* if mbA == 1,
         then we can use
         + mbA[0] for 1     // attestation of A for main
         + mbA[1] for #idT
         + mbA[2] for 42    // attestation of A for B
       *)
      (* if mbA == 2,
         then we can use
         + mbA[0] for 42    // attestation of A for B
         + mbA[1] for 1     // attestation of A for main
         + mbA[2] for #idT
       *)

      (* fetch sign key *)
      (* signs { mbA[#idT] }_signed_A *)
      (* signs { mbA[w42] }_signed_A *)

      (* call ENCLAVE B with
        r_t30 := return pointer;
        r_t1  := { mbA[#idT] }_signed_A;
        r_t2  := { mbA[w42] }_signed_A;
        r_t3  := pub_sign_key_A;
      *)

      (* ---- we only arrive here if B has successfully attested A ---- *)
      (* receives:
        r_t1  := { mbB[#idT] }_signed_B;
        r_t2  := { mbB[w43] }_signed_B;
        r_t3  := pub_sign_key_B;
      *)

      (* ATTEST B *)
      (* TODO @June: how do I attest
         the value returned by B
      *)
      (* if mbA[#idT] != mbB[#idT], then fail *)

      (* CHECK ATTESTS B *)
      (* get idT(B) in r_t2 *)
      (* get hash(idT) in r_t3 *)
      (* get hash_concat(idT(B),idT) in r_t3 *)

      (* compare identity(r_t1) == r_t3 *)

      (* assert unsealed( {43}_signed_B ) = 43 *)

      Jmp r_t0
      (* REST OF CODE OF A *)
    ].

  (* Expects:
     - r_t0 contains return pointer to caller
     - r_t1 contains entry point to ENCLAVE B, not attested yet
   *)
  Definition mutual_attest_enclave_B_code_pre : list LWord :=
    let size_idT : Z := 2 in
    let offset_idA : Z := 0 in
    let offset_idB : Z := 1 in
    encodeInstrsLW [
      (* CODE INITIALISATION ENCLAVE B *)

      (* receives:
         r_t1 := {42}_signed_A;
         r_t2 := pub_sign_key_A;
      *)

      (* CHECK ATTESTS A *)
      (* get idT(A) in r_t3 *)

      Mov r_t4 PC;                (* r4 := (RX, pc_b, pc_e, pc_a) *)
      GetA r_t5 r_t4;             (* r5 := pc_a *)
      GetE r_t6 r_t4;             (* r6 := pc_e *)
      Sub r_t5 r_t6 r_t5;         (* r5 := pc_e - pc_a *)
      Lea r_t4 r_t5;              (* r4 := (RX, pc_b, pc_e, pc_e) *)
      Lea r_t4 (-size_idT)%Z;     (* r4 := (RX, pc_b, pc_e, a_idT) *)

      Mov r_t3 r_t4;              (* r3 := (RX, pc_b, pc_e, a_idT) *)
      Lea r_t3 offset_idA;        (* r3 := (RX, pc_b, pc_e, a_idT(A)) *)
      Load r_t3 r_t3;             (* r3 := idT(A) *)

      (* get hash(idT) in r_t4 *)
      GetA r_t5 r_t4;             (* r5 := a_idT *)
      Subseg r_t4 r_t5 r_t6;      (* r4 := (RX, a_idT pc_e, a_idT) *)
      Hash r_t4 r_t4;             (* r4 := #[a_idT;pc_E] *)

      (* get hash_concat(idT(A),idT) in r_t3 *)
      HashConcat r_t3 r_t3 r_t4;  (* r3 := idT(A) || #[a_idT;pc_E] *)

      (* compare identity(r_t1) == r_t3 *)
      GetOType r_t4 r_t1;         (* r4 := ?signed_A *)
      Add r_t4 r_t4 1;            (* r5 := if is_sealed(r_t1) = false then 0 else not0 *)

      (* if  is_sealed(r_t1) then continue else fail *)
      Mov r_t5 PC;
      Lea r_t5 4;
      Jnz r_t5 r_t4;
      Fail;

      GetOType r_t5 r_t1;         (* r5 := ?signed_A *)
      EStoreId r_t4 r_t5;         (* r4 := I_signed_A *)
      Sub r_t3 r_t3 r_t4;         (* r3 := (idT(A) || #[a_idT;pc_E]) - ?signed_A*)

      (* if ?signed_A != (idT(A) || #[a_idT;pc_E])
         then Fail
         else continue *)
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t3;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      UnSeal r_t1 r_t2 r_t1;      (* r1 := unsealed( {(RO,a, a+1,a)}_signed_A ) ; a -> 42 *)
      (* if (unsealed( {42}_signed_A ) != 42)
         then Fail
         else continue
       *)
      (* TODO remove the NOP thanks to later credit? *)
      Mov r_t0 r_t0; (* NOP instruction for getting rid off the later *)

      GetA r_t2 r_t1;             (* r2 := a *)
      Mod r_t2 r_t2 2;            (* r2 := a%2 *)
      (* if a%2 != 0 then Fail else continue *)
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      Load r_t1 r_t1;     (* r1 := ?42 *)
      (* if ?42 != 42 then Fail else continue *)
      Sub r_t1 r_t1 42;
      Lea r_t5 6;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      (* fetch data_cap *)
      GetA r_t1 r_t5;
      GetB r_t2 r_t5;
      Sub r_t1 r_t1 r_t2;
      Lea r_t5 r_t1;
      Load r_t1 r_t5;       (* r1 := (RW, data_b, data_e, data_a) *)

      (* fetch sign_key *)
      GetA r_t2 r_t1;
      GetB r_t3 r_t1;      (* r3 := data_b *)
      Sub r_t2 r_t2 r_t3;
      Lea r_t1 r_t2;       (* r1 := (RW, data_b, data_e, data_b) *)
      Load r_t6 r_t1;      (* r6 := [SU, σ, σ+2, σ] *)
      (* fetch malloc *)
      Lea r_t1 1;          (* r1 := (RW, data_b, data_e, data_b+1) *)
      Load r_t2 r_t1;      (* r2 := ?malloc *)
      (* hash malloc *)
      Add r_t3 r_t3 1;     (* r3 := data_b + 1 *)
      Add r_t4 r_t3 1;     (* r4 := data_b + 2 *)
      Subseg r_t1 r_t3 r_t4; (* r1 := (RW, data_b + 1, data_b + 2, data_b+1) *)
      Hash r_t1 r_t1;      (* r1 := #(?malloc) *)

      (* if #(?malloc) != #(malloc_entry_point) then Fail else continue *)
      Sub r_t1 r_t1 (hash malloc_entry_point);
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      (* call malloc(2) --> r0-r4 are clobbered, but we only care about r6, so it's fine *)
      Mov r_t2 r_t1;
      Mov r_t1 2;
      Jmp r_t2;
      (* r1 := (RWX, x, x+2, x) *)

      (* prepare the result capabilities *)
      Mov r_t1 r_t4;        (* r4 := (RWX, x, x+2, x) *)
      Lea r_t4 1;           (* r4 := (RWX, x, x+2, x+1) *)
      GetA r_t2 r_t1;       (* r2 := x *)
      Add r_t3 r_t2 1;      (* r3 := x+1 *)
      Subseg r_t1 r_t2 r_t3; (* r1 := (RWX, x, x+1, x) *)
      Add r_t5 r_t3 1;      (* r5 := x+2 *)
      Subseg r_t4 r_t3 r_t5; (* r4 := (RWX, x+1, x+2, x+1) *)
      Mod r_t2 r_t2 2;      (* r2 := x%2 *)

      (* if x%2 = 0 then mb=[42;1] else  mb=[1;42] *)
      Mov r_t5 PC;
      Lea r_t5 7;
      Jnz r_t5 r_t2;

      (* case x%2 == 0 *)
      Store r_t1 42;
      Store r_t4 1;
      Lea r_t5 2;
      Jmp r_t5;
      (* case x%2 == 1 *)
      Store r_t1 1;
      Store r_t4 42;

      (* continue here  *)
      Restrict r_t1 (encodePerm RO);
      Restrict r_t4 (encodePerm RO);

      (* sign x and sign x+1 *)
      Lea r_t6 1;            (* r6 := (SU, σ+1, σ+2, σ+1) *)
      Seal r_t1 r_t6 r_t1;
      Seal r_t2 r_t6 r_t4;

      GetA r_t3 r_t6;        (* r3 := σ+1 *)
      Add r_t4 r_t3 1;       (* r4 := σ+2 *)
      Subseg r_t6 r_t3 r_t4; (* r6 := (SU, σ+1, σ+2, σ+1) *)
      Restrict r_t6 (encodeSealPerms (false,true));

      (* clear regs and jmp to adv *)
      Mov r_t3 r_t6;
      Mov r_t4 0;
      Mov r_t5 0;
      Mov r_t6 0;
      Jmp r_t0
    ].

  Definition hash_mutual_attest_A_pre : Z :=
    hash_concat (hash ma_addr_A) (hash mutual_attest_enclave_A_code_pre).
  Definition hash_mutual_attest_B_pre : Z :=
    hash_concat (hash ma_addr_B) (hash mutual_attest_enclave_B_code_pre).

  Definition mutual_attest_eid_table : list LWord :=
    [ LWInt hash_mutual_attest_A_pre; LWInt hash_mutual_attest_B_pre ].


  Definition mutual_attest_enclave_A_code : list LWord :=
   (mutual_attest_enclave_A_code_pre ++ mutual_attest_eid_table).
  Definition mutual_attest_enclave_B_code : list LWord :=
   (mutual_attest_enclave_B_code_pre ++ mutual_attest_eid_table).

  Definition hash_mutual_attest_A : Z :=
    hash_concat (hash ma_addr_A) (hash mutual_attest_enclave_A_code).
  Definition hash_mutual_attest_B : Z :=
    hash_concat (hash ma_addr_B) (hash mutual_attest_enclave_B_code).

  Definition mutual_attest_enclave_A (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_A_code ++ mutual_attest_eid_table.

  Definition mutual_attest_enclave_B (enclave_data_cap : LWord) : list LWord :=
    enclave_data_cap::mutual_attest_enclave_B_code  ++ mutual_attest_eid_table.

  Definition mutual_attestN : namespace := nroot .@ "mutual_attest".

  (* Sealed predicate for enclave A *)
  Definition prot_sealed_A (a : Addr) (lw : LWord) : iProp Σ:=
    ⌜ if (decide (a `mod` 2 = 0 ))
      then lw = LInt 42
      else lw = LInt 1 ⌝%I.

  Definition sealed_enclaveA : LWord → iProp Σ :=
    λ w, (∃ a v,
             ⌜ w = LCap RO a (a^+1)%a a v ⌝
             ∗ ⌜(a+1)%a = Some (a^+1)%a ⌝
             ∗ (inv (logN.@(a, v)) (∃ lw, (a,v) ↦ₐ lw ∗ prot_sealed_A a lw)))%I.
  Definition sealed_enclaveA_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveA w%I.

  Instance sealed_enclaveA_persistent (w : LWord) : Persistent (sealed_enclaveA w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveA (τ : OType) := seal_pred τ sealed_enclaveA.
  Definition valid_sealed_enclaveA_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveA.
  Lemma sealed_enclaveA_interp (lw : LWord) : sealed_enclaveA lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (a v -> HB) "Hinv".
    rewrite fixpoint_interp1_eq /=.
    rewrite finz_seq_between_singleton; auto.
    iApply big_sepL_singleton.
    iExists (λne (lw : leibnizO LWord), prot_sealed_A a lw).
    iFrame "Hinv".
    iSplit.
    - iPureIntro. intros lw. apply _.
    - iNext ; iModIntro.
      iIntros (lw Hlw); cbn.
      destruct (decide (a `mod` 2 = 0)); simplify_eq; by rewrite fixpoint_interp1_eq.
  Qed.


  (* Sealed predicate for enclave B *)
  Definition prot_sealed_B (a : Addr) (lw : LWord) : iProp Σ:=
    ⌜ if (decide (a `mod` 2 = 0 ))
      then lw = LInt 43
      else lw = LInt 1 ⌝%I.

  Definition sealed_enclaveB : LWord → iProp Σ :=
    λ w, (∃ a v,
             ⌜ w = LCap RO a (a^+1)%a a v ⌝
             ∗ ⌜(a+1)%a = Some (a^+1)%a ⌝
             ∗ (inv (logN.@(a, v)) (∃ lw, (a,v) ↦ₐ lw ∗ prot_sealed_B a lw)))%I.
  Definition sealed_enclaveB_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveB w%I.

  Instance sealed_enclaveB_persistent (w : LWord) : Persistent (sealed_enclaveB w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveB (τ : OType) := seal_pred τ sealed_enclaveB.
  Definition valid_sealed_enclaveB_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveB.
  Lemma sealed_enclaveB_interp (lw : LWord) : sealed_enclaveB lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (a v -> HB) "Hinv".
    rewrite fixpoint_interp1_eq /=.
    rewrite finz_seq_between_singleton; auto.
    iApply big_sepL_singleton.
    iExists (λne (lw : leibnizO LWord), prot_sealed_B a lw).
    iFrame "Hinv".
    iSplit.
    - iPureIntro. intros lw. apply _.
    - iNext ; iModIntro.
      iIntros (lw Hlw); cbn.
      destruct (decide (a `mod` 2 = 0)); simplify_eq; by rewrite fixpoint_interp1_eq.
  Qed.


  (* Trusted Compute Custom Predicates *)
  Definition mutual_attest_enclave_A_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_A_code
      ma_addr_A
      (λ w, False%I)
      sealed_enclaveA.
  Definition mutual_attest_enclave_B_pred : CustomEnclave :=
    @MkCustomEnclave Σ
      mutual_attest_enclave_B_code
      ma_addr_B
      (λ w, False%I)
      sealed_enclaveB.

  Definition ma_enclaves_map : custom_enclaves_map :=
   {[ hash_mutual_attest_A := mutual_attest_enclave_A_pred;
      hash_mutual_attest_B := mutual_attest_enclave_B_pred
   ]}.

  Lemma wf_ma_enclaves_map :
    custom_enclaves_map_wf ma_enclaves_map.
  Proof.
    rewrite /custom_enclaves_map_wf /ma_enclaves_map.
    apply (map_Forall_insert_2 (λ (I : Z) (ce : CustomEnclave), _)).
    - by rewrite /hash_mutual_attest_A /=.
    - by rewrite map_Forall_singleton /hash_mutual_attest_B /=.
  Qed.

  Lemma wp_hash_success_same Ep
    pc_p pc_b pc_e pc_a pc_a' pc_v
    dst p b e a v ws lw
    :

    decodeInstrWL lw = Hash dst dst →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    readAllowed p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
        ∗ ▷ dst ↦ᵣ LCap p b e a v
        ∗ ▷ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
    }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v
        ∗ ▷ (pc_a, pc_v) ↦ₐ lw
          ∗ dst ↦ᵣ LWInt (hash ws)
          ∗ [[ b , e ]] ↦ₐ{ v } [[ ws ]]
      }}}.
  Proof.
  Admitted.

  Axiom hash_concat_app : forall {A : Type} (la la' : list A),
    hash (la++la') = hash_concat (hash la) (hash la').
  Axiom hash_concat_assoc : Assoc eq hash_concat.
  Global Instance hash_concat_Assoc : Assoc eq hash_concat := hash_concat_assoc.

  Lemma mutual_attest_contract :
    custom_enclave_contract ma_enclaves_map.
  Proof.
    rewrite /custom_enclave_contract.
    iIntros (I b e a v b' e' a' v' enclave_data ot ce
      Hwf_cemap Hcode_ce Hot Hb' HIhash Hb He)
      "(#Henclaves_inv & #Hma_inv & #HPenc & #HPsign)".
    clear HIhash.
    clear Hwf_cemap.
    assert (e = (b ^+ (length (code ce) + 1))%a) as -> by solve_addr+He.

    rewrite /ma_enclaves_map in Hcode_ce.
    simplify_map_eq.

    assert (I = hash_mutual_attest_A \/ I = hash_mutual_attest_B) as HI.
    { rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      rewrite lookup_insert_Some in Hcode_ce.
      destruct Hcode_ce as [ [? _] | [_ Hcode_ce] ]; first auto.
      done.
    }
    destruct HI ; simplify_map_eq.
    - rewrite fixpoint_interp1_eq /=.
      iIntros (lregs); iNext ; iModIntro.
      iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
      rewrite /interp_conf.
      iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
      rewrite /registers_mapsto.
      iExtract "Hrmap" PC as "HPC".
      remember ma_addr_A as pc_b in |- * at 7.
      remember (ma_addr_A ^+ (3%nat + 1))%a as pc_e in |- * at 4.
      assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (3%nat + 1))%a) by (subst; solve_addr).
      admit.
    - rewrite lookup_insert_ne // in Hcode_ce.
      2:{ rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
          intro Hcontra.
          apply hash_concat_inj' in Hcontra.
          destruct Hcontra as [_ Hcontra].
          rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra.
          by injection Hcontra.
      }
      simplify_map_eq.
      rewrite fixpoint_interp1_eq /=.
      iIntros (lregs); iNext ; iModIntro.
      iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
      rewrite /interp_conf.
      iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
      rewrite /registers_mapsto.
      iExtract "Hrmap" PC as "HPC".
      remember ma_addr_B as pc_b in |- * at 7.
      remember (ma_addr_B ^+ (38%nat + 1))%a as pc_e in |- * at 4.
      assert (SubBounds pc_b pc_e ma_addr_B (ma_addr_B ^+ (32%nat + 1))%a) by (subst; solve_addr).

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

      assert (exists w4, lregs !! r_t4 = Some w4) as Hrt4 by apply (Hfullmap r_t4).
      destruct Hrt4 as [w4 Hr4].
      replace (delete PC lregs)
        with (<[r_t4:=w4]> (delete PC lregs)).
      2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

      assert (exists w5, lregs !! r_t5 = Some w5) as Hrt5 by apply (Hfullmap r_t5).
      destruct Hrt5 as [w5 Hr5].
      replace (delete PC lregs)
        with (<[r_t5:=w5]> (delete PC lregs)).
      2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

      assert (exists w6, lregs !! r_t6 = Some w6) as Hrt6 by apply (Hfullmap r_t6).
      destruct Hrt6 as [w6 Hr6].
      replace (delete PC lregs)
        with (<[r_t6:=w6]> (delete PC lregs)).
      2: { rewrite insert_id; auto. rewrite lookup_delete_ne; auto. }

      (* EXTRACT REGISTERS FROM RMAP *)
      (* iExtractList "Hrmap" [r_t0;r_t1;r_t2;r_t3] as ["Hr0";"Hr1";"Hr2";"Hr3"]. *)
      iDestruct (big_sepM_delete _ _ r_t0 with "Hrmap") as "[Hr0 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr1 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t5 with "Hrmap") as "[Hr5 Hrmap]".
      { by simplify_map_eq. }
      iDestruct (big_sepM_delete _ _ r_t6 with "Hrmap") as "[Hr6 Hrmap]".
      { by simplify_map_eq. }
      replace (delete r_t6 _) with
        ( delete r_t6 ( delete r_t5 ( delete r_t4 ( delete r_t3 (delete r_t2 (delete r_t1 (delete r_t0 (delete PC lregs)))))))).
      2:{
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t0) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t1) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t2) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t3) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t4) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t5) //.
        rewrite delete_insert_delete; repeat rewrite (delete_insert_ne _ r_t6) //.
        done.
      }
      iAssert (interp w1) as "Hinterp_w1".
      { iApply "Hinterp_map";eauto;done. }
      iAssert (interp w2) as "Hinterp_w2".
      { iApply "Hinterp_map";eauto;done. }

      (* Code memory *)
      iDestruct (region_mapsto_cons with "Hma_code") as "[Hma_addr_B Hma_code]"; last iFrame.
      { transitivity (Some (ma_addr_B ^+ 1)%a); auto ; try solve_addr. }
      { solve_addr. }
      rewrite /mutual_attest_enclave_B_code.

      iDestruct (region_mapsto_split _ _ (ma_addr_B ^+ (36%nat + 1))%a with "Hma_code") as "[Hma_code HidT]"; last iFrame.
      { solve_addr. }
      { cbn. admit. }
      rewrite /mutual_attest_eid_table.
      iDestruct (region_mapsto_cons with "HidT") as "[HidTA HidTB]".
      { transitivity (Some (ma_addr_B ^+ (36%nat + 2))%a); auto ; try solve_addr. }
      { solve_addr. }
      (* iDestruct (region_mapsto_cons with "HidTB") as "[HidTB _]". *)
      (* { transitivity (Some (ma_addr_B ^+ (31%nat + 2))%a); auto ; try solve_addr. } *)
      (* { solve_addr. } *)



      iAssert (codefrag (ma_addr_B ^+ 1%nat)%a v mutual_attest_enclave_B_code_pre)
        with "[Hma_code]" as "Hma_code".
      {
        rewrite /codefrag /=.
        by replace ((ma_addr_B ^+ 1%nat) ^+ 36%nat)%a with (ma_addr_B ^+ 37%nat)%a by solve_addr.
      }
      codefrag_facts "Hma_code".

      (* Data memory *)
      iDestruct (region_mapsto_cons with "Hma_data") as "[Hma_keys Hma_data]"; last iFrame.
      { transitivity (Some (b' ^+ 1)%a); auto ; try solve_addr. }
      { solve_addr. }


      (* Prove the spec *)
      (* Mov r_t4 PC *)
      iInstr "Hma_code".
      (* GetA r_t5 r_t4 *)
      iInstr "Hma_code".
      (* GetE r_t6 r_t4 *)
      iInstr "Hma_code".
      (* Sub r_t5 r_t6 r_t5 *)
      iInstr "Hma_code".
      (* Lea r_t4 r_t5 *)
      assert (
          ((ma_addr_B ^+ 1) + (pc_e - (ma_addr_B ^+ 1)%a))%a
          = Some pc_e
        ) as Hpce
      by (subst; solve_addr).
      iInstr "Hma_code".
      (* Lea r_t4 (-size_idT)%Z *)
      iInstr "Hma_code".
      { transitivity (Some (pc_e ^+ -2)%a); solve_addr. }

      (* Mov r_t3 r_t4 *)
      iInstr "Hma_code".
      (* Lea r_t3 offset_idA *)
      iInstr "Hma_code".
      { transitivity (Some (pc_e ^+ -2)%a); solve_addr. }
      (* Load r_t3 r_t3 *)
      replace (pc_e ^+ -2)%a  with (ma_addr_B ^+ (36%nat + 1))%a by (subst;solve_addr).
      iInstr "Hma_code".
      { subst; solve_addr. }
      (* GetA r_t5 r_t4 *)
      iInstr "Hma_code".
      (* Subseg r_t4 r_t5 r_t6 *)
      iInstr "Hma_code".
      { solve_addr. }
      (* Hash r_t4 r_t4 *)
      iInstr_lookup "Hma_code" as "Hi" "Hma_code".
      wp_instr.
      iDestruct (region_mapsto_cons _ _  with "[$HidTA $HidTB]") as "HidT".
      { solve_addr. }
      { solve_addr. }
      iApply (wp_hash_success_same with "[$HPC $Hr4 $Hi HidT]"); try solve_pure.
      { subst pc_e;iFrame. }
      iNext; iIntros "(HPC & Hi & Hr4 & HidT)".
      wp_pure; iInstr_close "Hma_code".

      (* HashConcat r_t3 r_t3 r_t4 *)
      wp_instr.
      iInstr_lookup "Hma_code" as "Hi" "Hma_code".
      iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hr4 $Hr3 $Hi]"); try solve_pure.
      { done. }
      iNext. iIntros "(HPC & Hpc_a & Hr4 & Hr3)".
      iEval (cbn) in "Hr3".
      (* NOTE we use the axiom HERE! *)
      replace
       (hash_concat hash_mutual_attest_A_pre (hash [LInt hash_mutual_attest_A_pre; LInt hash_mutual_attest_B_pre]))
        with
        hash_mutual_attest_A.
      2:{
        rewrite /hash_mutual_attest_A /hash_mutual_attest_A_pre /mutual_attest_enclave_A_code.
        by rewrite -(assoc_L hash_concat) -/mutual_attest_eid_table hash_concat_app.
      }
      wp_pure; iInstr_close "Hma_code".


    destruct (is_sealedL w1) eqn:Hsealed_w1 ; cycle 1.
    { (* w1 is not a sealed  *)
      destruct_lword (w1) ; cbn in Hsealed_w1 ; try done.
      all: iInstr "Hma_code". (* GetOType *)
      all: iInstr "Hma_code". (* Add *)
      all: replace (-1 + 1) with 0 by lia.
      all: iInstr "Hma_code". (* Mov *)
      all: iInstr "Hma_code". (* Lea *)
      all: iInstr "Hma_code". (* Jnz *)
      all: iInstr "Hma_code". (* Fail *)
      all: wp_end; by iIntros (?).
    }

    destruct w1 as [ ? | ? | o sw1 ]
    ; cbn in Hsealed_w1 ; try done; clear Hsealed_w1.
    (* GetOType r_t4 r_t1 *)
    iInstr "Hma_code".
    (* Add r_t4 r_t4 1 *)
    iInstr "Hma_code".
    assert (Ho : LInt (o + 1) ≠ LInt 0) by (clear ; intro ; inversion H ; solve_finz).
    (* Mov r_t5 PC *)
    iInstr "Hma_code".
    (* Lea r_t5 4 *)
    iInstr "Hma_code".
    (* Jnz r_t5 r_t4 *)
    iInstr "Hma_code".
    (* GetOType r_t4 r_t1 *)
    iInstr "Hma_code".
    (* EStoreId r_t4 r_t5 *)
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    wp_instr.
    iApply (wp_estoreid_success_unknown with "[$HPC $Hr5 $Hr4 $Hi]"); try solve_pure.
    iNext. iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr5 & [(-> & HPC & H)|(-> & HPC & Hr4)])".
    1: iDestruct "H" as (I tid) "(Hr4 & #Hma_env & %Hseal)".
    all: wp_pure; iInstr_close "Hma_code".
    2:{ wp_end; by iIntros (?). }
    iDestruct (interp_valid_sealed with "Hinterp_w1") as (Φ) "Hseal_valid".

    (* Sub r_t3 r_t3 r_t4 *)
    iInstr "Hma_code".
    (* Mov r_t5 PC *)
    iInstr "Hma_code".
    (* Lea r_t5 5 *)
    iInstr "Hma_code".

    destruct (decide (I = hash_mutual_attest_A)) as [-> | HnI]
    ; cycle 1.
    { (* Not the right enclave *)
      iInstr "Hma_code". (* Jnz *)
      by (injection; intro Hcontra; lia).
      iInstr "Hma_code". (* Fail *)
      wp_end; by iIntros (?).
    }
    replace ( _ - _) with 0 by lia.
    (* Jnz r_t5 r_t3 *)
    iInstr "Hma_code".
    (* Lea r_t5 1 *)
    iInstr "Hma_code".
    (* Jmp r_t5 *)
    iInstr "Hma_code".

    (* UnSeal r_t1 r_t1 r_t2 *)
    wp_instr.
    iMod (inv_acc with "Henclaves_inv") as "(Henclaves_inv_open & Hclose_inv)"; first solve_ndisj.

    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap _]".
    (* iApply (wp_UnSeal with "[$Hmap Hi]"); eauto; simplify_map_eq; eauto; try solve_pure. *)
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { apply isCorrectPC_isCorrectLPC ; cbn. constructor; last naive_solver.
      solve_addr.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds Hregs'|]; cycle 1.
    { iMod ("Hclose_inv" with "Henclaves_inv_open") as "_". iModIntro.
      by wp_pure; wp_end; by iIntros (?).
    }
    iDestruct "Henclaves_inv_open" as (ECn) "(HEC & #Hcemap)".
    iMod ("Hclose_inv" with "[HEC Hcemap]") as "_"; iModIntro.
    { iExists ECn. iFrame "HEC Hcemap". }
    Opaque mutual_attest_enclave_B_code_pre.
    incrementLPC_inv as (p''&b_main'&e_main'&a_main'&pc_v'& ? & HPC & Z & Hregs');
    simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    Transparent mutual_attest_enclave_B_code_pre.
    replace x with ((ma_addr_B ^+ 1) ^+ 29)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hma_code".

    iAssert (
        if Z.even a0
        then seal_pred a0 (Penc mutual_attest_enclave_A_pred)
             ∗ seal_pred (a0 ^+ 1)%f (Psign mutual_attest_enclave_A_pred)
        else seal_pred (a0 ^+ -1)%f (Penc mutual_attest_enclave_A_pred)
             ∗ seal_pred a0 (Psign mutual_attest_enclave_A_pred)
      )%I as "Hma_A".
    {
      iApply "Hcemap"; iFrame "%#∗".
      + iPureIntro. admit.
      + iPureIntro; apply wf_ma_enclaves_map.
      + iPureIntro; by rewrite /ma_enclaves_map; simplify_map_eq.
    }

    destruct (Z.even (finz.to_z a0)) eqn:HEven_a0
    ; iDestruct "Hma_A" as "[Hma_A_Penc Hma_A_Psign]"
    ; iEval (cbn) in "Hma_A_Penc"
    ; iEval (cbn) in "Hma_A_Psign".
    {
      iDestruct (seal_pred_valid_sealed_eq with "[$Hma_A_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }
    iDestruct (seal_pred_valid_sealed_eq with "[$Hma_A_Psign] Hseal_valid") as "Heqv".

    (* Sub r_t1 r_t1 42 *)
    iInstr "Hma_code".
    (* Lea r_t5 6 *)
    iInstr "Hma_code".
    (* Jnz r_t5 r_t1 *)
    iInstr "Hma_code".
    (* Lea r_t5 1 *)
    iInstr "Hma_code".
    (* Jmp r_t5 *)
    iInstr "Hma_code".
    (* Fail *)
    iInstr "Hma_code".

    (* Halt *)

    iInstr "Hma_code".
    iInstr "Hma_code".


    iInstr "Htc_code". (* Mov r_t1 PC *)
      admit.
  Admitted.

End mutual_attest_example.
