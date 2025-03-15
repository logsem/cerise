From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules seal_store.
From cap_machine Require Import logrel fundamental.
From cap_machine Require Import logrel.
From cap_machine Require Import proofmode.
(* From cap_machine Require Import macros_new. *)
(* Open Scope Z_scope. *)

Ltac iHide0 irisH coqH :=
  let coqH := fresh coqH in
  match goal with
  | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
      set (coqH := prop)
  end.

Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
  iHide0 irisH coqH.

Lemma finz_dist_add
  {finz_bound : Z} (f1 : finz finz_bound) (n : nat) :
  is_Some (f1 + n)%f → finz.dist f1 (f1 ^+ n)%f = n.
Proof.
  generalize dependent f1.
  induction n; intros f1 [f1' Hf1'].
  - apply finz_dist_0; solve_finz.
  - rewrite finz_dist_S; last solve_finz.
    f_equal.
    replace (f1 ^+ S n)%f with ((f1 ^+ 1) ^+n)%f by solve_finz.
    rewrite IHn; solve_finz.
Qed.

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

      UnSeal r_t1 r_t2 r_t1;      (* r1 := unsealed( {(RO,a, _, 42)}_signed_A ) *)
      (* if (unsealed( {42}_signed_A ) != 42)
         then Fail
         else continue
       *)
      (* TODO remove the NOP thanks to later credit? *)
      Mov r_t0 r_t0; (* NOP instruction for getting rid off the later *)

      GetB r_t2 r_t1;             (* r2 := a *)
      Mod r_t2 r_t2 2;            (* r2 := a%2 *)
      (* if a%2 != 0 then Fail else continue *)
      Mov r_t5 PC;
      Lea r_t5 5;
      Jnz r_t5 r_t2;
      Lea r_t5 1;
      Jmp r_t5;
      Fail;

      GetA r_t1 r_t1; (* r1 := ?42 *)
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
      Sub r_t1 r_t2 r_t1;
      Lea r_t5 r_t1;
      Load r_t1 r_t5;       (* r1 := (RW, data_b, data_e, data_a) *)

      (* fetch sign_key *)
      GetA r_t2 r_t1;
      GetB r_t3 r_t1;      (* r3 := data_b *)
      Sub r_t2 r_t3 r_t2;
      Lea r_t1 r_t2;       (* r1 := (RW, data_b, data_e, data_b) *)
      Load r_t6 r_t1;      (* r6 := [SU, σ, σ+2, σ] *)


      Mov r_t4 r_t1;      (* r4 := (RW, data_b, data_e, data_b) *)
      GetB r_t2 r_t1;     (* r2 := data_b *)
      Add r_t3 r_t2 1;    (* r3 := data_b + 1 *)
      Subseg r_t1 r_t2 r_t3; (* r1 := (RW, data_b, data_b+1, data_b) *)
      Add r_t5 r_t3 1;    (* r5 := data_b + 2 *)
      Subseg r_t4 r_t3 r_t5 (* r4 := (RW, data_b+1, data_b+2, data_b) *)
      ] ++ encodeInstrsLW [
        (* if x%2 = 0 then mb=[42;1] else  mb=[1;42] *)
        Mod r_t3 r_t2 2;
        Mov r_t5 PC;
        Lea r_t5 9;
        Jnz r_t5 r_t3;

        (* case x%2 == 0 *)
        Sub r_t3 43 r_t2;
        Lea r_t1 r_t3; (*  r1 :=  (RW, data_b, data_b+1, 42) *)
        Sub r_t3 1 r_t2;
        Lea r_t4 r_t3; (*  r4 :=  (RW, data_b+1, data_b+2, 1) *)
        Lea r_t5 4;
        Jmp r_t5;

        (* case x%2 == 1 *)
        Sub r_t3 1 r_t2;
        Lea r_t1 r_t3; (*  r1 :=  (RW, data_b, data_b+1, 1) *)
        Sub r_t3 43 r_t2;
        Lea r_t4 r_t3 (*  r4 :=  (RW, data_b+1, data_b+2, 42) *)
      ] ++ encodeInstrsLW [
      (* continue here  *)
      Restrict r_t1 (encodePerm O);
      Restrict r_t4 (encodePerm O);

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
  Program Definition f42 : Addr := (finz.FinZ 42 eq_refl eq_refl).
  Program Definition f1 : Addr := (finz.FinZ 1 eq_refl eq_refl).
  Definition prot_sealed_A (a : Addr) : Addr :=
    if (decide (a `mod` 2%nat = 0 )%Z) then f42 else f1.

  Definition sealed_enclaveA : LWord → iProp Σ :=
    λ w, (∃ (b e : Addr) v,
             ⌜ w = LCap O b e (prot_sealed_A b) v ⌝)%I.
  Definition sealed_enclaveA_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveA w%I.

  Instance sealed_enclaveA_persistent (w : LWord) : Persistent (sealed_enclaveA w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveA (τ : OType) := seal_pred τ sealed_enclaveA.
  Definition valid_sealed_enclaveA_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveA.
  Lemma sealed_enclaveA_interp (lw : LWord) : sealed_enclaveA lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
  Qed.


  (* Sealed predicate for enclave B *)
  Program Definition f43 : Addr := (finz.FinZ 43 eq_refl eq_refl).
  Definition prot_sealed_B (a : Addr) : Addr :=
    if (decide (a `mod` 2%nat = 0 )%Z) then f43 else f1.

  Definition sealed_enclaveB : LWord → iProp Σ :=
    λ w, (∃ (b e : Addr) v,
             ⌜ w = LCap O b e (prot_sealed_B b) v ⌝)%I.
  Definition sealed_enclaveB_ne : (leibnizO LWord) -n> (iPropO Σ) :=
      λne (w : leibnizO LWord), sealed_enclaveB w%I.

  Instance sealed_enclaveB_persistent (w : LWord) : Persistent (sealed_enclaveB w).
  Proof. apply _. Qed.

  Definition seal_pred_enclaveB (τ : OType) := seal_pred τ sealed_enclaveB.
  Definition valid_sealed_enclaveB_cap (w : LWord) (τ : OType) := valid_sealed w τ sealed_enclaveB.
  Lemma sealed_enclaveB_interp (lw : LWord) : sealed_enclaveB lw -∗ fixpoint interp1 lw.
  Proof.
    iIntros "Hsealed".
    iDestruct "Hsealed" as (b e v) "->".
    by rewrite fixpoint_interp1_eq /=.
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

  Axiom hash_concat_app : forall {A : Type} (la la' : list A),
    hash (la++la') = hash_concat (hash la) (hash la').
  Axiom hash_concat_assoc : Assoc eq hash_concat.
  Global Instance hash_concat_Assoc : Assoc eq hash_concat := hash_concat_assoc.


  (* -------------------------------------------------- *)
  (* ------------------ ENCLAVE A---------------------- *)
  (* -------------------------------------------------- *)

  Lemma mutual_attest_A_contract
    v b' e' a' v'
    enclave_data ot :
    let e := (length mutual_attest_enclave_A_code + 1)%Z in
    (ot + 2)%f = Some (ot ^+ 2)%f ->
    (b' < e')%a ->
    (ma_addr_A + e)%a =
    Some (ma_addr_A ^+ e)%a ->
    custom_enclave_inv ma_enclaves_map
    ∗ na_inv logrel_nais (custom_enclaveN.@hash_mutual_attest_A)
        ([[ma_addr_A,(ma_addr_A ^+ e)%a]]↦ₐ{v}
           [[LCap RW b' e' a' v' :: mutual_attest_enclave_A_code]]
         ∗ [[b',e']]↦ₐ{v'}[[LSealRange (true, true) ot (ot ^+ 2)%f ot :: enclave_data]])
    ∗ seal_pred (ot ^+ 1)%f sealed_enclaveA
      -∗ interp (LCap E ma_addr_A
                   (ma_addr_A ^+ e)%a
                   (ma_addr_A ^+ 1)%a v).
  Proof.
    intro e ; subst e.
    iIntros (Hot Hb' He) "#(Henclaves_inv & Hma_inv & HPsign)".
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext ; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    remember ma_addr_A as pc_b in |- * at 7.
    (* remember (ma_addr_A ^+ (91%nat + 1))%a as pc_e in |- * at 4. *)
    (* assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (91%nat + 1))%a) by (subst; solve_addr). *)
  Admitted.


  (* -------------------------------------------------- *)
  (* ------------------ ENCLAVE B---------------------- *)
  (* -------------------------------------------------- *)


  Lemma enclave_B_mod_encoding_spec
    pc_b pc_e pc_a pc_v
    b' v' φ
    :

    let code :=
     (encodeInstrsLW
                    [Mod r_t3 r_t2 2; Mov r_t5 PC; Lea r_t5 9; Jnz r_t5 r_t3;
                     Sub r_t3 43 r_t2; Lea r_t1 r_t3; Sub r_t3 1 r_t2;
                     Lea r_t4 r_t3; Lea r_t5 4; Jmp r_t5; Sub r_t3 1 r_t2;
                     Lea r_t1 r_t3; Sub r_t3 43 r_t2; Lea r_t4 r_t3])
    in

    ContiguousRegion pc_a (length code) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    (b' + 2)%a = Some (b' ^+ 2)%a ->

   (PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v)
   ∗ codefrag pc_a pc_v code
   ∗ r_t1 ↦ᵣ LCap RW b' (b' ^+ 1)%a b' v'
   ∗ r_t2 ↦ᵣ LInt b'
   ∗ r_t3 ↦ᵣ LInt (b' + 1%nat)%Z
   ∗ r_t4 ↦ᵣ LCap RW (b' ^+ 1)%a (b' ^+ 2)%a b' v'
   ∗ r_t5 ↦ᵣ LInt (b' + 1%nat + 1%nat)%Z

   ∗ ▷ ( (PC ↦ᵣ LCap RX pc_b pc_e (pc_a ^+ length code)%a pc_v
          ∗ codefrag pc_a pc_v code
          ∗ r_t1 ↦ᵣ LCap RW b' (b' ^+ 1)%a (prot_sealed_B b') v'
          ∗ r_t2 ↦ᵣ LInt b'
          ∗ (∃w3, r_t3 ↦ᵣ w3)
          ∗ r_t4 ↦ᵣ LCap RW (b' ^+ 1)%a (b' ^+ 2)%a (prot_sealed_B (b' ^+ 1)%a) v'
          ∗ (∃w5, r_t5 ↦ᵣ w5)
         -∗ WP Seq (Instr Executable) {{ v, φ v }}
       )
   )
   ⊢ WP Seq (Instr Executable) {{ v, φ v }}.
  Proof.
    intros code Hcont Hbounds Hb'2.
    iIntros "(HPC & Hcode & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hφ)".
    (* Mod r_t3 r_t2 2 *)
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hr2 $Hr3 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hi & Hr2 & Hr3)".
    iEval (cbn) in "Hr3".
    wp_pure; iInstr_close "Hcode".
    (* Mov r_t5 PC *)
    iInstr "Hcode".
    (* Lea r_t5 8 *)
    iInstr "Hcode".

    destruct (decide ((b' `mod` 2%nat)%Z = 0)) as [Hmod | Hmod].
    - (* Jnz r_t5 r_t3 *)
      rewrite Hmod.
      iInstr "Hcode".
      (* case x%2 == 0 *)
      (* Sub r_t3 43 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f43 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Sub r_t3 1 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t4 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f1 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Lea r_t5 4 *)
      iInstr "Hcode".
      (* Jmp r_t5 *)
      iInstr "Hcode".
      iApply "Hφ"; iFrame.
      rewrite /prot_sealed_B.
      cbn.
      rewrite Hmod.
      destruct (decide (((Z.of_nat 0%nat = 0%Z))%Z)); last lia.
      iFrame "Hr1".
      destruct (decide (((b' ^+ 1)%a `mod` 2%nat)%Z = 0%Z)); last iFrame.
      { exfalso.
        rewrite Zmod_even in Hmod.
        rewrite Zmod_odd in e0.
        destruct (Z.even b') eqn:Hb'; try done.
        destruct (Z.odd (b' ^+ 1)%a) eqn:Hb''; try done.
        rewrite -Z.odd_succ in Hb'.
        assert ( (Z.succ b')%a = (z_of (b' ^+ 1)%a)) by solve_addr.
        solve_addr.
      }
      iSplitL "Hr3" ; iExists _ ; iFrame.
    - (* Jnz r_t5 r_t3 *)
      iInstr "Hcode".
      { by intro Hcontra ; inv Hcontra. }
      (* case x%2 == 1 *)
      (* (Sub r_t3 1 r_t2) *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f1 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Sub r_t3 1 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t4 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f43 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      iApply "Hφ"; iFrame.
      rewrite /prot_sealed_B.
      assert ((b' `mod` 2%nat)%Z = 1) as Hmod'.
      { rewrite Zmod_even in Hmod.
        rewrite Zmod_even.
        destruct (Z.even b') eqn:Hb'; try done.
      }
      cbn.
      rewrite Hmod'.
      destruct (decide (((Z.of_nat 1%nat = 0%Z))%Z)); first lia.
      iFrame "Hr1".
      destruct (decide (((b' ^+ 1)%a `mod` 2%nat)%Z = 0%Z)); first iFrame.
      { iSplitL "Hr3" ; (iExists _ ; iFrame). }
      { exfalso.
        rewrite Zmod_even in Hmod.
        rewrite Zmod_odd in n0.
        destruct (Z.even b') eqn:Hb'; try done.
        destruct (Z.odd (b' ^+ 1)%a) eqn:Hb''; try done.
        rewrite -Z.odd_succ in Hb'.
        assert ( (Z.succ b')%a = (z_of (b' ^+ 1)%a)) by solve_addr.
        solve_addr.
      }
  Qed.



  Lemma mutual_attest_B_contract
    v b' e' a' v'
    enclave_data ot :
    let e := (length mutual_attest_enclave_B_code + 1)%Z in
    (ot + 2)%f = Some (ot ^+ 2)%f ->
    (b' < e')%a ->
    (ma_addr_B + e)%a =
    Some (ma_addr_B ^+ e)%a ->
    custom_enclave_inv ma_enclaves_map
    ∗ na_inv logrel_nais (custom_enclaveN.@hash_mutual_attest_B)
      ([[ma_addr_B,(ma_addr_B ^+ e)%a]]↦ₐ{v}
         [[LCap RW b' e' a' v' :: mutual_attest_enclave_B_code]]
       ∗ [[b',e']]↦ₐ{v'}[[LSealRange (true, true) ot (ot ^+ 2)%f ot :: enclave_data]])
    ∗ seal_pred (ot ^+ 1)%f sealed_enclaveB
    -∗ interp (LCap E ma_addr_B
                 (ma_addr_B ^+ e)%a
                 (ma_addr_B ^+ 1)%a v).
  Proof.
    intro e ; subst e.
    iIntros (Hot Hb' He) "#(Henclaves_inv & Hma_inv & HPsign)".
    rewrite fixpoint_interp1_eq /=.
    iIntros (lregs); iNext ; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".
    rewrite /interp_conf.
    iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    remember ma_addr_B as pc_b in |- * at 7.
    remember (ma_addr_B ^+ (91%nat + 1))%a as pc_e in |- * at 4.
    assert (SubBounds pc_b pc_e ma_addr_B (ma_addr_B ^+ (91%nat + 1))%a) by (subst; solve_addr).

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
    iAssert (interp w0) as "Hinterp_w0".
    { iApply "Hinterp_map";eauto;done. }
    (* Safe to jump to safe value *)
    iDestruct (jmp_to_unknown with "Hinterp_w0") as "Hjmp"; eauto.


    (* Code memory *)
    iDestruct (region_mapsto_cons with "Hma_code") as "[Hma_addr_B Hma_code]"; last iFrame.
    { transitivity (Some (ma_addr_B ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }
    rewrite /mutual_attest_enclave_B_code.

    iDestruct (region_mapsto_split _ _ (ma_addr_B ^+ (89%nat + 1))%a with "Hma_code") as "[Hma_code HidT]"; last iFrame.
    { solve_addr. }
    { cbn.
      replace (ma_addr_B ^+ (89%nat + 1))%a
        with ((ma_addr_B ^+ 1)%a ^+ 89%nat)%a by solve_addr.
      rewrite finz_dist_add; solve_addr.
    }
    rewrite /mutual_attest_eid_table.
    iDestruct (region_mapsto_cons with "HidT") as "[HidTA HidTB]".
    { transitivity (Some (ma_addr_B ^+ (89%nat + 2))%a); auto ; try solve_addr. }
    { solve_addr. }

    iAssert (codefrag (ma_addr_B ^+ 1)%a v mutual_attest_enclave_B_code_pre)
      with "[Hma_code]" as "Hma_code".
    {
      rewrite /codefrag /=.
      by replace ((ma_addr_B ^+ 1) ^+ 89%nat)%a with (ma_addr_B ^+ 90%nat)%a by solve_addr.
    }
    codefrag_facts "Hma_code".

    (* Data memory *)
    iDestruct (region_mapsto_cons with "Hma_data") as "[Hma_keys Hma_data]"; last iFrame.
    { transitivity (Some (b' ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }


    focus_block_0 "Hma_code" as "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.
    set (hma_code := encodeInstrsLW _).

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
    replace (pc_e ^+ -2)%a  with (ma_addr_B ^+ (89%nat + 1))%a by (subst;solve_addr).
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
      all: replace (-1 + 1%nat)%Z with 0%Z by lia.
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
    assert (Ho : LInt (o + 1) ≠ LInt 0%Z) by (clear ; intro ; inversion H ; solve_finz).
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
    replace ( _ - _)%Z with 0%Z by lia.
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
    Opaque mutual_attest_enclave_B_code_pre encodeInstrsLW.
    incrementLPC_inv as (p''&b_main'&e_main'&a_main'&pc_v'& ? & HPC & Z & Hregs');
      simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    Transparent mutual_attest_enclave_B_code_pre encodeInstrsLW.
    replace x with ((ma_addr_B ^+ 1) ^+ 29)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hma_code".

    iAssert (
        if Z.even a
        then seal_pred a (Penc mutual_attest_enclave_A_pred)
             ∗ seal_pred (a ^+ 1)%f (Psign mutual_attest_enclave_A_pred)
        else seal_pred (a ^+ -1)%f (Penc mutual_attest_enclave_A_pred)
             ∗ seal_pred a (Psign mutual_attest_enclave_A_pred)
      )%I as "Hma_A".
    {
      iApply "Hcemap"; iFrame "%#∗".
      + iPureIntro. admit.
      + iPureIntro; apply wf_ma_enclaves_map.
      + iPureIntro; by rewrite /ma_enclaves_map; simplify_map_eq.
    }

    destruct (Z.even (finz.to_z a)) eqn:HEven_a
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
    iAssert (▷ sealed_enclaveA (LWSealable sb))%I as (fb fe fv) ">%Hseal_A".
    { iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      iRewrite "Heqv".
      iFrame "HΦ". }
    destruct sb ; simplify_eq.
    iClear "Heqv Hma_A_Penc Hcemap Henclaves_inv".

    (* Mov r_t0 r_t0  *)
    iInstr "Hma_code".

    (* GetB r_t2 r_t1 *)
    iInstr "Hma_code".
    (* Mod r_t2 r_t2 2 *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hr2 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hi & Hr2)".
    iEval (cbn) in "Hr2".
    wp_pure; iInstr_close "Hma_code".

    (* Mov r_t5 PC *)
    iInstr "Hma_code".
    (* Lea r_t5 5 *)
    iInstr "Hma_code".
    rewrite /prot_sealed_A.
    destruct (decide ((fb `mod` 2%nat)%Z = 0%Z)) as [-> | Hfb]; cycle 1.
    {
      (* Jnz r_t5 r_t2 *)
      iInstr "Hma_code".
      by intro Hcontra; inv Hcontra.
      (* Fail *)
      iInstr "Hma_code".
      wp_end ; by iIntros (?).
    }
    (* Jnz r_t5 r_t2 *)
    iInstr "Hma_code".
    (* Lea r_t5 1 *)
    iInstr "Hma_code".
    (* Jmp r_t5 *)
    iInstr "Hma_code".

    (* GetA r_t1 r_t1 *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_Get_same_success with "[$HPC $Hr1 $Hi]"); try solve_pure.
    iNext. iIntros "(HPC & Hi & Hr1)".
    iEval (rewrite /prot_sealed_A) in "Hr1".
    wp_pure; iInstr_close "Hma_code".
    (* Sub r_t1 r_t1 42 *)
    iInstr "Hma_code".
    replace (f42 - 42%nat)%Z with 0%Z by (clear; solve_addr).
    (* Lea r_t5 6 *)
    iInstr "Hma_code".
    (* Jnz r_t5 r_t2 *)
    iInstr "Hma_code".

    (* Lea r_t5 1 *)
    iInstr "Hma_code".
    (* Jmp r_t5 *)
    iInstr "Hma_code".

    (* GetA r_t1 r_t5 *)
    iInstr "Hma_code".
    (* GetB r_t2 r_t5 *)
    iInstr "Hma_code".
    (* Sub r_t1 r_t1 r_t2 *)
    iInstr "Hma_code".
    (* Lea r_t5 r_t1 *)
    assert (
        (((ma_addr_B ^+ 1) ^+ 45)%a + (ma_addr_B - ((ma_addr_B ^+ 1) ^+ 45)%a))%a
        = Some (ma_addr_B)) by solve_addr+He.
    iInstr "Hma_code".
    (* Load r_t1 r_t5 *)
    iInstr "Hma_code".
    { split; solve_pure. }

    (* GetA r_t2 r_t1 *)
    iInstr "Hma_code".
    (* GetB r_t3 r_t1 *)
    iInstr "Hma_code".
    (* Sub r_t2 r_t2 r_t3 *)
    iInstr "Hma_code".
    (* Lea r_t1 r_t2 *)
    iInstr "Hma_code".
    { transitivity (Some b'); solve_addr. }
    (* Load r_t6 r_t1 *)
    iInstr "Hma_code".
    { split; try solve_pure; solve_addr. }

    (* Mov r_t4 r_t1 *)
    iInstr "Hma_code".
    (* GetB r_t2 r_t1 *)
    iInstr "Hma_code".
    (* Add r_t3 r_t2 1 *)
    iInstr "Hma_code".
    (* Subseg r_t1 r_t2 r_t3 *)
    iInstr "Hma_code".
    { transitivity (Some (b' ^+ 1))%a; solve_addr. }
    { solve_addr. }
    (* Add r_t5 r_t3 1 *)
    iInstr "Hma_code".
    (* Subseg r_t4 r_t3 r_t5 *)
    destruct ((b' + 2)%a) as [| b'2] eqn:Hb'2; cycle 1.
    {
      wp_instr.
      iInstr_lookup "Hma_code" as "Hi" "Hma_code".
      iDestruct (map_of_regs_4 with "HPC Hr3 Hr4 Hr5") as "[Hmap _]".
      iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
      { solve_pure. }
      { by unfold regs_of; rewrite !dom_insert; set_solver+. }
      iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr3' Hr4' Hbounds' Hregs'
                        | ? ? ? ? ? ? Hdst HpE Hr3' Hr4' Hbounds' Hregs'
                        | ]; cycle 1.
      - simplify_map_eq.
      - cbn. wp_pure; wp_end ; by iIntros (?).
      - exfalso.
        simplify_map_eq.
        rewrite /addr_of_argumentL /=
          lookup_insert_ne //
          lookup_insert_ne //
          lookup_insert_ne //
          lookup_insert /=
          in Hr4'.
        solve_addr + Hr4' Hb'2.
    }
    assert (f = (b' ^+ 2)%a) by solve_addr ; subst.
    destruct (decide ((b' ^+ 2)%a <= e')%a) as [Hb2e'|Hb2e']; cycle 1.
    {
      wp_instr.
      iInstr_lookup "Hma_code" as "Hi" "Hma_code".
      iDestruct (map_of_regs_4 with "HPC Hr3 Hr4 Hr5") as "[Hmap _]".
      iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
      { solve_pure. }
      { by unfold regs_of; rewrite !dom_insert; set_solver+. }
      iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr3' Hr4' Hbounds' Hregs'
                        | ? ? ? ? ? ? Hdst HpE Hr3' Hr4' Hbounds' Hregs'
                        | ]; cycle 1.
      - simplify_map_eq.
      - cbn. wp_pure; wp_end ; by iIntros (?).
      - exfalso.
        simplify_map_eq.
        rewrite /addr_of_argumentL /=
          lookup_insert_ne //
          lookup_insert_ne //
          lookup_insert_ne //
          lookup_insert /=
          in Hr4'.
        clear - Hr4' Hb2e' Hbounds'.
        apply isWithin_implies in Hbounds'.
        assert ((a0 ^+ 2)%a = a2) as <- by solve_addr.
        destruct Hbounds' as [ _ Hbounds' ].
        solve_addr + Hb2e' Hbounds'.
    }
    iInstr "Hma_code".
    { transitivity (Some (b' ^+ 1))%a; solve_addr. }
    { transitivity (Some (b' ^+ 2))%a; solve_addr. }
    { solve_addr. }

    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code hma_code.

    focus_block 1 "Hma_code" as a_Mod Ha_Mod "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.

    iApply ( enclave_B_mod_encoding_spec with "[- $HPC $Hma_code $Hr1 $Hr2 $Hr3 $Hr4 $Hr5]" ); eauto.
    iNext; iIntros "(HPC & Hma_code & Hr1 & Hr2 & Hr3 & Hr4 & Hr5)".
    iDestruct "Hr3" as (w3') "Hr3".
    iDestruct "Hr5" as (w5') "Hr5".

    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code.

    focus_block 2 "Hma_code" as a_block2 Ha_blobk2 "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.
    (* Restrict r_t1 (encodePerm O) *)
    iInstr "Hma_code".
    { rewrite decode_encode_perm_inv; solve_pure. }
    (* Restrict r_t4 (encodePerm O) *)
    iInstr "Hma_code".
    { rewrite decode_encode_perm_inv; solve_pure. }
    rewrite !decode_encode_perm_inv.

    (* Lea r_t6 1 *)
    iInstr "Hma_code".
    { transitivity (Some (ot ^+ 1)%ot); solve_addr. }
    (* Seal r_t1 r_t6 r_t1 *)
    iInstr "Hma_code".
    { done. }
    { solve_addr. }
    (* Seal r_t2 r_t6 r_t4 *)
    iInstr "Hma_code".
    { done. }
    { solve_addr. }

    (* GetA r_t3 r_t6 *)
    iInstr "Hma_code".
    (* Add r_t4 r_t3 1 *)
    iInstr "Hma_code".
    (* Subseg r_t6 r_t3 r_t4 *)
    iInstr "Hma_code".
    { transitivity (Some ( ((ot ^+ 2)%ot ))); solve_addr. }
    { solve_addr. }
    (* Restrict r_t6 (encodeSealPerms (false,true)) *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_restrict_success_z_sr with "[$Hi $HPC $Hr6]"); try solve_pure.
    { by rewrite decode_encode_seal_perms_inv; cbn. }
    iNext; iIntros "(HPC & Hi & Hr6)".
    iEval (rewrite decode_encode_seal_perms_inv /=) in "Hr6".
    wp_pure; iInstr_close "Hma_code".

    (*   Mov r_t3 r_t6; *)
    iInstr "Hma_code".
    (*   Mov r_t4 0; *)
    iInstr "Hma_code".
    (*   Mov r_t5 0; *)
    iInstr "Hma_code".
    (*   Mov r_t6 0; *)
    iInstr "Hma_code".

    (*   Jmp r_t0 *)
    iInstr "Hma_code".

    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code.

    iAssert (
        interp (LSealedCap (ot ^+ 1)%f O b' (b' ^+ 1)%a (prot_sealed_B b') v')
      ) as "Hinterp_sealed_b'".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_enclaveB; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_enclaveB_persistent. }
      { iNext; by iExists _,_,_. }
    }
    iAssert (
        interp (LSealedCap (ot ^+ 1)%f O (b' ^+ 1)%a (b' ^+ 2)%a (prot_sealed_B (b' ^+ 1)%a) v')
      ) as "Hinterp_sealed_b1'".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_enclaveB; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_enclaveB_persistent. }
      { iNext; by iExists _,_,_. }
    }
    iAssert (
        interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f)
      ) as "Hinterp_sealr_ot".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /safe_to_unseal).
      iSplit ; first done.
      rewrite finz_seq_between_singleton ; last solve_finz.
      iSplit ; last done.
      iExists sealed_enclaveB_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply sealed_enclaveB_interp.
    }

    (* Close the opened invariant *)
    iDestruct (region_mapsto_cons with "[Hma_addr_B Hma_code]") as "Hma_code"
    ; try iFrame.
    { solve_addr. }
    { solve_addr. }
    rewrite -/mutual_attest_eid_table.
    iDestruct (region_mapsto_split
                 ma_addr_B
                 (ma_addr_B ^+ (91%nat + 1))%a
                 ((ma_addr_B ^+ 1) ^+ 89%nat)%a
                with "[$Hma_code HidT]") as "Hma_code"; last iFrame.
    { solve_addr. }
    { cbn.
      rewrite finz_dist_S; last solve_addr.
      f_equal.
      rewrite finz_dist_add; solve_addr.
    }
    { replace (ma_addr_B ^+ (89%nat + 1))%a with
        ((ma_addr_B ^+ 1) ^+ 89%nat)%a by solve_addr.
      iFrame. }
    iDestruct (region_mapsto_cons with "[$Hma_keys $Hma_data]") as "Hma_data" ; last iFrame.
    { solve_addr. }
    { solve_addr. }
    iMod ("Hclose" with "[$Hna $Hma_code $Hma_data]") as "Hna".

    (* Wrap up the registers *)
    Opaque mutual_attest_enclave_B_code_pre encodeInstrsLW.
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
    { do 6 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 6 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    { do 5 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 5 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
    { do 4 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 4 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hrmap $Hr3]") as "Hrmap".
    { do 3 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 3 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t4 with "[$Hrmap $Hr4]") as "Hrmap".
    { do 2 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 2 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hrmap $Hr5]") as "Hrmap".
    { do 1 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 1 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hrmap $Hr6]") as "Hrmap".
    { do 0 ( rewrite lookup_delete_ne //) ; by rewrite lookup_delete. }
    do 0 (rewrite -delete_insert_ne //=); rewrite insert_delete_insert.
    set (rmap' := (<[r_t6:=LInt 0%nat]> _)).
    iAssert ([∗ map] k↦y ∈ rmap', k ↦ᵣ y ∗ interp y)%I with "[Hrmap]" as "Hrmap".
    {
      subst rmap'.
      iApply (big_sepM_sep_2 with "[Hrmap]") ; first done.
      iApply big_sepM_insert_2; first (iApply interp_int).
      iApply big_sepM_insert_2; first (iApply interp_int).
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
    - iApply ( mutual_attest_A_contract with "[]") ; last iFrame "#"; eauto.
    - rewrite lookup_insert_ne // in Hcode_ce.
      2:{ rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
          intro Hcontra.
          apply hash_concat_inj' in Hcontra.
          destruct Hcontra as [_ Hcontra].
          rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra.
          by injection Hcontra.
      }
      simplify_map_eq.
      iApply ( mutual_attest_B_contract with "[]") ; last iFrame "#"; eauto.
  Admitted.

End mutual_attest_example.
