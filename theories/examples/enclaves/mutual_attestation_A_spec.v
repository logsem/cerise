From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel fundamental.
From cap_machine Require Import proofmode.
From cap_machine Require Import mutual_attestation_code.

Section mutual_attest_A.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg : sealStoreG Σ}
    {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.
  Context {MA: MutualAttestation}.

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.

  Lemma enclave_A_mod_encoding_42_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (b' e' : Addr) (v' : Version)
    (w2 w3 w4 w5 : LWord)
    :
    let φ :=
      (λ v,
        ⌜v = HaltedV⌝
        → ∃ lregs : LReg,
            full_map lregs ∧ ([∗ map] r↦lw ∈ lregs, r ↦ᵣ lw) ∗ na_own logrel_nais ⊤)%I
    in
    let code := mutual_attest_enclave_A_mod_encoding_42 in
    let lword42_b' :=
      if (decide (b' `mod` 2 = 0)%Z) then b' else (b' ^+ 1)%a
    in
    let lword42_e' :=
      if (decide (b' `mod` 2 = 0)%Z) then (b' ^+ 1)%a else (b' ^+ 2)%a
    in
    let lword42_a' :=
      prot_sealed_A
        ( if decide ((b' `mod` 2)%Z = 0%Z)
          then b'
          else (b' ^+ 1)%a
        )
    in
    let lword42 : LWord :=
      (LCap O lword42_b' lword42_e' lword42_a' v')
    in

    ContiguousRegion pc_a (length code) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->

   (PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v)
   ∗ codefrag pc_a pc_v code
   ∗ r_t1 ↦ᵣ LCap RW b' e' b' v'
   ∗ r_t2 ↦ᵣ w2
   ∗ r_t3 ↦ᵣ w3
   ∗ r_t4 ↦ᵣ w4
   ∗ r_t5 ↦ᵣ w5

   ∗ ▷ ( (PC ↦ᵣ LCap RX pc_b pc_e (pc_a ^+ length code)%a pc_v
          ∗ codefrag pc_a pc_v code
          ∗ r_t1 ↦ᵣ lword42
          ∗ (∃w2, r_t2 ↦ᵣ w2)
          ∗ (∃w3, r_t3 ↦ᵣ w3)
          ∗ (∃w4, r_t4 ↦ᵣ w4)
          ∗ (∃w5, r_t5 ↦ᵣ w5)
         -∗ WP Seq (Instr Executable) {{ v, φ v }}
       )
   )
   ⊢ WP Seq (Instr Executable) {{ v, φ v }}.
  Proof.
    intros φ code lword42_b' lword42_e' lword42_a' lword42 Hcont Hbounds.
    iIntros "(HPC & Hcode & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hφ)".
    (* GetB r_t2 r_t1 *)
    iInstr "Hcode".
    (* Add r_t3 r_t2 1 *)
    iInstr "Hcode".
    (* Mod r_t4 r_t2 2 *)
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hr2 $Hr4 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hi & Hr2 & Hr4)".
    iEval (cbn) in "Hr4".
    wp_pure; iInstr_close "Hcode".

    (* Mov r_t5 PC *)
    iInstr "Hcode".
    (* Lea r_t5 6 *)
    iInstr "Hcode".

    destruct (decide ((b' `mod` 2%nat)%Z = 0)) as [Hmod | Hmod].
    - (* Jnz r_t5 r_t3 *)
      rewrite Hmod.
      iInstr "Hcode".

      (* Subseg r_t1 r_t2 r_t3 *)
      destruct ((b' + 1)%a) as [b1'|] eqn:Hb'1; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap _]".
        iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
        { solve_pure. }
        { by unfold regs_of; rewrite !dom_insert; set_solver+. }
        iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
        destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr2' Hr3' Hbounds' Hregs'
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
            in Hr3'.
          solve_addr + Hr3' Hb'1.
      }
      assert (b1' = (b' ^+ 1)%a) by solve_addr ; subst.
      destruct (decide ((b' ^+ 1)%a <= e')%a) as [Hb1e'|Hb1e']; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap _]".
        iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
        { solve_pure. }
        { by unfold regs_of; rewrite !dom_insert; set_solver+. }
        iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
        destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr2' Hr3' Hbounds' Hregs'
                          | ? ? ? ? ? ? Hdst HpE Hr2' Hr3' Hbounds' Hregs'
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
            in Hr3'.
          clear - Hr3' Hb1e' Hbounds'.
          apply isWithin_implies in Hbounds'.
          assert ((a ^+ 1)%a = a2) as <- by solve_addr.
          destruct Hbounds' as [ _ Hbounds' ].
          solve_addr + Hb1e' Hbounds'.
      }
      iInstr "Hcode".
      { transitivity (Some (b' ^+ 1))%a; solve_addr. }
      { solve_addr. }

      (* Lea r_t5 2 *)
      iInstr "Hcode".
      (* Jmp r_t5 *)
      iInstr "Hcode".
      (* Sub r_t3 42 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f42 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Restrict r_t1 (encodePerm O) *)
      iInstr "Hcode".
      { rewrite decode_encode_perm_inv ; done. }
      rewrite decode_encode_perm_inv.

      (* Continuation *)
      iApply "Hφ"; iFrame.
      iSplitL "Hr1".
      + rewrite /lword42 /lword42_b' /lword42_e' /lword42_a' /prot_sealed_A.
        rewrite !Hmod.
        by destruct (decide (((Z.of_nat 0%nat = 0%Z))%Z)); last lia.
      + iSplitL "Hr2" ; first (iExists _; iFrame).
        iSplitL "Hr3" ; first (iExists _; iFrame).
        iSplitL "Hr4" ; (iExists _; iFrame).
    - (* Jnz r_t5 r_t3 *)
      iInstr "Hcode".
      { intros Hcontra ; inv Hcontra; done. }

      (* Add r_t4 r_t3 1 *)
      iInstr "Hcode".
      (* Subseg r_t1 r_t3 r_t4 *)
      destruct ((b' + 2)%a) as [b2'|] eqn:Hb'2; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr3 Hr4") as "[Hmap _]".
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
      assert (b2' = (b' ^+ 2)%a) by solve_addr ; subst.
      destruct (decide ((b' ^+ 2)%a <= e')%a) as [Hb2e'|Hb2e']; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr3 Hr4") as "[Hmap _]".
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
          assert ((a ^+ 2)%a = a2) as <- by solve_addr.
          destruct Hbounds' as [ _ Hbounds' ].
          solve_addr + Hb2e' Hbounds'.
      }
      iInstr "Hcode".
      { transitivity (Some (b' ^+ 1))%a; solve_addr. }
      { transitivity (Some (b' ^+ 2))%a; solve_addr. }
      { solve_addr. }

      (* Sub r_t3 42 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f42 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Restrict r_t1 (encodePerm O) *)
      iInstr "Hcode".
      { rewrite decode_encode_perm_inv ; done. }
      rewrite decode_encode_perm_inv.

      (* Continuation *)
      iApply "Hφ"; iFrame.
      iSplitL "Hr1".
      + rewrite /lword42 /lword42_b' /lword42_e' /lword42_a' /prot_sealed_A.
        destruct (decide ((((b' `mod` 2)%Z = 0%Z))%Z)); first lia.
        assert ((b' `mod` 2%nat)%Z = 1) as Hmod'.
        { rewrite Zmod_even in Hmod.
          rewrite Zmod_even.
          destruct (Z.even b') eqn:Hb'; try done.
        }
        destruct (decide (((((b' ^+ 1)%a `mod` 2%nat)%Z = 0%Z))%Z)); first iFrame.
        { exfalso.
          rewrite Zmod_even in Hmod.
          rewrite Zmod_odd in n0.
          destruct (Z.even b') eqn:Hb'; try done.
          destruct (Z.odd (b' ^+ 1)%a) eqn:Hb''; try done.
          rewrite -Z.odd_succ in Hb'.
          assert ( (Z.succ b')%a = (z_of (b' ^+ 1)%a)) by solve_addr.
          solve_addr.
        }

      + iSplitL "Hr2" ; first (iExists _; iFrame).
        iSplitL "Hr3" ; first (iExists _; iFrame).
        iSplitL "Hr4" ; (iExists _; iFrame).
  Qed.



  Lemma enclave_A_mod_encoding_1_spec
    (pc_b pc_e pc_a : Addr) (pc_v : Version)
    (b' e' : Addr) (v' : Version)
    (w2 w3 w4 w5 : LWord)
    :
    let φ :=
      (λ v,
        ⌜v = HaltedV⌝
        → ∃ lregs : LReg,
            full_map lregs ∧ ([∗ map] r↦lw ∈ lregs, r ↦ᵣ lw) ∗ na_own logrel_nais ⊤)%I
    in
    let code := mutual_attest_enclave_A_mod_encoding_1 in
    let lword1_b' :=
      if (decide (b' `mod` 2 = 0)%Z) then (b' ^+ 1)%a else b'
    in
    let lword1_e' :=
      if (decide (b' `mod` 2 = 0)%Z) then (b' ^+ 2)%a else (b' ^+ 1)%a
    in
    let lword1_a' :=
      prot_sealed_A
        ( if decide ((b' `mod` 2)%Z = 0%Z)
          then (b' ^+ 1)%a
          else b'
        )
    in
    let lword1 : LWord :=
      (LCap O lword1_b' lword1_e' lword1_a' v')
    in

    ContiguousRegion pc_a (length code) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->

   (PC ↦ᵣ LCap RX pc_b pc_e pc_a pc_v)
   ∗ codefrag pc_a pc_v code
   ∗ r_t1 ↦ᵣ LCap RW b' e' b' v'
   ∗ r_t2 ↦ᵣ w2
   ∗ r_t3 ↦ᵣ w3
   ∗ r_t4 ↦ᵣ w4
   ∗ r_t5 ↦ᵣ w5

   ∗ ▷ ( (PC ↦ᵣ LCap RX pc_b pc_e (pc_a ^+ length code)%a pc_v
          ∗ codefrag pc_a pc_v code
          ∗ r_t1 ↦ᵣ lword1
          ∗ (∃w2, r_t2 ↦ᵣ w2)
          ∗ (∃w3, r_t3 ↦ᵣ w3)
          ∗ (∃w4, r_t4 ↦ᵣ w4)
          ∗ (∃w5, r_t5 ↦ᵣ w5)
         -∗ WP Seq (Instr Executable) {{ v, φ v }}
       )
   )
   ⊢ WP Seq (Instr Executable) {{ v, φ v }}.
  Proof.
    intros φ code lword1_b' lword1_e' lword1_a' lword1 Hcont Hbounds.
    iIntros "(HPC & Hcode & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hφ)".
    (* GetB r_t2 r_t1 *)
    iInstr "Hcode".
    (* Add r_t3 r_t2 1 *)
    iInstr "Hcode".
    (* Mod r_t4 r_t2 2 *)
    wp_instr.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hr2 $Hr4 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hi & Hr2 & Hr4)".
    iEval (cbn) in "Hr4".
    wp_pure; iInstr_close "Hcode".

    (* Mov r_t5 PC *)
    iInstr "Hcode".
    (* Lea r_t5 6 *)
    iInstr "Hcode".

    destruct (decide ((b' `mod` 2%nat)%Z = 0)) as [Hmod | Hmod].
    - (* Jnz r_t5 r_t3 *)
      rewrite Hmod.
      iInstr "Hcode".
      (* Add r_t4 r_t3 1 *)
      iInstr "Hcode".
      (* Subseg r_t1 r_t3 r_t4 *)
      destruct ((b' + 2)%a) as [b2'|] eqn:Hb'2; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr3 Hr4") as "[Hmap _]".
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
      assert (b2' = (b' ^+ 2)%a) by solve_addr ; subst.
      destruct (decide ((b' ^+ 2)%a <= e')%a) as [Hb2e'|Hb2e']; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr3 Hr4") as "[Hmap _]".
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
          assert ((a ^+ 2)%a = a2) as <- by solve_addr.
          destruct Hbounds' as [ _ Hbounds' ].
          solve_addr + Hb2e' Hbounds'.
      }
      iInstr "Hcode".
      { transitivity (Some (b' ^+ 1))%a; solve_addr. }
      { transitivity (Some (b' ^+ 2))%a; solve_addr. }
      { solve_addr. }

      (* Lea r_t5 1 *)
      iInstr "Hcode".
      (* Jmp r_t5  *)
      iInstr "Hcode".
      (* Sub r_t3 1 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f1 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Restrict r_t1 (encodePerm O) *)
      iInstr "Hcode".
      { rewrite decode_encode_perm_inv ; done. }
      rewrite decode_encode_perm_inv.

      (* Continuation *)
      iApply "Hφ"; iFrame.
      iSplitL "Hr1".
      + rewrite /lword1 /lword1_b' /lword1_e' /lword1_a' /prot_sealed_A.
        destruct (decide ((((b' `mod` 2)%Z = 0%Z))%Z)); last lia.
        destruct (decide (((((b' ^+ 1)%a `mod` 2%nat)%Z = 0%Z))%Z)); iFrame.
        exfalso.
        rewrite Zmod_even in Hmod.
        rewrite Zmod_odd in e0.
        destruct (Z.even b') eqn:Hb'; try done.
        destruct (Z.odd (b' ^+ 1)%a) eqn:Hb''; try done.
        rewrite -Z.odd_succ in Hb'.
        assert ( (Z.succ b')%a = (z_of (b' ^+ 1)%a)) by solve_addr.
        solve_addr.
      + iSplitL "Hr2" ; first (iExists _; iFrame).
        iSplitL "Hr3" ; first (iExists _; iFrame).
        iSplitL "Hr4" ; (iExists _; iFrame).




    - (* Jnz r_t5 r_t3 *)
      iInstr "Hcode".
      { intro Hcontra ; by inv Hcontra. }
      (* Subseg r_t1 r_t2 r_t3 *)
      destruct ((b' + 1)%a) as [b1'|] eqn:Hb'1; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap _]".
        iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
        { solve_pure. }
        { by unfold regs_of; rewrite !dom_insert; set_solver+. }
        iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
        destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr2' Hr3' Hbounds' Hregs'
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
            in Hr3'.
          solve_addr + Hr3' Hb'1.
      }
      assert (b1' = (b' ^+ 1)%a) by solve_addr ; subst.
      destruct (decide ((b' ^+ 1)%a <= e')%a) as [Hb1e'|Hb1e']; cycle 1.
      {
        wp_instr.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap _]".
        iApply (wp_Subseg with "[$Hi $Hmap]"); try solve_pure; [| by simplify_map_eq |..].
        { solve_pure. }
        { by unfold regs_of; rewrite !dom_insert; set_solver+. }
        iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
        destruct Hspec as [ ? ? ? ? ? ? ? Hdst HpE Hr2' Hr3' Hbounds' Hregs'
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
            in Hr3'.
          clear - Hr3' Hb1e' Hbounds'.
          apply isWithin_implies in Hbounds'.
          assert ((a ^+ 1)%a = a2) as <- by solve_addr.
          destruct Hbounds' as [ _ Hbounds' ].
          solve_addr + Hb1e' Hbounds'.
      }
      iInstr "Hcode".
      { transitivity (Some (b' ^+ 1))%a; solve_addr. }
      { solve_addr. }

      (* Sub r_t3 1 r_t2 *)
      iInstr "Hcode".
      (* Lea r_t1 r_t3 *)
      iInstr "Hcode".
      { transitivity ( Some f1 ); try solve_addr.
        by rewrite finz_incr_minus_id.
      }
      (* Restrict r_t1 (encodePerm O) *)
      iInstr "Hcode".
      { rewrite decode_encode_perm_inv ; done. }
      rewrite decode_encode_perm_inv.

      (* Continuation *)
      iApply "Hφ"; iFrame.
      iSplitL "Hr1".
      + rewrite /lword1 /lword1_b' /lword1_e' /lword1_a' /prot_sealed_A.
        destruct (decide ((((b' `mod` 2)%Z = 0%Z))%Z)); first lia.
        by destruct (decide ((((b' `mod` 2%nat)%Z = 0%Z))%Z)); first lia.
      + iSplitL "Hr2" ; first (iExists _; iFrame).
        iSplitL "Hr3" ; first (iExists _; iFrame).
        iSplitL "Hr4" ; (iExists _; iFrame).
  Qed.


  Lemma mutual_attest_A_callback
    v b' e' a' v'
    enclave_data ot :
    let e := (length mutual_attest_enclave_A_code + 1)%Z in
    let pc_a := ((ma_addr_A ^+ 1) ^+ 39%nat)%a in
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
    ∗ interp (LSealRange (false, true) (ot ^+ 1)%f (ot ^+ 2)%f (ot ^+ 1)%f)
      -∗ interp (LCap E ma_addr_A (ma_addr_A ^+ e)%a pc_a v).
    Proof.
      intros e pc_a; subst e pc_a.
    iIntros (Hot Hb' He) "#(Henclaves_inv & Hma_inv & HPsign & Hinterp_sealr_ot)".

    iEval (rewrite fixpoint_interp1_eq /=).
    iIntros (lregs).
    iNext; iModIntro.
    iIntros "([%Hfullmap #Hinterp_map] & Hrmap & Hna)".


    rewrite /interp_conf.
    iMod (na_inv_acc with "Hma_inv Hna") as "(>[Hma_code Hma_data]  & Hna & Hclose)"; [solve_ndisj ..|].
    rewrite /registers_mapsto.
    iExtract "Hrmap" PC as "HPC".
    remember ma_addr_A as pc_b in |- * at 7.
    remember (ma_addr_A ^+ (121%nat + 1))%a as pc_e in |- * at 1.
    assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (121%nat + 1))%a) by (subst; solve_addr).

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
    iDestruct (region_mapsto_cons with "Hma_code") as "[Hma_addr_A Hma_code]"; last iFrame.
    { transitivity (Some (ma_addr_A ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }
    rewrite /mutual_attest_enclave_A_code.

    iDestruct (region_mapsto_split _ _ (ma_addr_A ^+ (119%nat + 1))%a with "Hma_code") as "[Hma_code HidT]"; last iFrame.
    { solve_addr. }
    { cbn.
      replace (ma_addr_A ^+ (119%nat + 1))%a
        with ((ma_addr_A ^+ 1)%a ^+ 119%nat)%a by solve_addr.
      rewrite finz_dist_add; solve_addr.
    }
    rewrite /mutual_attest_eid_table.
    iDestruct (region_mapsto_cons with "HidT") as "[HidTA HidTB]".
    { transitivity (Some (ma_addr_A ^+ (119%nat + 2))%a); auto ; try solve_addr. }
    { solve_addr. }
    iDestruct (region_mapsto_single with "HidTB") as (?) "[HidTB %Heq]".
    { solve_addr. }
    injection Heq; intros <- ; clear Heq.

    iAssert (codefrag (ma_addr_A ^+ 1)%a v mutual_attest_enclave_A_code_pre)
      with "[Hma_code]" as "Hma_code".
    {
      rewrite /codefrag /=.
      by replace ((ma_addr_A ^+ 1) ^+ 119%nat)%a with (ma_addr_A ^+ 120%nat)%a by solve_addr.
    }
    codefrag_facts "Hma_code".

    (* Data memory *)
    iDestruct (region_mapsto_cons with "Hma_data") as "[Hma_keys Hma_data]"; last iFrame.
    { transitivity (Some (b' ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }

    iEval (rewrite /mutual_attest_enclave_A_code_pre) in "Hma_code".
    focus_block 3 "Hma_code" as a_block3 Ha_block3 "Hma_code" "Hcont_code"
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
        (a_block3 + (pc_e - a_block3))%a
        = Some pc_e
      ) as Hpce by (subst; solve_addr).
    iInstr "Hma_code".
    (* Lea r_t4 (-size_idT)%Z *)
    iInstr "Hma_code".
    { transitivity (Some (pc_e ^+ -2)%a); solve_addr+Heqpc_e He. }
    (* Mov r_t3 r_t4 *)
    iInstr "Hma_code".
    (* Lea r_t3 offset_idB *)
    iInstr "Hma_code".
    { transitivity (Some (pc_e ^+ -1)%a); solve_addr+Heqpc_e He. }
    (* Load r_t3 r_t3 *)
    replace (pc_e ^+ -1)%a  with (ma_addr_A ^+ (120%nat + 1))%a by solve_addr + Heqpc_e He.
    iInstr "Hma_code".
    { subst; solve_addr+He. }
    (* GetA r_t5 r_t4 *)
    iInstr "Hma_code".
    (* Subseg r_t4 r_t5 r_t6 *)
    iInstr "Hma_code".
    { subst; solve_addr+He. }
    (* Hash r_t4 r_t4 *)
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    wp_instr.
    iAssert (
        [[(ma_addr_A ^+ (119%nat + 2))%a,(ma_addr_A ^+ (121%nat + 1))%a]]↦ₐ{v}[[
              [LInt hash_mutual_attest_B_pre] ]]%I
      ) with "[HidTB]" as "HidTB".
    { rewrite /region_mapsto.
      rewrite (finz_seq_between_singleton (ma_addr_A ^+ (119%nat + 2))%a)
      ; last solve_addr+He.
      by iFrame "HidTB".
    }
    iDestruct (region_mapsto_cons _ _  with "[$HidTA $HidTB]") as "HidT".
    { solve_addr+He. }
    { solve_addr+He. }
    iApply (wp_hash_success_same with "[$HPC $Hr4 $Hi HidT]"); try solve_pure.
    { subst pc_e.
      replace (ma_addr_A ^+ (119%nat + 1))%a with
        ((ma_addr_A ^+ (121%nat + 1)) ^+ -2)%a by solve_addr+He.
      iFrame.
    }
    iNext; iIntros "(HPC & Hi & Hr4 & HidT)".
    wp_pure; iInstr_close "Hma_code".
    iEval (cbn) in "Hr4".

    (* HashConcat r_t3 r_t3 r_t4 *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hr4 $Hr3 $Hi]"); try solve_pure.
    { done. }
    iNext. iIntros "(HPC & Hpc_a & Hr4 & Hr3)".
    iEval (cbn) in "Hr3".
    (* NOTE we use the axiom HERE! *)
    replace
      (hash_concat hash_mutual_attest_B_pre (hash [WInt hash_mutual_attest_A_pre; WInt hash_mutual_attest_B_pre]))
      with
      hash_mutual_attest_B.
    2:{
      rewrite /hash_mutual_attest_B /hash_mutual_attest_B_pre /mutual_attest_enclave_B_code.
      by rewrite -(assoc_L hash_concat) -/mutual_attest_eid_table fmap_app hash_concat_app.
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
    iMod (inv_acc with "Henclaves_inv") as "(Henclaves_inv_open & Hclose_inv)"; first solve_ndisj.
    iDestruct "Henclaves_inv_open" as (ECn) "(HEC & #Hcemap)".
    iApply (wp_estoreid_success_unknown_ec with "[$HPC $Hr5 $Hr4 $Hi $HEC]"); try solve_pure.
    iNext. iIntros (retv) "H".
    iDestruct "H" as "(Hi & Hr5 & HEC & [(-> & HPC & H)|(-> & HPC & Hr4)])".
    1: iDestruct "H" as (I tid) "(Hr4 & #Hma_env & [%Hseal %Htidx])".
    all: iMod ("Hclose_inv" with "[HEC Hcemap]") as "_"; [ iExists ECn; iFrame "HEC Hcemap" | iModIntro].
    all: wp_pure; iInstr_close "Hma_code".
    2:{ wp_end; by iIntros (?). }
    iDestruct (interp_valid_sealed with "Hinterp_w1") as (Φ) "Hseal_valid".

    (* Sub r_t3 r_t3 r_t4 *)
    iInstr "Hma_code".
    (* Mov r_t5 PC *)
    iInstr "Hma_code".
    (* Lea r_t5 5 *)
    iInstr "Hma_code".

    destruct (decide (I = hash_mutual_attest_B)) as [-> | HnI]
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
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap _]".
    iApply (wp_UnSeal with "[$Hmap $Hi]") ; try (by simplify_map_eq) ; try solve_pure.
    { apply isCorrectPC_isCorrectLPC ; cbn. constructor; last naive_solver.
      solve_addr.
    }
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [ ? ? ? ? ? ? ? Hps Hbounds Hregs'|]; cycle 1.
    { by wp_pure; wp_end; by iIntros (?). }
    Opaque mutual_attest_enclave_B_code_pre encodeInstrsLW.
    incrementLPC_inv as (p''&b_main'&e_main'&a_main'&pc_v'& ? & HPC & Z & Hregs');
      simplify_map_eq.
    repeat (rewrite insert_commute //= insert_insert).
    Transparent mutual_attest_enclave_A_code_pre encodeInstrsLW.
    replace x with (a_block3 ^+ 29)%a by solve_addr.
    clear Z.
    iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame.
    wp_pure; iInstr_close "Hma_code".

    iAssert (
        if Z.even a
        then seal_pred a (Penc mutual_attest_enclave_B_pred)
             ∗ seal_pred (a ^+ 1)%f (Psign mutual_attest_enclave_B_pred)
        else seal_pred (a ^+ -1)%f (Penc mutual_attest_enclave_B_pred)
             ∗ seal_pred a (Psign mutual_attest_enclave_B_pred)
      )%I as "Hma_B".
    {
      iApply "Hcemap"; iFrame "%#∗".
      + iPureIntro; apply wf_ma_enclaves_map.
      + iPureIntro; rewrite /ma_enclaves_map.
        rewrite lookup_insert_ne; first by rewrite lookup_insert.
        rewrite /hash_mutual_attest_A /hash_mutual_attest_B.
        intro Hcontra.
        apply hash_concat_inj' in Hcontra.
        destruct Hcontra as [_ Hcontra].
        rewrite /mutual_attest_enclave_A_code /mutual_attest_enclave_B_code in Hcontra.
        by injection Hcontra.
    }

    destruct (Z.even (finz.to_z a)) eqn:HEven_a
    ; iDestruct "Hma_B" as "[Hma_B_Penc Hma_B_Psign]"
    ; iEval (cbn) in "Hma_B_Penc"
    ; iEval (cbn) in "Hma_B_Psign".
    {
      iDestruct (seal_pred_valid_sealed_eq with "[$Hma_B_Penc] Hseal_valid") as "Heqv".
      iAssert (▷ False)%I as ">%Hcontra"; last done.
      iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      by iRewrite "Heqv".
    }
    iDestruct (seal_pred_valid_sealed_eq with "[$Hma_B_Psign] Hseal_valid") as "Heqv".
    iAssert (▷ sealed_enclaveB (LWSealable sb))%I as (fb fe fv) ">%Hseal_B".
    { iDestruct "Hseal_valid" as (sb') "(%Heq & _ & _ & HΦ)".
      inversion Heq; subst.
      iSpecialize ("Heqv" $! (LWSealable sb')).
      iNext.
      iRewrite "Heqv".
      iFrame "HΦ". }
    destruct sb ; simplify_eq.
    iClear "Heqv Hma_B_Penc Hcemap Henclaves_inv".

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
    replace (f43 - 43%nat)%Z with 0%Z by (clear; solve_addr).
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
        ((a_block3 ^+ 44) + (ma_addr_A - (a_block3 ^+ 44)%a))%a
        = Some (ma_addr_A)) by solve_addr+He.
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
    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code hma_code.


    focus_block 4 "Hma_code" as a_block4 Ha_block4 "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.
    iApply ( enclave_A_mod_encoding_1_spec
             with "[- $HPC $Hma_code $Hr1 $Hr2 $Hr3 $Hr4 $Hr5]" ); eauto.
    iNext; iIntros "(HPC & Hma_code & Hr1 & Hr2 & Hr3 & Hr4 & Hr5)".
    iDestruct "Hr2" as (w2'') "Hr2".
    iDestruct "Hr3" as (w3'') "Hr3".
    iDestruct "Hr4" as (w4'') "Hr4".
    iDestruct "Hr5" as (w5'') "Hr5".
    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code.


    focus_block 5 "Hma_code" as a_block5 Ha_block5 "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.

    (* Lea r_t6 1 *)
    iInstr "Hma_code".
    { transitivity (Some (ot ^+ 1)%ot); solve_addr+Hot. }
    (* Seal r_t1 r_t6 r_t1 *)
    iInstr "Hma_code".
    { done. }
    { solve_addr+Hot. }
    (* GetA r_t3 r_t6 *)
    iInstr "Hma_code".
    (* Add r_t4 r_t3 1 *)
    iInstr "Hma_code".
    (* Subseg r_t6 r_t3 r_t4 *)
    iInstr "Hma_code".
    { transitivity (Some ( ((ot ^+ 2)%ot ))); solve_addr+Hot. }
    { solve_addr+Hot. }
    (* Restrict r_t6 (encodeSealPerms (false,true)) *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_restrict_success_z_sr with "[$Hi $HPC $Hr6]"); try solve_pure.
    { by rewrite decode_encode_seal_perms_inv; cbn. }
    iNext; iIntros "(HPC & Hi & Hr6)".
    iEval (rewrite decode_encode_seal_perms_inv /=) in "Hr6".
    wp_pure; iInstr_close "Hma_code".
    (*   Mov r_t2 r_t6; *)
    iInstr "Hma_code".
    (*   Mov r_t3 0; *)
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


    set (lword1 := LSealedCap (ot ^+ 1)%ot _ _ _ _ _).
    (* ----- Prepare the use of FTLR ----- *)
    iAssert (interp lword1) as "Hinterp_sealed_b'".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_enclaveA; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_enclaveA_persistent. }
      { iNext; by iExists _,_,_. }
    }

    (* Close the opened invariant *)
    iDestruct (region_mapsto_cons with "[Hma_addr_A Hma_code]") as "Hma_code"
    ; try iFrame.
    { solve_addr+He. }
    { solve_addr+He. }
    rewrite -/mutual_attest_eid_table.
    iDestruct (region_mapsto_split
                 ma_addr_A
                 (ma_addr_A ^+ (121%nat + 1))%a
                 ((ma_addr_A ^+ 1) ^+ 119%nat)%a
                with "[$Hma_code HidT]") as "Hma_code"; last iFrame.
    { solve_addr+He. }
    { cbn.
      rewrite finz_dist_S; last solve_addr+He.
      f_equal.
      rewrite finz_dist_add; solve_addr+He.
    }
    { replace ((ma_addr_A ^+ (121%nat + 1)) ^+ -2)%a with
        ((ma_addr_A ^+ 1) ^+ 119%nat)%a by solve_addr+He.
      iFrame. }
    iDestruct (region_mapsto_cons with "[$Hma_keys $Hma_data]") as "Hma_data" ; last iFrame.
    { solve_addr+Hb'. }
    { solve_addr+Hb'. }
    iMod ("Hclose" with "[$Hna $Hma_code $Hma_data]") as "Hna".

    (* Wrap up the registers *)
    Opaque mutual_attest_enclave_A_code_pre encodeInstrsLW.
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
    Transparent mutual_attest_enclave_A_code_pre encodeInstrsLW.
    iApply ("Hjmp" with "[]") ; eauto ; iFrame.
    Qed.

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
    remember (ma_addr_A ^+ (121%nat + 1))%a as pc_e in |- * at 4.
    assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (121%nat + 1))%a) by (subst; solve_addr).

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
    iDestruct (region_mapsto_cons with "Hma_code") as "[Hma_addr_A Hma_code]"; last iFrame.
    { transitivity (Some (ma_addr_A ^+ 1)%a); auto ; try solve_addr. }
    { solve_addr. }
    rewrite /mutual_attest_enclave_A_code.

    iDestruct (region_mapsto_split _ _ (ma_addr_A ^+ (119%nat + 1))%a with "Hma_code") as "[Hma_code HidT]"; last iFrame.
    { solve_addr. }
    { cbn.
      replace (ma_addr_A ^+ (119%nat + 1))%a
        with ((ma_addr_A ^+ 1)%a ^+ 119%nat)%a by solve_addr.
      rewrite finz_dist_add; solve_addr.
    }
    rewrite /mutual_attest_eid_table.
    iDestruct (region_mapsto_cons with "HidT") as "[HidTA HidTB]".
    { transitivity (Some (ma_addr_A ^+ (119%nat + 2))%a); auto ; try solve_addr. }
    { solve_addr. }

    iAssert (codefrag (ma_addr_A ^+ 1)%a v mutual_attest_enclave_A_code_pre)
      with "[Hma_code]" as "Hma_code".
    {
      rewrite /codefrag /=.
      by replace ((ma_addr_A ^+ 1) ^+ 119%nat)%a with (ma_addr_A ^+ 120%nat)%a by solve_addr.
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
    (* Mov r_t5 PC *)
    iInstr "Hma_code".
    (* GetA r_t1 r_t5 *)
    iInstr "Hma_code".
    (* GetB r_t2 r_t5 *)
    iInstr "Hma_code".
    (* Sub r_t1 r_t2 r_t1 *)
    iInstr "Hma_code".
    (* Lea r_t5 r_t1 *)
    assert (
        ((ma_addr_A ^+ 1) + (pc_b - (ma_addr_A ^+ 1)%a))%a
        = Some ma_addr_A
      ) as Hpcb by (subst; solve_addr).
    iInstr "Hma_code".
    (* Load r_t1 r_t5 *)
    iInstr "Hma_code".
    { split ; try solve_pure. solve_addr. }

    (* GetA r_t2 r_t1 *)
    iInstr "Hma_code".
    (* GetB r_t3 r_t1 *)
    iInstr "Hma_code".
    (* Sub r_t2 r_t3 r_t2 *)
    iInstr "Hma_code".
    (* Lea r_t1 r_t2 *)
    iInstr "Hma_code".
    { transitivity (Some (b')); solve_addr. }
    (* Load r_t6 r_t1 *)
    iInstr "Hma_code".
    { split ; try solve_pure. solve_addr. }

    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code hma_code.


    focus_block 1 "Hma_code" as a_block1 Ha_block1 "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.
    iApply ( enclave_A_mod_encoding_42_spec
             with "[- $HPC $Hma_code $Hr1 $Hr2 $Hr3 $Hr4 $Hr5]" ); eauto.
    iNext; iIntros "(HPC & Hma_code & Hr1 & Hr2 & Hr3 & Hr4 & Hr5)".
    iDestruct "Hr2" as (w2') "Hr2".
    iDestruct "Hr3" as (w3') "Hr3".
    iDestruct "Hr4" as (w4') "Hr4".
    iDestruct "Hr5" as (w5') "Hr5".
    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code.



    focus_block 2 "Hma_code" as a_block2 Ha_block2 "Hma_code" "Hcont_code"
    ; iHide "Hcont_code" as hcont_code.

    (* Lea r_t6 1 *)
    iInstr "Hma_code".
    { transitivity (Some (ot ^+ 1)%ot); solve_addr. }
    (* Seal r_t1 r_t6 r_t1 *)
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
    (* Restrict r_t6 (encodeSealPerms (false, true)) *)
    wp_instr.
    iInstr_lookup "Hma_code" as "Hi" "Hma_code".
    iApply (wp_restrict_success_z_sr with "[$Hi $HPC $Hr6]"); try solve_pure.
    { by rewrite decode_encode_seal_perms_inv; cbn. }
    iNext; iIntros "(HPC & Hi & Hr6)".
    iEval (rewrite decode_encode_seal_perms_inv /=) in "Hr6".
    wp_pure; iInstr_close "Hma_code".
    (* Mov r_t3 PC *)
    iInstr "Hma_code".
    (* Lea r_t3 8 *)
    iInstr "Hma_code".
    (* Restrict r_t3 (encodePerm E) *)
    iInstr "Hma_code".
    { by rewrite decode_encode_perm_inv. }
    rewrite decode_encode_perm_inv.
    (* Mov r_t2 r_t6 *)
    iInstr "Hma_code".
    (* Mov r_t4 0 *)
    iInstr "Hma_code".
    (* Mov r_t5 0 *)
    iInstr "Hma_code".
    (* Mov r_t6 0 *)
    iInstr "Hma_code".
    (* Jmp r_t0 *)
    iInstr "Hma_code".
    unfocus_block "Hma_code" "Hcont_code" as "Hma_code"
    ; subst hcont_code.

    set (lword42 := LSealedCap _ _ _ _ _ _).
    (* ----- Prepare the use of FTLR ----- *)
    iAssert (interp lword42) as "Hinterp_sealed_b'".
    {
      iEval (rewrite /= fixpoint_interp1_eq /= /interp_sb).
      iExists sealed_enclaveA; iFrame "%#".
      iSplit.
      { iPureIntro; intro; apply sealed_enclaveA_persistent. }
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
      iSplit ; last done.
      iExists sealed_enclaveA_ne; iFrame "#".
      iNext ; iModIntro; iIntros (lw) "Hlw".
      by iApply sealed_enclaveA_interp.
    }
    iAssert (interp (LCap E pc_b pc_e (a_block2 ^+ 14)%a v)) as "Hinterp_return".
    {
      replace
        (a_block2 ^+ 14)%a with ((ma_addr_A ^+ 1) ^+ 39%nat)%a by solve_addr.
      subst pc_b pc_e.
      iApply (mutual_attest_A_callback with "[-]"); last iFrame "#"; eauto.
    }

    (* Close the opened invariant *)
    iDestruct (region_mapsto_cons with "[Hma_addr_A Hma_code]") as "Hma_code"
    ; try iFrame.
    { solve_addr. }
    { solve_addr. }
    rewrite -/mutual_attest_eid_table.
    iDestruct (region_mapsto_cons _ _  with "[$HidTA $HidTB]") as "HidT".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_mapsto_split
                 ma_addr_A
                 (ma_addr_A ^+ (121%nat + 1))%a
                 ((ma_addr_A ^+ 1) ^+ 119%nat)%a
                with "[$Hma_code HidT]") as "Hma_code"; last iFrame.
    { solve_addr. }
    { cbn.
      rewrite finz_dist_S; last solve_addr.
      f_equal.
      rewrite finz_dist_add; solve_addr.
    }
    { replace (ma_addr_A ^+ (119%nat + 1))%a with
        ((ma_addr_A ^+ 1) ^+ 119%nat)%a by solve_addr.
      iFrame. }
    iDestruct (region_mapsto_cons with "[$Hma_keys $Hma_data]") as "Hma_data" ; last iFrame.
    { solve_addr. }
    { solve_addr. }
    iMod ("Hclose" with "[$Hna $Hma_code $Hma_data]") as "Hna".

    (* Wrap up the registers *)
    Opaque mutual_attest_enclave_A_code_pre encodeInstrsLW.
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
  Qed.

End mutual_attest_A.
