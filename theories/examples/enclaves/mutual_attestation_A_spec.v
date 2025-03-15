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
    let lword42 : LWord :=
      if (decide (b' `mod` 2 = 0)%Z)
      then (LCap O b'          (b' ^+ 1)%a (prot_sealed_A b') v')
      else (LCap O (b' ^+ 1)%a (b' ^+ 2)%a (prot_sealed_A (b'^+1)%a) v')
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
    intros φ code lword42 Hcont Hbounds.
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
      + rewrite /lword42 /prot_sealed_A.
        rewrite Hmod.
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
      + rewrite /lword42 /prot_sealed_A.
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
    let lword1 : LWord :=
      if (decide (b' `mod` 2 = 0)%Z)
      then (LCap O (b' ^+ 1)%a (b' ^+ 2)%a (prot_sealed_A (b'^+1)%a) v')
      else (LCap O b'          (b' ^+ 1)%a (prot_sealed_A b') v')
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
    intros φ code lword1 Hcont Hbounds.
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
      + rewrite /lword1 /prot_sealed_A.
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
      + rewrite /lword1 /prot_sealed_A.
        destruct (decide ((((b' `mod` 2)%Z = 0%Z))%Z)); first lia.
        by destruct (decide ((((b' `mod` 2%nat)%Z = 0%Z))%Z)); first lia.
      + iSplitL "Hr2" ; first (iExists _; iFrame).
        iSplitL "Hr3" ; first (iExists _; iFrame).
        iSplitL "Hr4" ; (iExists _; iFrame).
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
    (* remember (ma_addr_A ^+ (91%nat + 1))%a as pc_e in |- * at 4. *)
    (* assert (SubBounds pc_b pc_e ma_addr_A (ma_addr_A ^+ (91%nat + 1))%a) by (subst; solve_addr). *)
  Admitted.

End mutual_attest_A.
