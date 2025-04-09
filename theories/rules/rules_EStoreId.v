From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac gmap.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{ceriseg: ceriseG Σ}.
  Context `{MP: MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : Version.
  Implicit Types lw: LWord.
  Implicit Types reg : Reg.
  Implicit Types lregs : LReg.
  Implicit Types mem : Mem.
  Implicit Types lmem : LMem.

  Inductive EStoreId_spec (lregs lregs' : LReg) (rs rd : RegName) tidx (I : EIdentity) : cap_lang.val -> Prop :=
  | EStoreId_spec_success otype :
    lregs !! rs = Some (LInt otype) ->
    incrementLPC ((<[rd := LInt I]> lregs)) = Some lregs' →
    has_seal otype tidx → (* we associate a given table index with the provided otype *)
    EStoreId_spec lregs lregs' rs rd tidx I NextIV
  |EStoreId_spec_failure_incr_pc:
    incrementLPC lregs = None →
    lregs = lregs' →
    EStoreId_spec lregs lregs' rs rd tidx I FailedV.
  (* |EStoreId_spec_failure_other: *)
  (*   EStoreId_spec lregs lregs' rs rd any otype tidx FailedV. *)

  (* TODO @Denis *)
  (* The EStoreId instruction fetches the machine's stored hash for a given OType.
     It is used by the client of an enclave to verify that a value signed by a given OType originates from code with a known hash `I`. *)
  (* Logically, the crux of this contract is that the post-condition contains a duplicable resource `enclave_all`,
     which states that an enclave has existed at some point in the past at some index `tidx` in the enclave table, and that this index corresponds to some hash/EIdentity `I` *)
  (* Essentially it gives us a partial view on the enclave table, since we now know that at a particular index, at some point, there was an enclave with a particular identity. *)
  (* In a later step of the verification, an invariant will allow us to trade this resource for the specific predicate that always holds for results signed by enclaves with that hash... *)
  (* This enables "learning" some information about the signed, yet unknown result: we will be able to establish that at least the above predicate will hold for it... *)
  (* NOTE @June what if we already have the resource `enclave_cur(tidx, I)` ? *)
  Lemma wp_estoreid E pc_p pc_b pc_e pc_a pc_v lw rd rs lregs :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    regs_of (EStoreId rd rs) ⊆ dom lregs →
    lregs !! PC = Some (LCap pc_p pc_b pc_e pc_a pc_v) →

    {{{ (▷ [∗ map] k↦y ∈ lregs, k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw
    }}}
      Instr Executable @ E
    {{{ lregs' tidx I retv, RET retv;
        ⌜ EStoreId_spec lregs lregs' rs rd tidx I retv⌝ ∗
        ([∗ map] k↦y ∈ lregs', k ↦ᵣ y) ∗
        (pc_a, pc_v) ↦ₐ lw ∗
        if decide (retv = NextIV) then (enclave_all tidx I) (*!*) else emp }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HPC φ) "(>Hrmap & Hpca) Hφ".
    iApply (wp_instr_exec_opt Hvpc HPC Hinstr Dregs with "[$Hpca $Hrmap Hφ]").
    iModIntro.
    iIntros (σ1) "(Hσ1 & Hmap &Hpc_a)".
    iModIntro.
    iIntros (wa) "(%Hrpc & %Hmema & %Hcorrpc & %Hdecode) Hcred".
    apply isCorrectLPC_isCorrectPC_iff in Hvpc; cbn in Hvpc.

    iApply wp_wp2.

    iMod (state_interp_transient_intro (lm:= ∅) with "[$Hmap $Hσ1]") as "Hσ".
    { by rewrite big_sepM_empty. }

    iApply wp_opt2_bind.
    iApply wp_opt2_eqn_both.
    iApply (wp2_reg_lookup with "[$Hσ Hφ Hcred Hpc_a]") ; first by set_solver.
    iIntros (lwrs2) "Hσ %HrsL2 %Hrs2".

  Admitted.

  Lemma wp_estoreid_success_unknown E pc_p pc_b pc_e pc_a pc_a' pc_v lw rd rs otype any :
    decodeInstrWL lw = EStoreId rd rs →
    isCorrectLPC (LCap pc_p pc_b pc_e pc_a pc_v) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
        ▷ (pc_a, pc_v) ↦ₐ lw ∗
        ▷ rs ↦ᵣ LWInt otype ∗
        ▷ rd ↦ᵣ any }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (pc_a, pc_v) ↦ₐ lw ∗
        rs ↦ᵣ LWInt otype ∗
        ((⌜ retv = NextIV ⌝ ∗
          PC ↦ᵣ LCap pc_p pc_b pc_e pc_a' pc_v ∗
          ∃ (I : EIdentity), ∃ (tid : TIndex),
            rd ↦ᵣ (LWInt I) ∗
            (enclave_all tid I) ∗
            ⌜ has_seal otype tid ⌝)
           ∨
           (⌜ retv = FailedV ⌝ ∗
            PC ↦ᵣ LCap pc_p pc_b pc_e pc_a pc_v ∗
            rd ↦ᵣ any)
         ) }}}.
    Proof.
    iIntros (Hinstr Hvpc Hpca φ) "(>HPC & >Hpc_a & >Hrs & >Hrd) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrs Hrd") as "[Hrmap (%&%&%)]".

    (* iDestruct (big_opM_delete with "H"). *)
    iApply (wp_estoreid with "[$Hrmap $Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }


    iNext. iIntros (lregs' tidx I retv) "(#Hspec & Hrmap & HPCa & Henclave)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec eqn:?
    ; [ erewrite decide_True | erewrite decide_False ]; rewrite // ;
      simplify_eq; cycle 1; cbn; iApply "Hφ"; iFrame.
    - rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".
      iFrame.
      iRight; iFrame.
      done.
      (* iDestruct "Hpost" as "Hrd". iFrame. iSplit. by iPureIntro. subst. *)
      (* rewrite big_opM_insert_delete. iDestruct "Hrmap" as "[$ Hrmap]". *)
    - rewrite lookup_insert_ne in e ; last done.
      rewrite lookup_insert in e; simplify_eq.
      apply incrementLPC_Some_inv in e0 as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite (insert_commute _ rd PC) // insert_insert.
      rewrite (insert_commute _ rd rs) // insert_insert.
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[HPC Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrs Hrmap]".
      rewrite big_sepM_insert; last by simplify_map_eq.
      iDestruct "Hrmap" as "[Hrd _]".

      iFrame. iLeft; iFrame.
      iSplit ; first done.
      iExists I, tidx; iFrame.
      done.
      (* (* iDestruct "Hpost" as "[%I (Hrd & Henc)]". *) *)
      (* iFrame. iSplitR. by iPureIntro. *)
      (* clear Heqe. apply incrementLPC_Some_inv in e as (?&?&?&?&?&?&?&?&?). *)
      (* subst. *)

      (* rewrite big_opM_insert_delete. *)

      (* rewrite lookup_insert_ne in H2; auto. *)
      (* rewrite lookup_insert_ne in H2; auto. *)
      (* rewrite lookup_insert in H2. *)
      (* inversion H2; subst. *)

      (* rewrite Hpca in H3. inversion H3. *)

      (*  iDestruct "Hrmap" as "[$ Hrmap]". *)
      (* iExists I, tidx. iFrame. by iPureIntro. *)
  Qed.

End cap_lang_rules.
