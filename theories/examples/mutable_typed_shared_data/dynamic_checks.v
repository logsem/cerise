From iris.proofmode Require Import proofmode.
From cap_machine Require Import fundamental logrel macros macros_helpers proofmode rules register_tactics.

Section dynamic_checks.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ} `{MP: MachineParameters}.

  (* Instructions to dynamically type check if the type of the register `r` is `WInt`. *)
  (* This will override the registers `r_tmp` and `rjmp_tmp`. *)
  Definition dyn_typecheck_int_instrs (r : RegName) (r_tmp r_jmptmp : RegName) := encodeInstrsW [
    IsPtr r_tmp r;          (* r_tmp = 0  <=> r: WInt/WSealRange/WSealed; r_tmp = 1 <=> r: WCap *)
    Sub r_tmp r_tmp 1;      (* r_tmp = -1 <=> r: WInt/WSealRange/WSealed; r_tmp = 0 <=> r: WCap *)

    Mov r_jmptmp (inr PC);
    Lea r_jmptmp (inl 4)%Z;
    Jnz r_jmptmp r_tmp;     (* Jump after the `Fail` instruction if (r_tmp != 0 <=> r: WInt/WSealRange/WSealed) *)

    Fail                    (* Fail if r: WCap *)
  ].

  (* Instructions to dynamically type check if the type of the register `r` is `WCap`. *)
  (* This will use the registers `r_tmp` and `rjmp_tmp`. *)
  Definition dyn_typecheck_cap_instrs (r : RegName) (r_tmp r_jmptmp : RegName) := encodeInstrsW [
    IsPtr r_tmp r;          (* r_tmp = 0  <=> r: WInt/WSealRange/WSealed; r_tmp = 1 <=> r: WCap *)

    Mov r_jmptmp (inr PC);
    Lea r_jmptmp (inl 4)%Z;
    Jnz r_jmptmp r_tmp;     (* Jump after the `Fail` instruction if (r_tmp != 0 <=> r: WCap) *)

    Fail                    (* Fail if r: WInt/WSealRange/WSealed *)
  ].

  Lemma dyn_typecheck_int_spec
    p_pc b_pc e_pc a_pc (* PC *)
    r r_tmp r_jmptmp    (* Registers *)
    v w1 w2             (* Values in registers *)
    φ:

    let instrs := dyn_typecheck_int_instrs r r_tmp r_jmptmp in
    let length := (length instrs) in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_pc (a_pc ^+ length)%a →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ codefrag a_pc instrs
      ∗ r ↦ᵣ v
      ∗ r_tmp ↦ᵣ w1
      ∗ r_jmptmp ↦ᵣ w2
      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ length)%a
             ∗ codefrag a_pc instrs
             ∗ r ↦ᵣ v
             ∗ ⌜is_z v⌝
             ∗ (∃ w, r_tmp ↦ᵣ w)
             ∗ (∃ w, r_jmptmp ↦ᵣ w)
             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? Hexec ?) "(HPC & Hprog & Hr & Hr_tmp & Hr_jmptmp & Hφ)".
    subst instrs length.

    codefrag_facts "Hprog"; simpl in *.

    destruct v.
    - (* WInt *)
      iGo "Hprog".

      assert
        ((match p_pc with
         | E => _
         | _ => _
         end) = WCap p_pc b_pc e_pc (a_pc ^+ 6)%a) as ->.
      { destruct p_pc; auto.
        by inversion Hexec. }

      iGo "Hprog".
      iApply "Hφ".
      iFrame.
      iSplit; [ done |].
      iSplitL "Hr_tmp"; eauto.

    - (* WSealable *)
      destruct sb.
      + (* WCap *)
        iGo "Hprog".
        iApply wp_value.
        by iRight.

      + (* WSealRange *)
        admit. (* TODO: Waiting for a way to discriminate *)


    - (* WSealed *)
      admit. (* TODO: Waiting for a way to discriminate *)
  Admitted.

  Lemma dyn_typecheck_cap_spec
    p_pc b_pc e_pc a_pc (* PC *)
    r r_tmp r_jmptmp    (* Registers *)
    v w1 w2             (* Values in registers *)
    φ:

    let instrs := dyn_typecheck_cap_instrs r r_tmp r_jmptmp in
    let length := (length instrs) in

    ExecPCPerm p_pc →
    SubBounds b_pc e_pc a_pc (a_pc ^+ length)%a →

    PC ↦ᵣ WCap p_pc b_pc e_pc a_pc
      ∗ codefrag a_pc instrs
      ∗ r ↦ᵣ v
      ∗ r_tmp ↦ᵣ w1
      ∗ r_jmptmp ↦ᵣ w2
      ∗ ▷ (PC ↦ᵣ WCap p_pc b_pc e_pc (a_pc ^+ length)%a
             ∗ codefrag a_pc instrs
             ∗ r ↦ᵣ v
             ∗ ⌜is_cap v⌝
             ∗ (∃ w, r_tmp ↦ᵣ w)
             ∗ (∃ w, r_jmptmp ↦ᵣ w)
             -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (? ? Hexec ?) "(HPC & Hprog & Hr & Hr_tmp & Hr_jmptmp & Hφ)".
    subst instrs length.

    codefrag_facts "Hprog"; simpl in *.

    destruct v.
    - (* WInt *)
      iGo "Hprog".
      iApply wp_value.
      by iRight.

    - (* WSealable *)
      destruct sb.
      + (* WCap *)
        iGo "Hprog".

        assert
          ((match p_pc with
          | E => _
          | _ => _
          end) = WCap p_pc b_pc e_pc (a_pc ^+ 5)%a) as ->.
        { destruct p_pc; auto.
          by inversion Hexec. }

        iGo "Hprog".
        iApply "Hφ".
        iFrame.
        iSplit; [ done |].
        iSplitL "Hr_tmp"; eauto.

      + (* WSealRange *)
        iGo "Hprog".
        iApply wp_value.
        by iRight.

    - (* WSealed *)
      iGo "Hprog".
      iApply wp_value.
      by iRight.
  Qed.

End dynamic_checks.
