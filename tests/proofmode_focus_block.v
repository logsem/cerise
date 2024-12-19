From iris.proofmode Require Import tactics.
From cap_machine Require Import proofmode.

Definition l1 `{MP: MachineParameters} := encodeInstrsW [ Mov r_t1 1; Mov r_t1 0 ].
Definition i1 `{MP: MachineParameters} := encodeInstrsW [ Mov r_t2 1; Mov r_t2 0 ].
Definition i2 `{MP: MachineParameters} := encodeInstrsW [ Mov r_t3 1; Mov r_t3 0 ].
Definition l2 `{MP: MachineParameters} := i1 ++ i2.

Lemma foo {Σ:gFunctors} {ceriseg:ceriseG Σ} `{MP: MachineParameters} p b e a :
  {{{ ⌜ExecPCPerm p ∧ SubBounds b e a (a ^+ length (l1 ++ l2))%a⌝
      ∗ codefrag a (l1 ++ l2)
      ∗ PC ↦ᵣ WCap (p,b,e,(a ^+ length l1)%a) }}}
    Seq (Instr Executable)
  {{{ RET HaltedV; True }}}.
Proof.
  iIntros (Φ) "(%He & Hcode & HPC) HΦ".
  destruct He as [He Hs].
  focus_block 1 "Hcode" as a_mid Ha_mid "Hblock" "Hcont".
  (* check that "Hblock" is [codefrag a_mid l2] *)
  iAssert (codefrag a_mid l2) with "Hblock" as "Hblock".
Abort.
