From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone list call malloc.

Section sealing.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* Assume r_t1 contains a capability representing a sealed value.
     Get its b field, find the corresponding value in the linked list contained in r_env.
     Result is returned in r_t1; clear r_env for security and return. *)
  (* Arguments: r_t1 rret
     Uses: r_env *)
  Definition unseal_instr rret :=
    [ getb r_t1 r_t1 ]
    ++ findb_instr ++
    [ move_z r_env 0
    ; jmp rret
    ].

  (* Assume r_t1 contains the word to seal.
     Append it to the linked list contained in r_env.
     Restrict the new capability to O permission.
     Subseg it, clear r_env and return *)
  (* Arguments: r_t1 rret
     Uses: r_env r_t0 *)
  Definition seal_instr f_m rret :=
    appendb_instr f_m ++
    [ restrict_z r_t1 (encodePerm O)
    ; getb r_t0 r_t1
    ; subseg_r_r r_t1 r_t0 r_t0
    ; move_z r_env 0
    ; jmp rret
    ].

  (* Create two closures for sealing and unsealing *)
  (* TODO *)
  Definition make_seal f_m :=
    malloc_instrs f_m (42).

End sealing.
