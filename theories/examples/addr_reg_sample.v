From Coq Require Import Eqdep_dec.
From stdpp Require Import gmap fin_maps list.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export addr_reg cap_lang region.

(* Instructions and their decodings *)
(* A special register for the stack pointer, different from PC *)
Definition r_stk : RegName := r_t31.
Definition r_env : RegName := r_t30.
Lemma r_stk_ne : r_stk ≠ PC. Proof. done. Qed.

Section instr_encodings.
  Context `{MachineParameters}.

  (* Restore code encodings *)
  Definition w_1 := encodeInstr (Mov r_t1 (inr PC)).
  Definition w_2 := encodeInstr (Lea r_t1 (inl 7%Z)).
  Definition w_2_U := encodeInstr (Lea r_t1 (inl 6%Z)).
  Definition w_3 := encodeInstr (Load r_stk r_t1).
  Definition w_4a := encodeInstr (Sub r_t1 (inl 0%Z) (inl 1%Z)).
  Definition w_4b := encodeInstr (Lea r_stk (inr r_t1)).
  Definition w_4c := encodeInstr (Load PC r_stk).
  (* Instruction encodings *)
  Definition lea_z r z := encodeInstrW (Lea r (inl z)).
  Definition lea_r r1 r2 := encodeInstrW (Lea r1 (inr r2)).
  Definition store_z r z := encodeInstrW (Store r (inl z)).
  Definition store_r r1 r2 := encodeInstrW (Store r1 (inr r2)).
  Definition load_r r1 r2 := encodeInstrW (Load r1 r2).
  Definition move_z r z := encodeInstrW (Mov r (inl z)).
  Definition move_r r1 r2 := encodeInstrW (Mov r1 (inr r2)).
  Definition restrict_r r1 r2 := encodeInstrW (Restrict r1 (inr r2)).
  Definition restrict_z r z := encodeInstrW (Restrict r (inl z)).
  Definition geta r1 r2 := encodeInstrW (GetA r1 r2).
  Definition getb r1 r2 := encodeInstrW (GetB r1 r2).
  Definition gete r1 r2 := encodeInstrW (GetE r1 r2).
  Definition getp r1 r2 := encodeInstrW (GetP r1 r2).
  Definition add_r_z r1 r2 z := encodeInstrW (Add r1 (inr r2) (inl z)).
  Definition add_r_r r1 r2 r3 := encodeInstrW (Add r1 (inr r2) (inr r3)).
  Definition sub_r_r r1 r2 r3 := encodeInstrW (Sub r1 (inr r2) (inr r3)).
  Definition sub_r_z r1 r2 z := encodeInstrW (Sub r1 (inr r2) (inl z)).
  Definition sub_z_r r1 z r2 := encodeInstrW (Sub r1 (inl z) (inr r2)).
  Definition sub_z_z r z1 z2 := encodeInstrW (Sub r (inl z1) (inl z2)).
  Definition subseg_r_r r1 r2 r3 := encodeInstrW (Subseg r1 (inr r2) (inr r3)).
  Definition subseg_z_z r1 z1 z2 := encodeInstrW (Subseg r1 (inl z1) (inl z2)).
  Definition jnz r1 r2 := encodeInstrW (Jnz r1 r2).
  Definition lt_r_r r1 r2 r3 := encodeInstrW (Lt r1 (inr r2) (inr r3)).
  Definition lt_z_r r1 z r2 := encodeInstrW (Lt r1 (inl z) (inr r2)).
  Definition lt_r_z r1 r2 z := encodeInstrW (Lt r1 (inr r2) (inl z)).
  Definition jmp r := encodeInstrW (Jmp r).
  Definition get_tag r1 r2 := encodeInstrW (GetTag r1 r2).
  Definition halt := encodeInstrW Halt.
  Definition fail_end := encodeInstrW Fail.


  (* encodings of return pointer permission pair *)
  Definition e := encodePerm E.
End instr_encodings.

(* Some additional helper lemmas about region_addrs *)

Definition region_addrs_zeroes (b e : Addr) : list Word :=
  replicate (finz.dist b e) (WInt 0%Z).

Lemma region_addrs_zeroes_lookup (b e : Addr) i y :
  region_addrs_zeroes b e !! i = Some y → y = WInt 0%Z.
Proof. apply lookup_replicate. Qed.

Lemma region_addrs_zeroes_split (b a e: Addr) :
  (b <= a)%a ∧ (a <= e)%a →
  region_addrs_zeroes b e = region_addrs_zeroes b a ++ region_addrs_zeroes a e.
Proof.
  intros. rewrite /region_addrs_zeroes.
  rewrite (finz_dist_split a). 2: solve_addr.
  rewrite replicate_add //.
Qed.
