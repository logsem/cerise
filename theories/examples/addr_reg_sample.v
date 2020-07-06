From Coq Require Import Eqdep_dec.
From stdpp Require Import gmap fin_maps list.
From iris.proofmode Require Import tactics.
From cap_machine Require Export addr_reg cap_lang region.

(* Some addresses *)
Notation "a- z" := (A z eq_refl) (at level 10, format "a- z").

(* Some general purpuse registers *)
Definition r_t0 : RegName := R 0 eq_refl.
Definition r_t1 : RegName := R 1 eq_refl.
Definition r_t2 : RegName := R 2 eq_refl.
Definition r_t3 : RegName := R 3 eq_refl.
Definition r_t4 : RegName := R 4 eq_refl.
Definition r_t5 : RegName := R 5 eq_refl.
Definition r_t6 : RegName := R 6 eq_refl.
Definition r_t7 : RegName := R 7 eq_refl.
Definition r_t8 : RegName := R 8 eq_refl.
Definition r_t9 : RegName := R 9 eq_refl.
Definition r_t10 : RegName := R 10 eq_refl.
Definition r_t11 : RegName := R 11 eq_refl.
Definition r_t12 : RegName := R 12 eq_refl.
Definition r_t13 : RegName := R 13 eq_refl.
Definition r_t14 : RegName := R 14 eq_refl.
Definition r_t15 : RegName := R 15 eq_refl.
Definition r_t16 : RegName := R 16 eq_refl.
Definition r_t17 : RegName := R 17 eq_refl.
Definition r_t18 : RegName := R 18 eq_refl.
Definition r_t19 : RegName := R 19 eq_refl.
Definition r_t20 : RegName := R 20 eq_refl.
Definition r_t21 : RegName := R 21 eq_refl.
Definition r_t22 : RegName := R 22 eq_refl.
Definition r_t23 : RegName := R 23 eq_refl.
Definition r_t24 : RegName := R 24 eq_refl.
Definition r_t25 : RegName := R 25 eq_refl.
Definition r_t26 : RegName := R 26 eq_refl.
Definition r_t27 : RegName := R 27 eq_refl.
Definition r_t28 : RegName := R 28 eq_refl.
Definition r_t29 : RegName := R 29 eq_refl.
Definition r_t30 : RegName := R 30 eq_refl.
Definition r_t31 : RegName := R 31 eq_refl.

(* A list of all general purpuse registers (if regnum=31) *)
Definition all_registers : list RegName :=
  [r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6;r_t7;r_t8;r_t9;r_t10;r_t11;r_t12;r_t13;
     r_t14;r_t15;r_t16;r_t17;r_t18;r_t19;r_t20;r_t21;r_t22;r_t23;r_t24;r_t25;r_t26;
       r_t27;r_t28;r_t29;r_t30;r_t31;PC].

Definition all_registers_s : gset RegName := list_to_set all_registers.

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
  Definition w_4b_U := encodeInstr (LoadU PC r_stk (inr r_t1)).
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
  Definition getl r1 r2 := encodeInstrW (GetL r1 r2).
  Definition getp r1 r2 := encodeInstrW (GetP r1 r2).
  Definition add_r_z r1 r2 z := encodeInstrW (Add r1 (inr r2) (inl z)).
  Definition sub_r_r r1 r2 r3 := encodeInstrW (Sub r1 (inr r2) (inr r3)).
  Definition sub_r_z r1 r2 z := encodeInstrW (Sub r1 (inr r2) (inl z)).
  Definition sub_z_r r1 z r2 := encodeInstrW (Sub r1 (inl z) (inr r2)).
  Definition sub_z_z r z1 z2 := encodeInstrW (Sub r (inl z1) (inl z2)).
  Definition subseg_r_r r1 r2 r3 := encodeInstrW (Subseg r1 (inr r2) (inr r3)).
  Definition jnz r1 r2 := encodeInstrW (Jnz r1 r2).
  Definition lt_r_r r1 r2 r3 := encodeInstrW (Lt r1 (inr r2) (inr r3)).
  Definition lt_z_r r1 z r2 := encodeInstrW (Lt r1 (inl z) (inr r2)).
  Definition jmp r := encodeInstrW (Jmp r).
  Definition halt := encodeInstrW Halt.
  Definition fail_end := encodeInstrW Fail.

  (* instructions for U-rules *)
  Definition storeU_z_r r1 z r2 := encodeInstrW (StoreU r1 (inl z) (inr r2)).
  Definition storeU_z_z r z1 z2 := encodeInstrW (StoreU r (inl z1) (inl z2)).
  Definition loadU_r_z r1 r2 z := encodeInstrW (LoadU r1 r2 (inl z)).
  Definition promoteU r := encodeInstrW (PromoteU r).

  (* encodings of return pointer permission pair *)
  Definition local_e := encodePermPair (E, Local).
  (* encodings of enter capability permission pair *)
  Definition global_e := encodePermPair (E, Global).
End instr_encodings.

Lemma all_registers_NoDup :
  NoDup all_registers.
Proof.
  rewrite /all_registers.
  repeat (
    apply NoDup_cons_2;
    first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
  ).
  by apply NoDup_nil.
Qed.

(* helper lemmas for the list of all registers *)

(* a typical helper lemma for stack calls *)
(* TODO: is this still necessary? *)
Lemma helper1 r1 :
   r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 →
   r1 ∈ all_registers →
   length (list_difference all_registers [PC; r_stk; r_t0; r1]) = 29.
Proof.
  intros (Hne1 & Hne2 & Hne3) Hr1.
  assert ([PC; r_stk; r_t0; r1] = [PC; r_stk; r_t0] ++ [r1]); first done.
  rewrite H.
  rewrite list_difference_app.
  assert (r1 ∈ (list_difference all_registers [PC; r_stk; r_t0])).
  { simpl.
    rewrite /all_registers in Hr1.
    apply elem_of_cons in Hr1 as [Hcontr | Hr1]; first contradiction.
    assert
    ([r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
       r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
       r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30; r_t31; PC] =
    [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6; r_t7; r_t8; r_t9; r_t10; r_t11;
       r_t12; r_t13; r_t14; r_t15; r_t16; r_t17; r_t18; r_t19; r_t20; r_t21; r_t22;
       r_t23; r_t24; r_t25; r_t26; r_t27; r_t28; r_t29; r_t30] ++ [r_t31; PC]); auto.
    rewrite H0 in Hr1. clear H0.
    apply elem_of_app in Hr1 as [Hr1 | Hcontr]; auto.
    apply elem_of_cons in Hcontr as [? | Hcontr]; first contradiction.
    apply elem_of_list_singleton in Hcontr; contradiction.
  }
  rewrite list_difference_length; auto.
  apply NoDup_list_difference, all_registers_NoDup.
Qed.

(* Spec for all_registers *)

Lemma all_registers_correct r1 :
  r1 ∈ all_registers.
Proof.
  rewrite /all_registers.
  destruct r1.
  - do 32 (apply elem_of_cons; right).
      by apply elem_of_list_singleton.
  - induction n.
    + apply elem_of_cons; left.
      apply f_equal. apply eq_proofs_unicity. decide equality.
    + apply elem_of_list_lookup_2 with (S n).
      repeat (destruct n;
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
      simpl in *. inversion fin.
Qed.

Lemma all_registers_s_correct r:
  r ∈ all_registers_s.
Proof.
  rewrite /all_registers_s elem_of_list_to_set.
  apply all_registers_correct.
Qed.

Lemma all_registers_union_l s :
  s ∪ all_registers_s = all_registers_s.
Proof.
  eapply (anti_symm _). 2: set_solver.
  rewrite elem_of_subseteq. intros ? _.
  apply all_registers_s_correct.
Qed.

Lemma all_registers_union_r s :
  all_registers_s ∪ s = all_registers_s.
Proof. rewrite union_comm_L. apply all_registers_union_l. Qed.

Lemma all_registers_subseteq s :
  s ⊆ all_registers_s.
Proof.
  rewrite elem_of_subseteq. intros ? _. apply all_registers_s_correct.
Qed.

Lemma regmap_full_dom (r: gmap RegName Word):
  (∀ x, is_Some (r !! x)) →
  dom (gset RegName) r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm _); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite -elem_of_gmap_dom. apply Hfull.
Qed.

(* Some additional helper lemmas about region_addrs *)

Definition region_addrs_zeroes (b e : Addr) : list Word :=
  replicate (region_size b e) (inl 0%Z).

Lemma region_addrs_zeroes_lookup (b e : Addr) i y :
  region_addrs_zeroes b e !! i = Some y → y = inl 0%Z.
Proof. apply lookup_replicate. Qed.

Lemma region_addrs_zeroes_split (b a e: Addr) :
  (b <= a)%a ∧ (a <= e)%a →
  region_addrs_zeroes b e = region_addrs_zeroes b a ++ region_addrs_zeroes a e.
Proof.
  intros. rewrite /region_addrs_zeroes.
  rewrite (region_size_split a). 2: solve_addr.
  rewrite replicate_plus //.
Qed.
