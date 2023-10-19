From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import rules_binary logrel_binary fundamental_binary.
From cap_machine.examples Require Import macros macros_binary macros_helpers malloc_binary counter_binary.
From stdpp Require Import countable.

Section counter_example_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  Definition counter_left_instrs :=
    incr_instrs ++ read_instrs.

  Definition counter_right_instrs :=
    decr_instrs ++ read_neg_instrs.

  Definition counter_left a :=
    ([∗ list] a_i;w ∈ a;counter_left_instrs, a_i ↦ₐ w )%I.

  Definition counter_right a :=
    ([∗ list] a_i;w ∈ a;counter_right_instrs, a_i ↣ₐ w )%I.

  Definition counter_left' a :=
    ([∗ list] a_i;w ∈ a;counter_right_instrs, a_i ↦ₐ w )%I.

  Definition counter_right' a :=
    ([∗ list] a_i;w ∈ a;counter_left_instrs, a_i ↣ₐ w )%I.

  Definition counter_left_instrs_length : Z :=
    Eval cbv in (length (counter_left_instrs)).
  Definition incr_instrs_length : Z :=
    Eval cbv in (length (incr_instrs)).
  Definition read_instrs_length : Z :=
    Eval cbv in (length (read_instrs)).

  Definition counter_right_instrs_length : Z :=
    Eval cbv in (length (counter_right_instrs)).
  Definition decr_instrs_length : Z :=
    Eval cbv in (length (decr_instrs)).
  Definition read_neg_instrs_length : Z :=
    Eval cbv in (length (read_neg_instrs)).

  Compute (counter_left_instrs_length = counter_right_instrs_length).

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_counter] is the offset between the [move_r r_t1 PC] instruction
  and the code of the implementation counter, which will be the concatenation of: incr;read *)
  Definition counter_left_preamble_instrs (f_m offset_to_counter: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
    move_r r_t2 r_t1;
    move_r r_t1 PC;
    move_r r_t8 r_t2; (* we keep a copy of the capability for the other closures *)
    move_r r_t9 r_t1; (* same for PC *)
    (* closure for incr *)
    lea_z r_t1 offset_to_counter] ++
    crtcls_instrs f_m ++
    [move_r r_t10 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for read *)
    lea_z r_t1 (offset_to_counter + incr_instrs_length)] ++
    crtcls_instrs f_m ++
    (* cleanup *)
    [move_r r_t2 r_t10;
    move_z r_t10 0;
    move_z r_t8 0;
    move_z r_t9 0;
    jmp r_t0].

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_counter] is the offset between the [move_r r_t1 PC] instruction
  and the code of the specification counter, which will be the concatenation of: decr;read_neg *)
  Definition counter_right_preamble_instrs (f_m offset_to_counter: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 0;
    move_r r_t2 r_t1;
    move_r r_t1 PC;
    move_r r_t8 r_t2; (* we keep a copy of the capability for the other closures *)
    move_r r_t9 r_t1; (* same for PC *)
    (* closure for incr *)
    lea_z r_t1 offset_to_counter] ++
    crtcls_instrs f_m ++
    [move_r r_t10 r_t1;
    move_r r_t2 r_t8;
    move_r r_t1 r_t9;
    (* closure for read *)
    lea_z r_t1 (offset_to_counter + decr_instrs_length)] ++
    crtcls_instrs f_m ++
    (* cleanup *)
    [move_r r_t2 r_t10;
    move_z r_t10 0;
    move_z r_t8 0;
    move_z r_t9 0;
    jmp r_t0].

  Definition counter_left_preamble f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_left_preamble_instrs f_m offset_to_counter), a_i ↦ₐ w_i)%I.
  Definition counter_right_preamble f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_right_preamble_instrs f_m offset_to_counter), a_i ↣ₐ w_i)%I.

  Definition counter_left_preamble' f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_right_preamble_instrs f_m offset_to_counter), a_i ↦ₐ w_i)%I.
  Definition counter_right_preamble' f_m offset_to_counter ai :=
    ([∗ list] a_i;w_i ∈ ai;(counter_left_preamble_instrs f_m offset_to_counter), a_i ↣ₐ w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_awkward]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  (* The two preambles have the same number of instructions, so we can here use the same value
     to calculate the offset *)
  Definition counter_preamble_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := counter_left_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, counter_left_preamble_instrs.
      (* Program-specific part *)
      eapply step_app.
      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- move_r r_t1 PC :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition counter_preamble_move_offset : Z :=
    Eval cbv in counter_preamble_move_offset_.

  Definition counter_preamble_instrs_length : Z :=
    Eval cbv in (length (counter_left_preamble_instrs 0 0)).


  (* The following two lemmas show that the created closures are valid *)

  Definition cls_inv b_cls e_cls b_cls' e_cls' pc1 pc2 c1 pcs1 pcs2 c2 : iProp Σ :=
    ([[b_cls,e_cls]]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pc1; c1] ]]
     ∗ [[b_cls',e_cls']]↦ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pc2; c1] ]]
     ∗ [[b_cls,e_cls]]↣ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pcs1; c2] ]]
     ∗ [[b_cls',e_cls']]↣ₐ[[ [WInt v1; WInt v2; WInt v3; WInt v4; WInt v5; WInt v6; pcs2; c2] ]])%I.

End counter_example_preamble.
