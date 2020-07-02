From iris.proofmode Require Import tactics.
Require Import Eqdep_dec.
From cap_machine Require Import cap_lang machine_base.
From cap_machine.examples Require Import
     stack_macros malloc awkward_example_u awkward_example_preamble
     awkward_example_adequacy disjoint_regions_tactics.

Open Scope Addr_scope.
Notation "! x" := (^(z_to_addr x)%a) (at level 1).
Local Obligation Tactic := try done.

(* Encoders/decoders for instructions/perms using countable instances *)

Definition decodeInstr (z: Z): instr :=
  match z with
  | Zpos p =>
    match decode p with
    | Some i => i
    | None => Fail
    end
  | _ => Fail
  end.

Definition encodeInstr (i: instr): Z :=
  Zpos (encode i).

Definition encodePerm (p: Perm): Z :=
  Zpos (encode p).

Definition encodeLoc (l: Locality): Z :=
  Zpos (encode l).

Definition decodePermPair (z: Z): Perm * Locality :=
  match z with
  | Zpos p =>
    match decode p with
    | Some pl => pl
    | None => (O, Local) (* dummy *)
    end
  | _ => (O, Local)
  end.

Definition encodePermPair (pl: Perm * Locality): Z :=
  Zpos (encode pl).

Program Instance my_capability_machine : MachineParameters :=
  @Build_MachineParameters
    decodeInstr encodeInstr _
    encodePerm _ encodeLoc _
    decodePermPair encodePermPair _.
Next Obligation. intros. rewrite /decodeInstr /encodeInstr decode_encode //. Qed.
Next Obligation. intros. rewrite /decodePermPair /encodePermPair decode_encode //. Qed.

(* A simple concrete memory layout, with some hardcoded sizes *)
Program Instance my_concrete_layout : memory_layout :=
  let stack_size := 100%Z in
  let malloc_mem_size := 100%Z in
  let adv_size := 1000%Z in

  let awk_region_start := 0%Z in
  let awk_preamble_start := (awk_region_start + 1)%Z in
  let awk_body_start := (awk_preamble_start + awkward_preamble_instrs_length)%Z in
  let awk_region_end := (awk_body_start + awkward_example_u.awkward_instrs_length)%Z in
  let stack_start := awk_region_end in
  let stack_end := (awk_region_end + stack_size)%Z in
  let adv_start := stack_end in
  let adv_end := (adv_start + adv_size)%Z in
  let malloc_start := adv_end in
  let malloc_memptr := (malloc_start + length malloc_subroutine_instrs)%Z in
  let malloc_mem_start := (malloc_memptr + 1)%Z in
  let malloc_end := (malloc_mem_start + malloc_mem_size)%Z in
  let fail_start := malloc_end in
  let fail_end := (fail_start + length assert_fail_instrs + 1)%Z in
  let link_table_start := fail_end in
  let link_table_end := (link_table_start + 2)%Z in
  let fail_flag := link_table_end in
  let fail_flag_next := (fail_flag + 1)%Z in

  @Build_memory_layout
    _
    !awk_region_start
    !awk_preamble_start
    !awk_body_start
    !awk_region_end
    _ _ _
    !stack_start !stack_end
    !adv_start !adv_end
    !malloc_start !malloc_memptr !malloc_mem_start !malloc_end
    _ _ _
    !fail_start !fail_end _
    !link_table_start !link_table_end _
    !fail_flag !fail_flag_next _
    _.
Next Obligation. eapply addr_disjoint_list_cons; disj_regions. Qed.
(* FIXME: should be simply [disj_regions] *)

(* The stack is all zeroes but it could be anything *)
Definition stack_val := region_addrs_zeroes stack_start stack_end.

Definition my_initial_memory adv_val : gmap Addr Word :=
  mk_initial_memory adv_val stack_val.

Lemma my_initial_memory_correct adv_val:
  length adv_val = 1000 →
  Forall (λ w, is_cap w = false) adv_val →
  is_initial_memory (my_initial_memory adv_val).
Proof.
  intros Hlen ?. exists adv_val, stack_val. split. reflexivity.
  split. auto. split. rewrite Hlen; reflexivity.
  reflexivity.
Qed.

Definition my_initial_registers : gmap RegName Word :=
  <[PC := inr (RX, Global, awk_region_start, awk_region_end, awk_preamble_start)]>
  (<[r_stk := inr (URWLX, Local, stack_start, stack_end, stack_start)]>
  (<[r_t0 := inr (RWX, Global, adv_start, adv_end, adv_start)]>
  (list_to_map (map (λ r, (r, inl 0%Z)) all_registers)))).

Lemma my_initial_registers_correct : is_initial_registers my_initial_registers.
Proof.
  repeat split. intros r Hr. exists (inl 0%Z). repeat split.
  unfold my_initial_registers.
  do 3 (rewrite lookup_insert_ne; [|set_solver]).
  apply elem_of_list_to_map. cbn. apply all_registers_NoDup.
  generalize (all_registers_correct r).
  repeat (rewrite elem_of_cons; intros [->| H ]; [repeat constructor|revert H]).
  inversion 1.
Qed.

Theorem my_awkward_example_adequacy reg' m' es adv_code:
  length adv_code = 1000 →
  Forall (λ w, is_cap w = false) adv_code →
  rtc erased_step
      ([Seq (Instr Executable)], (my_initial_registers, my_initial_memory adv_code))
      (es, (reg', m')) →
  m' !! fail_flag = Some (inl 0%Z).
Proof.
  intros ? ?.
  apply awkward_example_adequacy.
  apply my_initial_memory_correct; auto.
  apply my_initial_registers_correct.
Qed.
