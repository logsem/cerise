From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample malloc macros_new lse.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Import with_adv.

Class memory_layout `{MachineParameters} := {
  (* Code of f *)
  f_region_start : Addr;
  f_start : Addr;
  f_end : Addr;
  f_size: (f_start + (length (roe_instrs 0 1 r_adv)) = Some f_end)%a;
  f_region_start_offset: (f_region_start + 1)%a = Some f_start;

  (* adversary code *)
  adv_start : Addr;
  adv_end : Addr;
  adv_instrs : list Word;
  adv_size : (adv_start + (length adv_instrs) = Some adv_end)%a ;

  (* malloc routine *)
  malloc_start : Addr;
  malloc_memptr : Addr;
  malloc_mem_start : Addr;
  malloc_end : Addr;

  malloc_code_size :
    (malloc_start + length malloc_subroutine_instrs)%a
    = Some malloc_memptr;

  malloc_memptr_size :
    (malloc_memptr + 1)%a = Some malloc_mem_start;

  malloc_mem_size :
    (malloc_mem_start <= malloc_end)%a;

  (* fail routine *)
  fail_start : Addr;
  fail_end : Addr;

  fail_size :
    (fail_start
     + (length assert_fail_instrs (* code of the subroutine *)
        + 1 (* pointer to the flag *))
    )%a
    = Some fail_end;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* failure flag *)
  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        region_addrs adv_start adv_end;
        region_addrs f_start f_end;
        [fail_flag];
        region_addrs link_table_start link_table_end;
        region_addrs fail_start fail_end;
        region_addrs malloc_mem_start malloc_end;
        [malloc_memptr];
        region_addrs malloc_start malloc_memptr
       ]
}.

Definition mk_initial_memory `{memory_layout} : gmap Addr Word :=
    mkregion f_start f_end (roe_instrs 0 1 r_adv)
  ∪ mkregion adv_start adv_end adv_instrs
  ∪ mkregion 


Definition roe_prog `{MachineParameters} `{memory_layout} : prog :=
  {| prog_start := f_start ;
     prog_end := f_end ;
     prog_instrs := (roe_instrs 0 1 r_adv) ;
     prog_size := f_size |}.

Definition adv_prog `{MachineParameters} `{memory_layout} : prog :=
  {| prog_start := adv_start ;
     prog_end := adv_end ;
     prog_instrs := adv_instrs ;
     prog_size := adv_size |}.


Definition OK_invariant `{MachineParameters} `{memory_layout} (m : gmap Addr Word) : Prop :=
  ∀ w, m !! fail_flag = Some w → w = WInt 0%Z.

Definition OK_dom `{MachineParameters} `{memory_layout} : gset Addr := {[ fail_flag ]}.

Program Definition OK_dom_correct `{MachineParameters} `{memory_layout} :
  ∀ m m',
    (∀ a, a ∈ OK_dom → ∃ x, m !! a = Some x ∧ m' !! a = Some x) →
    OK_invariant m ↔ OK_invariant m'.
Proof.
  intros m m' Hdom.
  destruct Hdom with fail_flag as [w [Hw1 Hw2] ]. set_solver.
  split;intros HOK;intros w' Hw';simplify_eq;apply HOK;auto.
Defined.

Definition flag_inv `{MachineParameters} `{memory_layout} : memory_inv :=
  {| minv := OK_invariant ;
     minv_dom := {[ fail_flag ]} ;
     minv_dom_correct := OK_dom_correct |}.
