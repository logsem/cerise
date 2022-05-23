From iris.algebra Require Import auth agree excl gmap gset frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental.
From cap_machine.examples Require Import addr_reg_sample safe_malloc assert.
From cap_machine.examples Require Export mkregion_helpers disjoint_regions_tactics.
From cap_machine.examples Require Import template_adequacy_concurrency.

Section ocpl.

Record ocpl_library `{MachineParameters} := MkOcplLibrary {
  (* malloc library *)
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

  (* assert library *)
  assert_start : Addr;
  assert_cap : Addr;
  assert_flag : Addr;
  assert_end : Addr;

  assert_code_size :
    (assert_start + length assert_subroutine_instrs)%a = Some assert_cap;
  assert_cap_size :
    (assert_cap + 1)%a = Some assert_flag;
  assert_flag_size :
    (assert_flag + 1)%a = Some assert_end;

  (* disjointness of the two libraries *)
  libs_disjoint : ## [
      finz.seq_between assert_start assert_end;
      finz.seq_between malloc_mem_start malloc_end;
      [malloc_memptr];
      finz.seq_between malloc_start malloc_memptr
     ]
}.

Definition malloc_library_content `{MachineParameters} (layout : ocpl_library) : gmap Addr Word :=
  (* code for the malloc subroutine *)
  mkregion (malloc_start layout) (malloc_memptr layout) malloc_subroutine_instrs
  (* Capability to malloc's memory pool, used by the malloc subroutine *)
  ∪ list_to_map [((malloc_memptr layout), WCap RWX (malloc_memptr layout) (malloc_end layout) (malloc_mem_start layout))]
  (* Malloc's memory pool, initialized to zero *)
  ∪ mkregion (malloc_mem_start layout) (malloc_end layout) (region_addrs_zeroes (malloc_mem_start layout) (malloc_end layout)).

Definition lib_entry_malloc `{MachineParameters} (layout : ocpl_library) : lib_entry :=
  {| lib_start := malloc_start layout;
     lib_end := malloc_end layout;
     lib_entrypoint := malloc_start layout;
     lib_full_content := malloc_library_content layout|}.

(* assert library entry *)
Definition assert_library_content `{MachineParameters} (layout : ocpl_library) : gmap Addr Word :=
  (* code for the assert subroutine, followed by a capability to the assert flag
     and the flag itself, initialized to 0. *)
  mkregion (assert_start layout) (assert_cap layout) assert_subroutine_instrs
  ∪ list_to_map [(assert_cap layout, WCap RW (assert_flag layout) (assert_end layout) (assert_flag layout))]
  ∪ list_to_map [(assert_flag layout, WInt 0)] (* assert flag *).

Definition lib_entry_assert `{MachineParameters} (layout : ocpl_library) : lib_entry :=
  {| lib_start := assert_start layout;
     lib_end := assert_end layout;
     lib_entrypoint := assert_start layout;
     lib_full_content := assert_library_content layout |}.

(* full library *)
Definition library `{MachineParameters} (layout : ocpl_library) : lib :=
  {| priv_libs := [lib_entry_assert layout] ;
     pub_libs := [lib_entry_malloc layout] |}.

Definition assertInv `{memG Σ, regG Σ, MachineParameters} (layout : ocpl_library) :=
  assert_inv (assert_start layout) (assert_flag layout) (assert_end layout).
Definition mallocInv `{memG Σ, regG Σ,static_spinlock.lockG Σ, MachineParameters}
  (layout : ocpl_library) γ :=
  malloc_inv (malloc_start layout) (malloc_end layout) γ.
End ocpl.
