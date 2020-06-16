From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import
     region_macros malloc awkward_example awkward_example_preamble.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout := {
  (* awkward example: preamble & body *)
  awk_region_start : Addr;
  awk_region_end : Addr;

  awk_region_size :
    (awk_region_start
     + (1 (* pointer to the linking table *)
        + awkward_preamble_instrs_length (* preamble instructions *)
        + awkward_instrs_length (* closure body instructions *))
    )%a
    = Some awk_region_end;

  (* malloc routine *)
  malloc_start : Addr;
  malloc_end : Addr;

  (* fail routine *)
  fail_start : Addr;
  fail_end : Addr;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [region_addrs awk_region_start awk_region_end;
        region_addrs malloc_start malloc_end;
        region_addrs fail_start fail_end;
        region_addrs link_table_start link_table_end];
}.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (region_addrs r_start r_end) contents).

Definition initial_memory_spec `{memory_layout} (m m_adv: gmap Addr Word) :=
  m =   mkregion awk_region_start awk_region_end
          ((* pointer to the linking table *)
           [inr (RW, Global, link_table_start, link_table_end, link_table_start)] ++
           (* preamble: code that creates the awkward example closure *)
           awkward_preamble_instrs 0%Z (* offset to malloc in linking table *)
             0%Z (* ?? *) ++
           (* body of the awkward example, that will be encapsulated in the closure
              created by the preamble *)
           awkward_instrs r_t0 (* ?? *) 0%Z (* ?? *))
      ∪ mkregion malloc_start malloc_end malloc_subroutine
      ∪ m_adv
  ∧
  (∀ a w, m_adv !! a = Some w → is_cap w = false).
