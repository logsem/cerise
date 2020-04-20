From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants.
Import uPred.

Section heap.
  Context `{heapG Σ, memG Σ, regG Σ, STSG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (prodO STS STS).
  Implicit Types W : WORLD.


  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- Opening and closing static regions -------------------- *)

  (* cf region_invariants_revocation?

     three main lemmas:
     - one that opens all of a static region at once
     - one that closes what was a static region and turns it into a temporary one
     - one that turns a revoked region into a static region
   *)


End heap.
