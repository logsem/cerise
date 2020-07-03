This directory contains the Coq mechanization accompanying the submission Efficient and Provable Local Capability Revocation using Uninitialized Capabilities.

## Installation

The development has been built using:

- OCaml >= X.Y.Z
- Coq >= X.Y.Z
- Iris 3.2.0

These dependencies can be installed using [opam](https://opam.ocaml.org/).

    opam install coq.X.Y.Z
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install coq-iris.3.2.0

The development can then be compiled using `make -jN` where N is the number of threads to use.
Please be aware that the development may take up to 2h to compile depending on your computer.
In particular, the files `theories/examples/{awkward_example, awkward_example_u}.v` can each take up to 25 minutes to compile.

It is possible to use `make fundamental` (without `-jN`) instead that will only compile files up to the Fundamental Theorem, this can take up to only half an hour.

## Documentation

Documentation generated using Coqdoc can be created using `make html`. The html files will be available in the `html/` folder.

## Organization

The organization of the `theories/` folder is as follows.

- machine_base.v : Contains the syntax (permissions, capability, instructions, ...) of the capability machine.

- cap_lang.v : Contains the operational semantics, and the embedding of the capability machine language into Iris.

- rules_base.v : Contains some of the core resource algebras for the program logic, namely the definition for points to predicates with permissions. 

- rules.v : Imports all the hoare triple rules for each instruction. These rules are separated into separate files (located in the rules folder)

- region_invariants.v : Contains definitions for standard resources, and the shared resources map *sharedResources*. Contains some lemmas for "opening" and "closing" the map, akin to opening and closing invariants. 

- region_invariants_revocation.v : Contains lemmas for revoking standard resources (setting Temporary invariants to a Revoked state)

- region_invariants_static.v : Contains lemmas for manipulating frozen standard resources

- region_invariants_uninitialized.v : Contains lemmas for manipulating frozen standard singleton resources. These are specifically for manipulating the resources that are related to the interpretation of uninitialized capabilities. 

- sts.v : Contains the definition of *stsCollection*, and associated lemmas. 

- logrel.v : Contains the definition of the logical relation. 

- monotone.v : Contains the proofs for the monotonicity of the value relation with regards to public future worlds, and private future worlds for non local words. 

- fundamental.v : Contains *Theorem 6.1: fundamental theorem of logical relations*. Each case (one for each instruction) is proved in a separate file (located in the ftlr folder), which are all imported and applied in this file. 

In the examples folder: 

- stack_macros.v and stack_macros_u.v : Contain specifications for some useful macros, the former for a RWLX stack and the latter for a URWLX stack. 

- scall.v scall_u.v : Contain the specification of a safe calling convention for a RWLX and URWLX stack respectively. Each specification is split up into two parts: the prologue is the specification for the code before the jump, the epilogue is the specification for the activation record.

- malloc.v : Contains a malloc implementation, and its specification. 

- awkward_example.v awkward_example_u.v : Contain the proof of safety of the awkward example (the former using scall with stack clearing, the latter using scallU without stack clearing), *Lemma 6.2*. 

- awkward_example_preamble.v : Contains the proof of safety of the preamble to the awkward example (in which a closure to the awkward example is dynamically allocated)

- awkward_example_adequacy.v : Contains the proof of correctness of the awkward example, *Theorem 6.3*. 

- awkward_example_concrete.v : Contains a concrete run of the awkward example applied to a closure of itself to showcase reentrancy. The file contains a proof that the run gracefully halts. 

## Differences

Some definitions have different names from the paper.

*name in paper => name in mechanization*

In the operational semantics: 

- SingleStep => Instr Executable

- Done Standby => Instr NextI

- Done Halted => Instr Halted

- Done Failed => Instr Failed

- Repeat _ => Seq _

In the model:

- Frozen => Static

- stsCollection => full_sts_world

- sharedResources => region