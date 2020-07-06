This directory contains the Coq mechanization accompanying the submission
"Efficient and Provable Local Capability Revocation using Uninitialized
Capabilities".

# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.9.1 and Iris 3.2.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --deps-only --repositories=default,coq-released=https://coq.inria.fr/opam/released .
   eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.02.3 and < 4.10:

```
    # Add the coq-released repo (skip if you already have it)
    opam repo add coq-released https://coq.inria.fr/opam/released
    # Install Coq 8.9.1 (skip if already installed)
    opam install coq.8.9.1
    opam update
    opam install coq-iris.3.2.0
```

### Troubleshooting

For Option 1, if the invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y --deps-only .` (this will continue from where it
failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

We recommend that you have **32Gb of RAM+swap**. Please be aware that the
development takes around 1h to compile. In particular, the files
`theories/examples/awkward_example{,_u}.v` can each take up to 25 minutes to
compile.

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem. This usually takes up 20 minutes.

# Documentation

After building the development, documentation generated using Coqdoc can be
created using `make html`. 

Then, browse the `html/toc.html` file.

# Organization

The organization of the `theories/` folder is as follows.

## Operational semantics

- `addr_reg.v`: Defines registers and the set of (finite) memory addresses.

- `machine_base.v`: Contains the syntax (permissions, capability, instructions,
  ...) of the capability machine.

- `machine_parameters.v`: Defines a number of "settings" for the machine, that
  parameterize the whole development (e.g. the specific encoding scheme for
  instructions, etc.).

- `cap_lang.v`: Defines the operational semantics of the machine, and the
  embedding of the capability machine language into Iris.

- `machine_run.v`: Defines an executable version of the operational semantics,
  allowing to use them as an interpreter to run a concrete machine
  configuration.

## Program logic

- `monocmra.v`, `mono_ref.v`: Definition of monotonic references in Iris, used
  to define the points-to predicate for memory addresses.

- `region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `rules_base.v`: Contains some of the core resource algebras for the program
  logic, namely the definition for points to predicates with permissions.

- `rules.v`: Imports all the Hoare triple rules for each instruction. These
  rules are separated into separate files (located in the `rules/` folder).

## Logical relation

- `multiple_updates.v`: Auxiliary definitions to reason about multiple updates
  to a world.

- `region_invariants.v`: Definitions for standard resources, and the shared
  resources map *sharedResources*. Contains some lemmas for "opening" and
  "closing" the map, akin to opening and closing invariants.

- `region_invariants_revocation.v`: Lemmas for revoking standard resources
  (setting *Temporary* invariants to a *Revoked* state).

- `region_invariants_static.v`: Lemmas for manipulating frozen standard
  resources.

- `region_invariants_uninitialized.v`: Lemmas for manipulating frozen standard
  singleton resources. These are specifically for manipulating the resources
  that are related to the interpretation of uninitialized capabilities.

- `sts.v`: The definition of *stsCollection*, and associated lemmas.

- `logrel.v`: The definition of the logical relation.

- `monotone.v`: Proof of the monotonicity of the value relation with regards to
  public future worlds, and private future worlds for non local words.

- `fundamental.v`: Contains *Theorem 6.1: fundamental theorem of logical
  relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.

## Case studies

In the `examples` folder:

- `stack_macros.v` and `stack_macros_u.v`: Specifications for some useful
  macros, the former for a RWLX stack and the latter for a URWLX stack.

- `scall.v`, `scall_u.v`: Specification of a safe calling convention for a RWLX
  and URWLX stack respectively. Each specification is split up into two parts:
  the prologue is the specification for the code before the jump, the epilogue
  is the specification for the activation record.

- `malloc.v`: A simple malloc implementation, and its specification.

- `awkward_example.v`, `awkward_example_u.v`: The proof of safety of the awkward
  example (the former using scall with stack clearing, the latter using scallU
  without stack clearing), corresponding to *Lemma 6.2*.

- `awkward_example_preamble.v`: Proof of safety of the preamble to the awkward
  example (in which a closure to the awkward example is dynamically allocated).

- `awkward_example_adequacy.v`: Proof of correctness of the awkward example,
  *Theorem 6.3*.

- `awkward_example_concrete.v`: A concrete instantiation of the correctness
  theorem of the awkward example on a concrete machine, linked with a concrete
  "adversarial program". Then, we also prove that this concrete machine
  configurations indeed runs and gracefully halts.


# Differences with the paper

Some definitions have different names from the paper.

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper*   | *name in mechanization*   |
|-------------------|---------------------------|
| SingleStep        | Instr Executable          |
| Done Standby      | Instr NextI               |
| Done Halted       | Instr Halted              |
| Done Failed       | Instr Failed              |
| Repeat _          | Seq _                     |

In the model:

| *name in paper* | *name in mechanization* |
|-----------------|-------------------------|
| Frozen          | Static                  |
| stsCollection   | full_sts_world          |
| sharedResources | region                  |

In `scall.v` and `scall_u.v` : the scall macro is in both cases slightly unfolded, as it does not include the part of the calling convention which stores local state on the stack. That part is inlined into the awkward examples. 

In `awkward_example_u.v`: in the mechanized version of the awkward example (uninitialized version), we clear the local stack frame in two stages: before the second call, we clear the part of the frame which is frozen during the first call, but passed to the adversary during the second call (i.e. a single address at the top of the first local stack frame), and before retuning to the caller we clear the rest the local stack frame which is frozen during the second call.