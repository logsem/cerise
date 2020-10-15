This repository contains the Coq mechanization of a capability machine and
principles to reason about the interaction of known and unknown code.

We consider here a machine with "enter" capabilities on top of the usual memory
capabilities, and focus on reasoning about the *local-state encapsulation*
properties they can enforce.

Enter capabilities are similar to CHERI "sealed" capabilities; they correspond
to a specific usage mode of sealed capabilities in combination with the CCall
instruction.

We instantiate the Iris program logic to reason about programs running on the
machine, and we use it to define a logical relation characterizing the behavior
of unknown code. The logical relation is much simpler than what one would need
do reason about more complex stack-like properties: in particular, we only need
to rely on standard Iris invariants.


# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.9.1 and Iris 3.2.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.08.1
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
env)` and then `opam install -y .` (this will continue from where it failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem. This usually takes up 20 minutes.

# Documentation

After building the development, documentation generated using Coqdoc can be
created using `make html`. 

Then, browse the `html/toc.html` file.

Note that we have included a copy of the generated html files as a supplemental material. 

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

- `region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `rules/rules_base.v`: Contains some of the core resource algebras for the
  program logic, namely the definition for points to predicates with
  permissions.

- `rules/rules.v`: Imports all the Hoare triple rules for each instruction.
  These rules are separated into separate files (located in the `rules/`
  folder).

## Logical relation

- `logrel.v`: The definition of the logical relation.

- `fundamental.v`: Contains *Theorem 6.1: fundamental theorem of logical
  relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.

## Case studies

In the `examples` folder:

- `macros.v`: Some useful macros and their proof (in particular, the `crtcls`
  macro used to implement closures).

- `adder.v`, `adder_adequacy.v`: Simple example, detailed in the JFLA
  submission. Exposes one closure that enables increasing the value of a
  reference. The first file proves a separation-logic specification for the
  system, and the "adequacy" file extracts it into a self-contained statement
  depending only on the operational semantics.

- `malloc.v`: A simple malloc implementation, and its proof.

- `counter.v`, `counter_preamble.v`, `counter_adequacy.v`: A counter, with an
  increment, read, and reset closure. Relies on the malloc routine to allocate
  its memory, and an "assert" routine to signal failure.
  (which we then prove cannot happen)

- `call.v`, `callback.v`: ?

- `lse.v`: Example showing how one can reason on capabilities with a RO
  permission, and in particular obtain than their contents cannot change even
  after being shared with an adversary.


# Differences with the paper

Some definitions have different names than on paper.

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper*   | *name in mechanization*   |
|-------------------|---------------------------|
| SingleStep        | Instr Executable          |
| Done Standby      | Instr NextI               |
| Done Halted       | Instr Halted              |
| Done Failed       | Instr Failed              |
| Repeat _          | Seq _                     |
