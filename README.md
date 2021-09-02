This repository contains the Coq mechanization of a capability machine and
principles to reason about the interaction of known and unknown code.

We consider here a machine with so-called *sentry* (or "enter") capabilities on
top of the usual memory capabilities, and focus on reasoning about the
*local-state encapsulation* properties they can enforce.

We instantiate the Iris program logic to reason about programs running on the
machine, and we use it to define a logical relation characterizing the behavior
of unknown code. The logical relation is much simpler than what one would need
do reason about more complex stack-like properties: in particular, we only need
to rely on standard Iris invariants.


# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The simplest option is to create a fresh *local* opam switch with everything
needed, by running the following commands:

```
opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.11.2
eval $(opam env)
```

Consult the `opam` file for more information.

### Troubleshooting

If the `opam switch` invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y .` (this will continue from where it failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem.

# Documentation

An HTML rendering of the development can be browsed online at
[logsem.github.io/cerise/dev/](https://logsem.github.io/cerise/dev/) ([table of
contents](https://logsem.github.io/cerise/dev/toc.html)).

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

- `fundamental.v`: Establishes the *fundamental theorem of our logical
  relation*. Each case (one for each instruction) is proved in a separate file
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

- `call.v`, `callback.v`: A heap based calling convention: the calling convention 
   invokes `malloc` to dynamically allocate heap space, store the activation 
   record and the locals, and clear all non parameter and continuation registers. 

- `lse.v`: Example showing how one can reason on capabilities with a RO
  permission, and in particular obtain than their contents cannot change even
  after being shared with an adversary.

- *(TODO: detail the remaining newer examples)*
