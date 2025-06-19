This repository contains the Rocq mechanization accompanying the submission 
"Cerisier: A Program Logic for Attestation".
It provides a model of a capability machine with feature for local attestation and TEE,
and principles to reason about the interaction of known, unknown, and attested code.

The repository depends on the submodule `machine_utils`.
After cloning Cerisier, you can load the submodule using
```
git submodule update --init
```

# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.18.0, stdpp 1.9.0, and Iris 4.1.0. 
To install those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.14.0
eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.14.0:

```
    # Add the coq-released repo (skip if you already have it)
    opam repo add coq-released https://coq.inria.fr/opam/released
    # Install Coq 8.18.0 (skip if already installed)
    opam update
    opam install coq.8.18.0
    opam install coq-iris.4.1.0
```

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

<!-- # Documentation -->

<!-- An HTML rendering of the development can be browsed online at -->
<!-- [logsem.github.io/cerise/dev/](https://logsem.github.io/cerise/dev/). In -->
<!-- particular, the index page provides an overview of the organisation of the -->
<!-- formalization. -->

# Organization

| *section in the paper*            | *Rocq files*                                        |
|-----------------------------------|-----------------------------------------------------|
| Operational semantics (3)         | `machine_base.v`, `cap_lang.v`                      |
| Program Logic (4)                 | `logical_mapsto.v`, `rules/*.v`                     |
| Logical Relation (5)              | `logrel.v`, `ftlr/*.v`, `fundamental.v`             |
| Adequacy (6)                      | `examples/enclaves/template_adequacy_attestation.v` |
| Case Study - SOC (7.1)            | `examples/enclaves/trusted_compute_*.v`             |
| Case Study - Mutual Attest (7.2)  | `examples/enclaves/mutual_attestation_*.v`          |
| Case Study - Sensor Readout (7.2) | `examples/enclaves/trusted_memory_readout_*.v`      |

# Differences with the paper

Some definitions have different names from the paper.  

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper*   | *name in mechanization*   |
|-------------------|---------------------------|
| Executable        | Instr Executable          |
| Halted            | Instr Halted              |
| Failed            | Instr Failed              |

For technical reasons (so that Iris considers a single instruction as an atomic step), 
the execution mode is interweaved with the "Instr Next" mode, which reduces to a value.
The Seq _ context can then return and continue to the next instruction. The full expression 
for an executing program is Seq (Instr Executable).

In the program logic:

| *name in paper*     | *name in mechanization* |
|---------------------|-------------------------|
| EC(ecn)             | EC⤇ ecn                 |
| tidx ↦_{E}^{□} I    | enclave_all             |
| tidx ↦_{E} I        | enclave_cur             |
| DeInitialized(tidx) | enclave_prev            |
