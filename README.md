This repository contains the Coq mechanization of a capability machine and
principles to reason about the interaction of known and unknown code.

The repository depends on the submodule `machine_utils`. After cloning Cerise,
you can load the submodule using
```
git submodule update --init
```

We consider here a machine with so-called *sentry* (or "enter") capabilities on
top of the usual memory capabilities, and focus on reasoning about the
*local-state encapsulation* properties they can enforce.

We instantiate the Iris program logic to reason about programs running on the
machine, and we use it to define a logical relation characterizing the behavior
of unknown code. The logical relation is much simpler than what one would need
do reason about more complex stack-like properties: in particular, we only need
to rely on standard Iris invariants.

For more information, see this [extended
article](https://cs.au.dk/~birke/papers/cerise.pdf) which provides a pedagogical
but thorough overview of the work (currently submitted for publication).

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
[logsem.github.io/cerise/dev/](https://logsem.github.io/cerise/dev/). In
particular, the index page provides an overview of the organisation of the
formalization.
