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

The development can then be compiled using `make coq -jN` where N is the number of threads to use.
Please be aware that the development is known to take up to 2h to compile.
In particular, the files `theories/examples/{awkward_example, awkward_example_u}.v` can each take up to 25 minutes to compile.

## Organization

TODO: describe the organization of the files wrt. paper, e.g., file `foo.v` contains theorem Bar of the paper.


