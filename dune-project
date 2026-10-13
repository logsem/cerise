(lang dune 3.21)
(using rocq 0.11)

(name cerise)

(generate_opam_files false)

(license BSD-3-Clause)

(package
 (name cerise)
 (synopsis "Cerise")
 (description "Rocq mechanization of a capability machine and principles to reason about the interaction of known and unknown code")
 (depends ocaml dune rocq-iris rocq-equations)
 (tags
  (Rocq "capability machine" Iris)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
