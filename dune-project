(lang dune 3.7)
(generate_opam_files true)

(name bitwuzla-cxx)
(version 0.2.0)
(maintainers "Frédéric Recoules <frederic.recoules@cea.fr>")
(authors "Frédéric Recoules")
(source (github  bitwuzla/ocaml-bitwuzla))
(license MIT)
(homepage "https://bitwuzla.github.io")
(bug_reports "https://github.com/bitwuzla/ocaml-bitwuzla/issues")

(package
 (name bitwuzla-cxx)
 (synopsis "SMT solver for AUFBVFP (C++ API)")
 (description "
OCaml binding for the SMT solver Bitwuzla C++ API.

Bitwuzla is a Satisfiability Modulo Theories (SMT) solver for the theories of fixed-size bit-vectors, arrays and uninterpreted functions and their combinations. Its name is derived from an Austrian dialect expression that can be translated as “someone who tinkers with bits”.")
 (documentation "https://bitwuzla.github.io/docs/ocaml/")
 (depends
  (ocaml (>= 4.12))
  (conf-git :build)
  (conf-gcc :build)
  (conf-g++ :build)
  zarith
  (ppx_inline_test (and :with-test (>= v0.13)))
  (ppx_expect (and :with-test (>= v0.13))))
 (tags
  ("SMT solver"
   "AUFBVFP")))