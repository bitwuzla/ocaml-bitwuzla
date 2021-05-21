(lang dune 2.6)
(generate_opam_files true)

(name bitwuzla)
(version 0.0.0)
(maintainers "Frédéric Recoules <frederic.recoules@cea.fr>")
(authors "Frédéric Recoules")
(source (github  bitwuzla/ocaml-bitwuzla))
(license MIT)
(homepage "https://bitwuzla.github.io")
(bug_reports "https://github.com/bitwuzla/ocaml-bitwuzla/issues")

(package
 (name bitwuzla)
 (synopsis "SMT solver for QF_AUFBVFP")
 (description "
OCaml binding for the SMT solver Bitwuzla.

Bitwuzla is a Satisfiability Modulo Theories (SMT) solver for the theories of fixed-size bit-vectors, arrays and uninterpreted functions and their combinations. Its name is derived from an Austrian dialect expression that can be translated as “someone who tinkers with bits”.")
 (documentation "https://bitwuzla.github.io/docs/ocaml/")
 (depends
  (ocaml (>= 4.08))
  (conf-git :build)
  (conf-cmake :build)
  (conf-gcc :build)
  (conf-g++ :build)
   conf-gmp
  (ppx_expect :with-test))
 (depopts
   zarith)
 (tags
  ("SMT solver"
   "SMT-COMP 2020"
   "QF_AUFBVFP")))

(package
 (name bitwuzla-bin)
 (synopsis "Bitwuzla SMT solver executable")
 (description "
Standalone installer for the SMT solver Bitwuzla.

Bitwuzla is a Satisfiability Modulo Theories (SMT) solver for the theories of fixed-size bit-vectors, arrays and uninterpreted functions and their combinations. Its name is derived from an Austrian dialect expression that can be translated as “someone who tinkers with bits”.")
 (depends
  (conf-git :build)
  (conf-cmake :build)
  (conf-gcc :build)
  (conf-g++ :build)
  (conf-gmp :build))
 (tags
  ("SMT solver"
   "SMT-COMP 2020"
   "QF_AUFBVFP")))
