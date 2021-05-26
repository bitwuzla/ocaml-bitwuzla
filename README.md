[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![CI](https://github.com/bitwuzla/ocaml-bitwuzla/workflows/CI/badge.svg)

# ocaml-bitwuzla

[Bitwuzla](https://bitwuzla.github.io) is a Satisfiability Modulo Theories
(SMT) solvers for the theories of fixed-size bit-vectors, floating-point
arithmetic, arrays, uninterpreted functions and their combinations.

This library contains basic bindings for using Bitwuzla in OCaml code.
Bitwuzla sources and dependencies are repackaged for convenient use
with [*opam*](https://opam.ocaml.org/).

Online documentation is avaialbe at
https://bitwuzla.github.io/docs/ocaml.

## From Opam

```bash
opam install bitwuzla
```

## From source

The latest version of `ocaml-bitwuzla` is available on GitHub:
https://github.com/bitwuzla/ocaml-bitwuzla

---
:information_source: **Dealing with submodules**

In order to checkout the complete source tree,
run the following at `clone` time:
```bash
git clone --recurse-submodules git@github.com:bitwuzla/ocaml-bitwuzla.git
```
or at any time:
```bash
git submodule init # first time
git submodule update
```

:exclamation: **Temporary fix** : until the next release of
[Cadical](https://github.com/arminbiere/cadical),
the symlink [`vendor/cadical/src/makefile`](vendor/cadical/src/makefile)
should be manually removed (arminbiere/cadical#36).
```bash
rm vendor/cadical/src/makefile
```


:warning: **Do not** download the source archive (`.zip`, `.tar.gz`).
Download instead the
[tarball](https://github.com/bitwuzla/ocaml-bitwuzla/releases/download/0.0.1/bitwuzla-0.0.1.tbz) from release panel.
```bash
tar -xjf bitwuzla-0.0.1.tbz
```

### Dependencies

- [GMP v6.1 (GNU Multi-Precision arithmetic library)](https://gmplib.org)
  (**required**)
- [OCaml >= 4.08](https://github.com/ocaml/ocaml) (**required**)
- [dune >= 2.7](https://github.com/ocaml/dune) (**required**)
- [zarith](https://github.com/ocaml/Zarith) (*optional*)
- [odoc](https://github.com/ocaml/odoc) (*documentation*)
- [ppx_expect](https://github.com/janestreet/ppx_expect) (*tests*)

---
:information_source: **Handling dependencies with opam**

Dependencies can be automatically installed via
[*opam*](https://opam.ocaml.org/doc/Install.html).

```bash
opam pin add -n .                             # read the package definition
opam depext bitwuzla                          # install system dependencies
opam install --deps-only bitwuzla             # install OCaml dependencies
opam install --deps-only --with-doc bitwuzla  # optional, for documentation
opam install --deps-only --with-test bitwuzla # optional, for tests
```

### Build

```bash
dune build @install
```

#### Building the API documentation

```bash
dune build @doc
```

#### Running tests

```bash
dune build @runtest
```

:memo: No output is the expected behavior.
