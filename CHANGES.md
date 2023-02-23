## 1.0.5 (2023-02-23)

- Enable macOS Homebrew distribution

## 1.0.4 (2023-02-14)

- Fix an [issue](https://github.com/bitwuzla/bitwuzla/issues/40)
  with `get_value` and `assignment` when the term is an `array`
  or a `function` 

## 1.0.3 (2022-08-30)

Update [Bitwuzla](https://bitwuzla.github.io/) sources.

Vendor submodules:
- [Bitwuzla](https://github.com/bitwuzla/bitwuzla) commit:a2c3cc2

## 1.0.2 (2022-06-16)

Update [Bitwuzla](https://bitwuzla.github.io/) and its dependencies
to more recent versions.

Vendor submodules:
- [Cadical](https://github.com/arminbiere/cadical) tag:rel-1.5.2
- [Btor2Tools](https://github.com/Boolector/btor2tools) commit:db46e96
- [Bitwuzla](https://github.com/bitwuzla/bitwuzla) commit:19dd987

## 1.0.1 (2021-12-20)

- Fix `timeout` function not working properly

- Decrease default model generation level (`2` -> `1`)

## 1.0.0 (2021-07-11)

Brand new `Bitwuzla` OCaml API in addition the low level `Bitwuzla_c` C API.

Online documentation is available at https://bitwuzla.github.io/docs/ocaml/.

- `bitwuzla-c` package installs [C API](https://bitwuzla.github.io/docs/c/interface.html) binding;
- `bitwuzla` package installs more OCaml-ish, type safer Bitwuzla API.

Vendor submodules:
- [Cadical](https://github.com/arminbiere/cadical) tag:rel-1.4.1
- [SymFPU](https://github.com/martin-cs/symfpu) commit:8fbe139
- [Btor2Tools](https://github.com/Boolector/btor2tools) commit:6ba194b
- [Bitwuzla](https://github.com/bitwuzla/bitwuzla) commit:58d7205

## 0.0.1 (2021-05-24)

- Fix compilation errors on non debian familly os:

    - Remove `bitwuzla-bin` package
      (it required non always available `static` version of system libraries)
    - Completely rework the building rules of foreign archives
      (side effect: drop `conf-cmake` dependency)
    - Fix Cadical compilation on `archlinux`

- Upgrade `dune` to 2.7 (fix opam lint warning)

## 0.0.0 (2021-05-20)

Initial release.

OCaml binding for the SMT solver [Bitwuzla](https://bitwuzla.github.io/).

- `Bitwuzla_c` library exposes low level functions from the
  [C API](https://bitwuzla.github.io/docs/c/interface.html);
- `Bitwuzla_z` library converts bitvector value to
  [Zarith](https://github.com/ocaml/Zarith) integer;
- `bitwuzla-bin` package installs Bitwuzla executable.

Vendor submodules:
- [Cadical](https://github.com/arminbiere/cadical) tag:sc2021
- [SymFPU](https://github.com/martin-cs/symfpu) commit:8fbe139
- [Btor2Tools](https://github.com/Boolector/btor2tools) commit:1df768d
- [Bitwuzla](https://github.com/bitwuzla/bitwuzla) commit:2f4dad6
