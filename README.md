[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![CI](https://github.com/bitwuzla/ocaml-bitwuzla/workflows/CI/badge.svg)

# ocaml-bitwuzla

[Bitwuzla](https://bitwuzla.github.io) is a Satisfiability Modulo Theories
(SMT) solvers for the theories of fixed-size bit-vectors, floating-point
arithmetic, arrays, uninterpreted functions and their combinations.

This library provides an API for using Bitwuzla in OCaml code.
Online documentation is available at
https://bitwuzla.github.io/docs/ocaml.

### Quickstart

First, create a `Options` instance:
```ocaml
let options = Options.default () in
```

This instance can be configured via `Options.set`. For example, to enable model generation (SMT-LIB: (set-option :produce-models true)):
```ocaml
Options.set options Produce_models true;
```

Then, create a Bitwuzla instance (configuration options are now frozen and cannot be changed for this instance):
```ocaml
let bitwuzla = Solver.create options in
```

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:
```smt2
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-fun f ((_ BitVec 8) (_ BitVec 4)) (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert
    (distinct
        ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
        ((_ extract 3 0) (bvashr y (_ bv1 8)))))
(assert (= (f x ((_ extract 6 3) x)) y))
(assert (= (select a x) y))
(check-sat)
(get-model)
(get-value (x y f a (bvmul x x)))
(exit)
```

This input is created and asserted as follows:

```ocaml
  (* Create bit-vector sorts of size 4 and 8. *)
  let sortbv4 = mk_bv_sort 4 and sortbv8 = mk_bv_sort 8 in
  (* Create function sort. *)
  let sortfun = mk_fun_sort [| sortbv8; sortbv4 |] sortbv8 in
  (* Create array sort. *)
  let sortarr = mk_array_sort sortbv8 sortbv8 in

  (* Create two bit-vector constants of that sort. *)
  let x = mk_const sortbv8 ~symbol:"x" and y = mk_const sortbv8 ~symbol:"y" in
  (* Create fun const. *)
  let f = mk_const sortfun ~symbol:"f" in
  (* Create array const. *)
  let a = mk_const sortarr ~symbol:"a" in

  (* Create bit-vector values one and two of the same sort. *)
  let one = mk_bv_one sortbv8 in
  (* Alternatively, you can create bit-vector value one with: *)
  (* let one = mk_bv_value sortbv8 "1" 2 in *)
  (* let one = mk_bv_value_int sortbv8 1 in *)
  let two = mk_bv_value_int sortbv8 2 in

  (* (bvsdiv x (_ bv2 8)) *)
  let sdiv = mk_term2 Bv_sdiv x two in
  (* (bvashr y (_ bv1 8)) *)
  let ashr = mk_term2 Bv_ashr y one in
  (* ((_ extract 3 0) (bvsdiv x (_ bv2 8))) *)
  let sdive = mk_term1_indexed2 Bv_extract sdiv 3 0 in
  (* ((_ extract 3 0) (bvashr x (_ bv1 8))) *)
  let ashre = mk_term1_indexed2 Bv_extract ashr 3 0 in

  (* (assert *)
  (*     (distinct *)
  (*         ((_ extract 3 0) (bvsdiv x (_ bv2 8))) *)
  (*         ((_ extract 3 0) (bvashr y (_ bv1 8))))) *)
  Solver.assert_formula bitwuzla (mk_term2 Distinct sdive ashre);
  (* (assert (= (f x ((_ extract 6 3) x)) y)) *)
  Solver.assert_formula bitwuzla
    (mk_term2 Equal (mk_term3 Apply f x (mk_term1_indexed2 Bv_extract x 6 3)) y);
  (* (assert (= (select a x) y)) *)
  Solver.assert_formula bitwuzla (mk_term2 Equal (mk_term2 Select a x) y);
```

After asserting formulas, satisfiability can be determined via
`check_sat`.
```ocaml
  let result = Solver.check_sat bitwuzla in
```

If the formula is satisfiable and model generation has been enabled, the resulting model can be printed via `Solver.get_value` and `Term.pp`. An example implementation illustrating how to print the current model via declared symbols (in this case `x`, `y`, `f` and `a`) is below:
```ocaml
  Format.open_vbox 0;
  Format.printf "Expect: sat@,";
  Format.printf "Bitwuzla: %s@," (Result.to_string result);
  Format.print_space ();

  (* Print model in SMT-LIBv2 format. *)
  Format.printf "@[<v>Model:@,@[<v 2>(@,%a@]@,)@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space (fun ppf term ->
         let sort = Term.sort term in
         Format.fprintf ppf "(define-fun %a ("
           (fun ppf term ->
             try Format.pp_print_string ppf (Term.symbol term)
             with Not_found -> Format.fprintf ppf "%@t%Ld" (Term.id term))
           term;
         if Sort.is_fun sort then (
           let value = Solver.get_value bitwuzla term in
           assert (Term.kind value = Lambda);
           assert (Term.num_children value = 2);
           let rec unroll value =
             let value1 = Term.get value 1 in
             if Term.kind value1 = Lambda then (
               let value0 = Term.get value 0 in
               assert (Term.is_variable value0);
               Format.fprintf ppf "(%a %a) " Term.pp value0 Sort.pp
                 (Term.sort value0);
               unroll value1)
             else value
           in
           let value = unroll value in
           let value0 = Term.get value 0 in
           assert (Term.is_variable value0);
           Format.fprintf ppf "(%a %a)) %a %a)" Term.pp value0 Sort.pp
             (Term.sort value0) Sort.pp (Sort.fun_codomain sort) Term.pp
             (Term.get value 1))
         else
           Format.fprintf ppf ") %a %a)" Sort.pp sort Term.pp
             (Solver.get_value bitwuzla term)))
    [ x; y; f; a ];
  Format.print_space ();
  Format.print_space ();
```

This will output a possible model, in this case:
```smt2
(
  (define-fun x () (_ BitVec 8) #b10011111)
  (define-fun y () (_ BitVec 8) #b11111111)
  (define-fun f ((@bzla.var_71 (_ BitVec 8)) (@bzla.var_72 (_ BitVec 4))) 
  (_ BitVec 8) (ite (and (= @bzla.var_71 #b10011111) (= @bzla.var_72 #b0011)) #b11111111 #b00000000))
  (define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111))
)
```

Alternatively, it is possible to query the value of terms as assignment string via `Term.value`, or as a term via `Solver.get_value`.

In our case, we can query the assignments of `x` and `y`, both bit-vector terms, as binary strings:
```ocaml
  Format.printf "value of x: %s@,"
    (Term.value (String { base = 2 }) (Solver.get_value bitwuzla x));
  Format.printf "value of y: %s@,"
    (Term.value (String { base = 2 }) (Solver.get_value bitwuzla y));
  Format.print_space ();
```

This will print:
```text
value of x: 10011111
value of y: 11111111
```

The value of `f` (a function term) and `a` (an array term), on the other hand, cannot be represented with a simple type. Thus, function values are given as `Lambda`, and array values are given as `Store`. We can retrieve an SMT-LIB2 string representation of the values via `Term.pp`:
```ocaml
  Format.printf "str() representation of value of x:@,%a@," Term.pp
    (Solver.get_value bitwuzla x);
  Format.printf "str() representation of value of y:@,%a@," Term.pp
    (Solver.get_value bitwuzla y);
  Format.print_space ();
```

This will print:
```text
str() representation of value of f:
(lambda ((@bzla.var_71 (_ BitVec 8))) (lambda ((@bzla.var_72 (_ BitVec 4))) (ite (and (= @bzla.var_71 #b10011111) (= @bzla.var_72 #b0011)) #b11111111 #b00000000)))
str() representation of value of a:
(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111)
```

Note that the string representation of values representable as simple type (bit-vectors, boolean, floating-point, rounding mode) are given as pure value string (in the given number format) via `Term.value`. Their string representation retrieved via `Term.pp`, however, is given in SMT-LIB2 format. For example,
```ocaml
  Format.printf "str() representation of value of x:@,%a@," Term.pp
    (Solver.get_value bitwuzla x);
  Format.printf "str() representation of value of y:@,%a@," Term.pp
    (Solver.get_value bitwuzla y);
  Format.print_space ();
```

This will print:
```text
str() representation of value of x:
#b10011111
str() representation of value of y:
#b11111111
```

It is also possible to query the model value of expressions that do not occur in the input formula:
```ocaml
  let v = Solver.get_value bitwuzla (mk_term2 Bv_mul x x) in
  Format.printf "value of v = x * x: %s@," (Term.value (String { base = 2 }) v)
```

This will print:
```text
value of v = x * x: 11000001
```

### Examples

Other examples together with their SMT-LIB input can be found in directory
[examples](examples):
- an incremental example with `push` and `pop`
([pushpop](examples/pushpop.ml));
- an incremental example with `check-sat-assuming`
([checksatassuming](examples/checksatassuming.ml));
- an unsatisfiable example with unsat core generation
([unsatcore](examples/unsatcore.ml));
- an unsatisfiable example with unsat assumption query
([unsatassumptions](examples/unsatassumptions.ml))
- an example with termination callback
([terminator](examples/terminator.ml)).

## Installation

Bitwuzla sources and dependencies are repackaged for convenient use
with [*opam*](https://opam.ocaml.org/).

### From Opam

```bash
opam install bitwuzla
```

### From source

The latest version of `ocaml-bitwuzla` is available on GitHub:
https://github.com/bitwuzla/ocaml-bitwuzla.

---
:information_source: **Dealing with submodules**

In order to checkout the complete source tree,
run the following at `clone` time:
```bash
git clone --recurse-submodules https://github.com/bitwuzla/ocaml-bitwuzla.git
```
or at any time:
```bash
git submodule init # first time
git submodule update
```

:warning: **Do not** download the source archive (`.zip`, `.tar.gz`).
Download instead the
[tarball](https://github.com/bitwuzla/ocaml-bitwuzla/releases/download/0.1.0/bitwuzla-cxx-0.1.0.tbz) from release panel.
```bash
tar -xjf bitwuzla-cxx-0.1.0.tbz
```

#### Dependencies

- [GMP v6.1 (GNU Multi-Precision arithmetic library)](https://gmplib.org)
  (**required**)
- [OCaml >= 4.08](https://github.com/ocaml/ocaml) (**required**)
- [dune >= 3.7](https://github.com/ocaml/dune) (**required**)
- [zarith](https://github.com/ocaml/Zarith) (**required**)
- [odoc](https://github.com/ocaml/odoc) (*documentation*)
- [ppx_expect](https://github.com/janestreet/ppx_expect) (*tests*)

---
:information_source: **Handling dependencies with opam**

Dependencies can be automatically installed via
[*opam*](https://opam.ocaml.org/doc/Install.html).

```bash
opam pin add -n .                             # read the package definition
opam install --deps-only bitwuzla             # install OCaml dependencies
opam install --deps-only --with-doc bitwuzla  # optional, for documentation
opam install --deps-only --with-test bitwuzla # optional, for tests
```

#### Build

```bash
dune build @install
```

#### Running examples

```bash
dune exec -- examples/quickstart.exe # replace quickstart by other examples
```

#### Building the API documentation

```bash
dune build @doc
```
*An index page containing examples and links to modules can be found in
`_build/default/_doc/_html/index.html`.*

#### Running tests

```bash
dune build @runtest
```

:memo: No output is the expected behavior.
