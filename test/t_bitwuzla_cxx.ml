(**************************************************************************)
(*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.                *)
(*                                                                        *)
(*  Copyright (C) 2023 by the authors listed in the AUTHORS file at       *)
(*  https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS                *)
(*                                                                        *)
(*  This file is part of Bitwuzla under the MIT license.                  *)
(*  See COPYING for more information at                                   *)
(*  https://github.com/bitwuzla/bitwuzla/blob/main/COPYING                *)
(**************************************************************************)

(* The inline tests were moved here to avoid depending on ppx outside tests.  *)
(* The goal of these tests are to catch errors in the function and constant   *)
(* mappings. They do not try to catch functional errors in Bitwuzla.          *)

open Bitwuzla_cxx
open Format

let print_predicate b = print_int (Bool.to_int b)
let timeout t () = Float.compare (Sys.time ()) t > 0

let pp_array pp f a =
  Array.iter
    (fun t ->
      pp f t;
      Format.print_space ())
    a

let with_t_naked f =
  let options = Options.default () in
  Options.set options Produce_models true;
  Options.set options Produce_unsat_assumptions true;
  Options.set options Produce_unsat_cores true;
  let t = Solver.create options in
  let r = f t in
  Solver.unsafe_delete t;
  r

let with_t f =
  with_t_naked (fun t ->
      Solver.assert_formula t @@ mk_true ();
      f t)

let with_sat_formula f =
  with_t (fun t ->
      let bv1 = mk_bool_sort () in
      let a = mk_const bv1 ~symbol:"a" in
      Solver.assert_formula t @@ mk_term2 Equal a @@ mk_true ();
      f (t, a))

let with_unsat_formula assert_formula f =
  with_t (fun t ->
      let bv1 = mk_bool_sort () in
      let a = mk_const bv1 ~symbol:"a" in
      let e = mk_term2 Equal a @@ mk_term1 Not a in
      if assert_formula then Solver.assert_formula t e;
      f (t, e))

let with_sat_push_unsat_push2_formula f =
  with_t (fun t ->
      Solver.assert_formula t @@ mk_true ();
      Solver.push t 1;
      Solver.assert_formula t @@ mk_false ();
      Solver.push t 2;
      f t)

let with_hard_formula f =
  with_t_naked (fun t ->
      let bv64 = mk_bv_sort 64 in
      let bv128 = mk_bv_sort 128 in
      let a64 = mk_const bv64 ~symbol:"a" in
      let b64 = mk_const bv64 ~symbol:"b" in
      let a128 = mk_term1_indexed1 Bv_zero_extend a64 64 in
      let b128 = mk_term1_indexed1 Bv_zero_extend b64 64 in
      let ab128 = mk_term2 Bv_mul a128 b128 in
      let p = mk_bv_value bv128 "87e03acc9f5050086f083d2d5d6b9d47" 16 in
      let one128 = mk_bv_one bv128 in
      Solver.assert_formula t @@ mk_term2 Distinct a128 one128;
      Solver.assert_formula t @@ mk_term2 Distinct b128 one128;
      Solver.assert_formula t @@ mk_term2 Equal ab128 p;
      f t)

let rm_sort = mk_rm_sort ()
let bool_sort = mk_bool_sort ()
let bv8_sort = mk_bv_sort 8
let bv32_sort = mk_bv_sort 32
let fp16_sort = mk_fp_sort 5 11
let ar32_8_sort = mk_array_sort bv32_sort bv8_sort
let fun1_1_1_sort = mk_fun_sort [| bool_sort; bool_sort |] bool_sort
let uninterpreted_sort = mk_uninterpreted_sort ~symbol:"T" ()

let sorts =
  [|
    ar32_8_sort;
    bool_sort;
    bv8_sort;
    bv32_sort;
    fp16_sort;
    fun1_1_1_sort;
    rm_sort;
    uninterpreted_sort;
  |]

let with_sorts f = Array.iter (fun s -> f s) sorts

let with_sorts_2 f =
  Array.iter
    (fun s1 ->
      Array.iter (fun s2 -> f s1 s2) sorts;
      print_space ())
    sorts

let bv_zero = mk_bv_zero bv8_sort

let bv_const_a = mk_const bv8_sort ~symbol:"a"
and bv_const_b = mk_const bv8_sort ~symbol:"b"
and bv_const_c = mk_const bv32_sort ~symbol:"c"

let bv_var = mk_var bv8_sort ~symbol:"a"
let fp_zero = mk_fp_pos_zero fp16_sort
let fp_const_a = mk_const fp16_sort ~symbol:"a"
let ar_value = mk_const_array ar32_8_sort bv_zero
let ar_const_a = mk_const ar32_8_sort ~symbol:"a"
let fun_const_a = mk_const fun1_1_1_sort ~symbol:"a"
let rm_rtz = mk_rm_value Rtz
let term1 = mk_term1 Bv_not bv_const_a
let term2 = mk_term2 Bv_add bv_const_a bv_const_b
let term3 = mk_term3 Store ar_const_a bv_const_c bv_const_b
let term1_indexed2 = mk_term1_indexed2 Bv_extract bv_const_a 1 0

let terms =
  [|
    bv_zero;
    bv_const_a;
    bv_const_b;
    bv_const_c;
    bv_var;
    fp_zero;
    fp_const_a;
    ar_value;
    ar_const_a;
    fun_const_a;
    term1;
    term2;
    term3;
    term1_indexed2;
    rm_rtz;
  |]

let with_terms f = Array.iter f terms
let%test "version" = 0 <> String.length @@ version ()

let%expect_test "copyright" =
  print_string @@ copyright ();
  [%expect
    {|
    Bitwuzla is a Satisfiability Modulo Theories (SMT) Solver for bit-vectors,
    floating-points, arrays and uninterpreted functions.

    Copyright (C) 2018-2023 by its authors and contributors and their institutional
    affiliations as listed in file AUTHORS.

    MIT License

    Permission is hereby granted, free of charge, to any person obtaining a
    copy of this software and associated documentation files (the "Software"),
    to deal in the Software without restriction, including without limitation
    the rights to use, copy, modify, merge, publish, distribute, sublicense,
    and/or sell copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
    THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
    OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
    ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
    OTHER DEALINGS IN THE SOFTWARE.


    This version of Bitwuzla is linked against the following
    third party libraries. For copyright information of each
    library see the corresponding url.

      CaDiCaL
      https://github.com/arminbiere/cadical

      GMP - GNU Multiple Precision Arithmetic Library
      https://gmplib.org

      SymFPU
      https://github.com/martin-cs/symfpu |}]

let%test "Options (bool)" =
  let t = Options.default () in
  let d = Options.default_value Produce_models in
  let r = d = Options.get t Produce_models in
  Options.set t Produce_models (not d);
  r && d <> Options.get t Produce_models

let%test "Options (numeric)" =
  let t = Options.default () in
  let d = Options.default_value Log_level in
  let r = d = Options.get t Log_level in
  let min = Options.min Log_level in
  Options.set t Log_level min;
  let r = r && min = Options.get t Log_level in
  let max = Options.max Log_level in
  Options.set t Log_level max;
  r && max = Options.get t Log_level

let%test "Options (numeric)" =
  let t = Options.default () in
  let max = Options.max Log_level in
  try
    Options.set t Log_level (max + 1);
    false
  with Invalid_argument _ -> true

let%test "Options (mode)" =
  let t = Options.default () in
  let d = Options.default_value Sat_solver in
  let r = d = Options.get t Sat_solver in
  let s : Options.sat_solver = if d = Cadical then Kissat else Cadical in
  Options.set t Sat_solver s;
  let n = Options.get t Sat_solver in
  r && d <> n && s = n

let%expect_test "mk_array_sort" =
  Sort.pp Format.std_formatter ar32_8_sort;
  [%expect {| (Array (_ BitVec 32) (_ BitVec 8)) |}]

let%expect_test "mk_bool_sort" =
  Sort.pp Format.std_formatter bool_sort;
  [%expect {| Bool |}]

let%expect_test "mk_bv_sort" =
  Sort.pp Format.std_formatter bv8_sort;
  [%expect {| (_ BitVec 8) |}]

let%expect_test "mk_fp_sort" =
  Sort.pp Format.std_formatter fp16_sort;
  [%expect {| (_ FloatingPoint 5 11) |}]

let%expect_test "mk_fun_sort" =
  Sort.pp Format.std_formatter fun1_1_1_sort;
  [%expect {| Bool Bool -> Bool |}]

let%test "mk_fun_sort" =
  try
    ignore (mk_fun_sort [||] bool_sort);
    false
  with Invalid_argument _ -> true

let%expect_test "mk_rm_sort" =
  Sort.pp Format.std_formatter rm_sort;
  [%expect {| RoundingMode |}]

let%test "mk_uninterpreted_sort" =
  Sort.is_uninterpreted @@ mk_uninterpreted_sort ()

let%expect_test "mk_uninterpreted_sort" =
  Sort.pp Format.std_formatter uninterpreted_sort;
  [%expect {| T |}]

let%expect_test "Sort.equal" =
  with_sorts_2 (fun s1 s2 -> print_predicate @@ Sort.equal s1 s2);
  [%expect
    {| 10000000 01000000 00100000 00010000 00001000 00000100 00000010 00000001 |}]

let%expect_test "Sort.compare" =
  with_sorts_2 (fun s1 s2 ->
      print_predicate (Sort.compare s1 s2 = 0 = Sort.equal s1 s2));
  [%expect
    {| 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 |}]

let%test "Sort.hash" =
  with_sorts (fun s -> ignore (Sort.hash s));
  true

let%test "Sort.bv_size" = Sort.bv_size bv8_sort = 8
let%test "Sort.fp_exp_size" = Sort.fp_exp_size fp16_sort = 5
let%test "Sort.fp_sig_size" = Sort.fp_sig_size fp16_sort = 11

let%expect_test "Sort.array_index" =
  Sort.pp Format.std_formatter (Sort.array_index ar32_8_sort);
  [%expect {| (_ BitVec 32) |}]

let%expect_test "Sort.array_element" =
  Sort.pp Format.std_formatter (Sort.array_element ar32_8_sort);
  [%expect {| (_ BitVec 8) |}]

let%expect_test "Sort.fun_domain_sorts" =
  (pp_array Sort.pp) Format.std_formatter (Sort.fun_domain fun1_1_1_sort);
  [%expect {| Bool Bool |}]

let%expect_test "Sort.fun_codomain" =
  Sort.pp Format.std_formatter (Sort.fun_codomain fun1_1_1_sort);
  [%expect {| Bool |}]

let%test "Sort.fun_arity" = Sort.fun_arity fun1_1_1_sort = 2

let%expect_test "Sort.uninterpreted_symbol" =
  print_string
    (Sort.uninterpreted_symbol (mk_uninterpreted_sort ~symbol:"T" ()));
  [%expect {| T |}]

let%test "Sort.uninterpreted_symbol" =
  try
    ignore @@ Sort.uninterpreted_symbol (mk_uninterpreted_sort ());
    false
  with Not_found -> true

let%test "Sort (compare)" = mk_bool_sort () = mk_bool_sort ()
let%test "Sort (compare)" = not (mk_bv_sort 32 = mk_bv_sort 64)

let%expect_test "Sort.is_array" =
  with_sorts (fun s -> print_predicate @@ Sort.is_array s);
  [%expect {| 10000000 |}]

let%expect_test "Sort.is_bv" =
  with_sorts (fun s -> print_predicate @@ Sort.is_bool s);
  [%expect {| 01000000 |}]

let%expect_test "Sort.is_bv" =
  with_sorts (fun s -> print_predicate @@ Sort.is_bv s);
  [%expect {| 00110000 |}]

let%expect_test "Sort.is_fp" =
  with_sorts (fun s -> print_predicate @@ Sort.is_fp s);
  [%expect {| 00001000 |}]

let%expect_test "Sort.is_fun" =
  with_sorts (fun s -> print_predicate @@ Sort.is_fun s);
  [%expect {| 00000100 |}]

let%expect_test "Sort.is_rm" =
  with_sorts (fun s -> print_predicate @@ Sort.is_rm s);
  [%expect {| 00000010 |}]

let%expect_test "Sort.is_uninterpreted" =
  with_sorts (fun s -> print_predicate @@ Sort.is_uninterpreted s);
  [%expect {| 00000001 |}]

let%expect_test "mk_true" =
  Term.pp Format.std_formatter (mk_true ());
  [%expect {| true |}]

let%expect_test "mk_false" =
  Term.pp Format.std_formatter (mk_false ());
  [%expect {| false |}]

let%expect_test "mk_bv_zero" =
  Term.pp Format.std_formatter (mk_bv_zero bv8_sort);
  [%expect {| #b00000000 |}]

let%expect_test "mk_bv_one" =
  Term.pp Format.std_formatter (mk_bv_one bv8_sort);
  [%expect {| #b00000001 |}]

let%expect_test "mk_bv_ones" =
  Term.pp Format.std_formatter (mk_bv_ones bv8_sort);
  [%expect {| #b11111111 |}]

let%expect_test "mk_bv_min_signed" =
  Term.pp Format.std_formatter (mk_bv_min_signed bv8_sort);
  [%expect {| #b10000000 |}]

let%expect_test "mk_bv_max_signed" =
  Term.pp Format.std_formatter (mk_bv_max_signed bv8_sort);
  [%expect {| #b01111111 |}]

let%expect_test "mk_bv_value" =
  Term.pp Format.std_formatter (mk_bv_value bv8_sort "42" 10);
  [%expect {| #b00101010 |}]

let%expect_test "mk_bv_value" =
  Term.pp Format.std_formatter (mk_bv_value bv8_sort "2a" 16);
  [%expect {| #b00101010 |}]

let%expect_test "mk_bv_value" =
  Term.pp Format.std_formatter (mk_bv_value bv8_sort "00101010" 2);
  [%expect {| #b00101010 |}]

let%expect_test "mk_bv_value_int" =
  Term.pp Format.std_formatter (mk_bv_value_int bv8_sort 42);
  [%expect {| #b00101010 |}]

let%expect_test "mk_bv_value_int64" =
  Term.pp Format.std_formatter (mk_bv_value_int64 bv8_sort 42L);
  [%expect {| #b00101010 |}]

let%expect_test "mk_fp_pos_zero" =
  Term.pp Format.std_formatter (mk_fp_pos_zero fp16_sort);
  [%expect {| (fp #b0 #b00000 #b0000000000) |}]

let%expect_test "mk_fp_neg_zero" =
  Term.pp Format.std_formatter (mk_fp_neg_zero fp16_sort);
  [%expect {| (fp #b1 #b00000 #b0000000000) |}]

let%expect_test "mk_fp_pos_inf" =
  Term.pp Format.std_formatter (mk_fp_pos_inf fp16_sort);
  [%expect {| (fp #b0 #b11111 #b0000000000) |}]

let%expect_test "mk_fp_neg_inf" =
  Term.pp Format.std_formatter (mk_fp_neg_inf fp16_sort);
  [%expect {| (fp #b1 #b11111 #b0000000000) |}]

let%expect_test "mk_fp_nan" =
  Term.pp Format.std_formatter (mk_fp_nan fp16_sort);
  [%expect {| (fp #b0 #b11111 #b1000000000) |}]

let%expect_test "mk_fp_value" =
  Term.pp Format.std_formatter
    (let sign = mk_bv_zero (mk_bv_sort 1)
     and expv = mk_bv_value (mk_bv_sort 5) "10010" 2
     and sigv = mk_bv_value (mk_bv_sort 10) "100001100" 2 in
     mk_fp_value sign expv sigv);
  [%expect {| (fp #b0 #b10010 #b0100001100) |}]

let%expect_test "mk_fp_value_from_real" =
  Term.pp Format.std_formatter
    (mk_fp_value_from_real fp16_sort (mk_rm_value Rtz) "10.1");
  [%expect {| (fp #b0 #b10010 #b0100001100) |}]

let%expect_test "mk_fp_value_from_rational" =
  Term.pp Format.std_formatter
    (mk_fp_value_from_rational fp16_sort (mk_rm_value Rtz) "101" "10");
  [%expect {| (fp #b0 #b10010 #b0100001100) |}]

let%expect_test "mk_rm_value" =
  (RoundingMode.[| Rne; Rna; Rtn; Rtp; Rtz |]
  |> Array.iter @@ fun x ->
     Term.pp Format.std_formatter (mk_rm_value x);
     Format.print_space ());
  [%expect {| RNE RNA RTN RTP RTZ |}]

let%expect_test "mk_term" =
  Term.pp Format.std_formatter
    (mk_term Bv_and
       [|
         mk_const bv8_sort ~symbol:"a";
         mk_const bv8_sort ~symbol:"b";
         mk_const bv8_sort ~symbol:"c";
       |]);
  [%expect {| (bvand (bvand a b) c) |}]

let%expect_test "mk_term_indexed" =
  Term.pp Format.std_formatter
    (mk_term Bv_repeat [| mk_bv_zero bv8_sort |] ~indices:[| 4 |]);
  [%expect {| ((_ repeat 4) #b00000000) |}]

let%expect_test "mk_const" =
  Term.pp Format.std_formatter (mk_const bv8_sort ~symbol:"a");
  [%expect {| a |}]

let%test "mk_const" = Term.is_const (mk_const bv8_sort)

let%expect_test "mk_const_array" =
  Term.pp Format.std_formatter (mk_const_array ar32_8_sort @@ mk_bv_one bv8_sort);
  [%expect {| ((as const (Array (_ BitVec 32) (_ BitVec 8))) #b00000001) |}]

let%expect_test "mk_var" =
  Term.pp Format.std_formatter (mk_var bv8_sort ~symbol:"a");
  [%expect {| a |}]

let%test "mk_var" = Term.is_variable (mk_var bv8_sort)

let%expect_test "substitute_term" =
  Term.pp Format.std_formatter
    (let a = mk_const bv8_sort ~symbol:"a" in
     substitute_term a [| (a, mk_bv_one bv8_sort) |]);
  [%expect {| #b00000001 |}]

let%expect_test "substitute_terms" =
  (pp_array Term.pp) Format.std_formatter
    (let a = mk_const bv8_sort ~symbol:"a"
     and b = mk_const bv8_sort ~symbol:"b" in
     let terms = [| a; b |] in
     substitute_terms terms
       [| (b, mk_bv_ones bv8_sort); (a, mk_bv_one bv8_sort) |];
     terms);
  [%expect {| #b00000001 #b11111111 |}]

let%test "Term.hash" =
  with_terms (fun t -> ignore @@ Term.hash t);
  true

let%test "Term.kind" = Term.kind term1 = Bv_not
let%test "Term.num_children" = Term.num_children term1 = 1
let%test "Term.num_children" = Term.num_children term2 = 2
let%test "Term.num_children" = Term.num_children term3 = 3
let%test "Term.num_children" = Term.num_children term1_indexed2 = 1

let%expect_test "Term.children" =
  (pp_array Term.pp) Format.std_formatter (Term.children term1);
  [%expect {| a |}]

let%expect_test "Term.children" =
  (pp_array Term.pp) Format.std_formatter (Term.children term2);
  [%expect {|
       a b |}]

let%expect_test "Term.children" =
  (pp_array Term.pp) Format.std_formatter (Term.children term3);
  [%expect {|
       a c b |}]

let%expect_test "Term.get" =
  Term.pp Format.std_formatter (Term.get term2 0);
  [%expect {|
       a |}]

let%expect_test "Term.get" =
  Term.pp Format.std_formatter (Term.get term2 1);
  [%expect {|
       b |}]

let%expect_test "Term.get" =
  Term.pp Format.std_formatter (Term.get term3 0);
  [%expect {|
       a |}]

let%expect_test "Term.get" =
  Term.pp Format.std_formatter (Term.get term3 1);
  [%expect {|
       c |}]

let%expect_test "Term.get" =
  Term.pp Format.std_formatter (Term.get term3 2);
  [%expect {|
       b |}]

let%test "Term.get" =
  try
    ignore @@ Term.get term3 3;
    false
  with Invalid_argument _ -> true

let%test "Term.num_indices" = Term.num_indices term1 = 0
let%test "Term.num_indices" = Term.num_indices term1 = 0
let%test "Term.num_indices" = Term.num_indices term2 = 0
let%test "Term.num_indices" = Term.num_indices term3 = 0
let%test "Term.num_indices" = Term.num_indices term1_indexed2 = 2

let%expect_test "Term.indices" =
  (pp_array pp_print_int) Format.std_formatter (Term.indices term1_indexed2);
  [%expect {| 1 0 |}]

let%expect_test "Term.sort" =
  with_terms (fun t ->
      Sort.pp Format.std_formatter (Term.sort t);
      Format.print_space ());
  [%expect
    {|
       (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 32) (_ BitVec 8)
       (_ FloatingPoint 5 11) (_ FloatingPoint 5 11)
       (Array (_ BitVec 32) (_ BitVec 8)) (Array (_ BitVec 32) (_ BitVec 8))
       Bool Bool -> Bool (_ BitVec 8) (_ BitVec 8)
       (Array (_ BitVec 32) (_ BitVec 8)) (_ BitVec 2) RoundingMode |}]

let%expect_test "Term.symbol" =
  print_string (Term.symbol bv_const_a);
  [%expect {| a |}]

let%test "Term.symbol" =
  try
    ignore @@ Term.symbol (mk_bv_zero bv8_sort);
    false
  with Not_found -> true

let%expect_test "Term.is_const" =
  with_terms (fun t -> print_predicate (Term.is_const t));
  [%expect {| 011100101100000 |}]

let%expect_test "Term.is_variable" =
  with_terms (fun t -> print_predicate (Term.is_variable t));
  [%expect {| 000010000000000 |}]

let%expect_test "Term.is_value" =
  with_terms (fun t -> print_predicate (Term.is_value t));
  [%expect {| 100001000000001 |}]

let%test "Term.is_bv_value_zero" = not @@ Term.is_bv_value_zero bv_var
let%test "Term.is_bv_value_zero" = Term.is_bv_value_zero @@ mk_bv_zero bv8_sort
let%test "Term.is_bv_value_one" = not @@ Term.is_bv_value_one bv_var
let%test "Term.is_bv_value_one" = Term.is_bv_value_one @@ mk_bv_one bv8_sort
let%test "Term.is_bv_value_ones" = not @@ Term.is_bv_value_ones bv_var
let%test "Term.is_bv_value_ones" = Term.is_bv_value_ones @@ mk_bv_ones bv8_sort

let%test "Term.is_bv_value_min_signed" =
  not @@ Term.is_bv_value_min_signed bv_var

let%test "Term.is_bv_value_min_signed" =
  Term.is_bv_value_min_signed @@ mk_bv_min_signed bv8_sort

let%test "Term.is_bv_value_max_signed" =
  not @@ Term.is_bv_value_max_signed bv_var

let%test "Term.is_bv_value_max_signed" =
  Term.is_bv_value_max_signed @@ mk_bv_max_signed bv8_sort

let%test "Term.is_fp_value_pos_zero" = not @@ Term.is_fp_value_pos_zero bv_var

let%test "Term.is_fp_value_pos_zero" =
  Term.is_fp_value_pos_zero @@ mk_fp_pos_zero fp16_sort

let%test "Term.is_fp_value_neg_zero" = not @@ Term.is_fp_value_neg_zero bv_var

let%test "Term.is_fp_value_neg_zero" =
  Term.is_fp_value_neg_zero @@ mk_fp_neg_zero fp16_sort

let%test "Term.is_fp_value_pos_inf" = not @@ Term.is_fp_value_pos_inf bv_var

let%test "Term.is_fp_value_pos_inf" =
  Term.is_fp_value_pos_inf @@ mk_fp_pos_inf fp16_sort

let%test "Term.is_fp_value_neg_inf" = not @@ Term.is_fp_value_neg_inf bv_var

let%test "Term.is_fp_value_neg_inf" =
  Term.is_fp_value_neg_inf @@ mk_fp_neg_inf fp16_sort

let%test "Term.is_fp_value_nan" = not @@ Term.is_fp_value_nan bv_var
let%test "Term.is_fp_value_nan" = Term.is_fp_value_nan @@ mk_fp_nan fp16_sort

let%test "push/pop" =
  with_sat_push_unsat_push2_formula (fun t ->
      Solver.pop t 1;
      Solver.check_sat t = Unsat)

let%test "push/pop" =
  with_sat_push_unsat_push2_formula (fun t ->
      Solver.pop t 2;
      Solver.check_sat t = Unsat)

let%test "push/pop" =
  with_sat_push_unsat_push2_formula (fun t ->
      Solver.pop t 3;
      Solver.check_sat t = Sat)

let%expect_test "pp_formula" =
  with_hard_formula (fun t -> Solver.pp_formula Format.std_formatter t);
  [%expect
    {|
       (set-logic QF_BV)
       (declare-const a (_ BitVec 64))
       (declare-const b (_ BitVec 64))
       (assert (distinct ((_ zero_extend 64) a) #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001))
       (assert (distinct ((_ zero_extend 64) b) #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001))
       (assert (= (bvmul ((_ zero_extend 64) a) ((_ zero_extend 64) b)) #b10000111111000000011101011001100100111110101000001010000000010000110111100001000001111010010110101011101011010111001110101000111))
       (check-sat)
       (exit) |}]

let%expect_test "simplify" =
  with_sat_formula (fun (t, _) ->
      ignore (Solver.simplify t);
      Solver.pp_formula Format.std_formatter t);
  [%expect {|
    (set-logic ALL)
    (check-sat)
    (exit) |}]

let%expect_test "get_value" =
  Term.pp Format.std_formatter
    (with_sat_formula (fun (t, a) ->
         ignore @@ Solver.check_sat t;
         Solver.get_value t a));
  [%expect {| true |}]

let%test "get_bool_value" =
  with_sat_formula (fun (t, a) ->
      ignore @@ Solver.check_sat t;
      Term.value Bool (Solver.get_value t a))

let%expect_test "get_bv_value" =
  print_string
    (with_t_naked (fun t ->
         let bv8 = mk_bv_sort 8 in
         let a = mk_const bv8 ~symbol:"a" in
         let v = mk_bv_value_int bv8 42 in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         Term.value (String { base = 2 }) (Solver.get_value t a)));
  [%expect {| 00101010 |}]

let%expect_test "get_bv_value" =
  Z.print
    (with_t_naked (fun t ->
         let bv8 = mk_bv_sort 8 in
         let a = mk_const bv8 ~symbol:"a" in
         let v = mk_bv_value_int bv8 42 in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         Term.value Z (Solver.get_value t a)));
  [%expect {| 42 |}]

let%expect_test "get_bv_value" =
  Z.print
    (with_t_naked (fun t ->
         let bv64 = mk_bv_sort 64 in
         let a = mk_const bv64 ~symbol:"a" in
         let v = mk_bv_value_int64 bv64 9223372036854775807L in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         Term.value Z (Solver.get_value t a)));
  [%expect {| 9223372036854775807 |}]

let%expect_test "get_bv_value" =
  Z.print
    (with_t_naked (fun t ->
         let bv128 = mk_bv_sort 128 in
         let a = mk_const bv128 ~symbol:"a" in
         let v = mk_bv_value bv128 "36893488147419103232" 10 in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         Term.value Z (Solver.get_value t a)));
  [%expect {| 36893488147419103232 |}]

let%expect_test "get_fp_value" =
  print_string
    (with_t_naked (fun t ->
         let fp32 = mk_fp_sort 8 24 in
         let a = mk_const fp32 ~symbol:"a" in
         let r = mk_rm_value Rtz in
         let v = mk_fp_value_from_real fp32 r "42" in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         let sign, exponent, significand =
           Term.value IEEE_754 (Solver.get_value t a)
         in
         sign ^ exponent ^ significand));
  [%expect {| 01000010001010000000000000000000 |}]

let%expect_test "get_rm_value" =
  print_string
    (with_t_naked (fun t ->
         let rm = mk_rm_sort () in
         let a = mk_const rm ~symbol:"a" in
         let v = mk_rm_value Rtz in
         Solver.assert_formula t @@ mk_term2 Equal a v;
         ignore @@ Solver.check_sat t;
         RoundingMode.to_string (Term.value RoundingMode (Solver.get_value t a))));
  [%expect {| RTZ |}]

let%test "is_unsat_assumption" =
  (with_unsat_formula false) (fun (t, e) ->
      ignore @@ Solver.check_sat ~assumptions:[| e |] t;
      Solver.is_unsat_assumption t e)

let%expect_test "get_unsat_assumptions" =
  (pp_array Term.pp) Format.std_formatter
    (with_unsat_formula false (fun (t, e) ->
         ignore @@ Solver.check_sat ~assumptions:[| e |] t;
         Solver.get_unsat_assumptions t));
  [%expect {| (= a (not a)) |}]

let%expect_test "get_unsat_core" =
  (pp_array Term.pp) Format.std_formatter
    (with_unsat_formula true (fun (t, _) ->
         ignore @@ Solver.check_sat t;
         Solver.get_unsat_core t));
  [%expect {| (= a (not a)) |}]

let%test "terminate" =
  with_hard_formula (fun t ->
      Solver.configure_terminator t (Some (timeout (Sys.time () +. 0.1)));
      Solver.check_sat t = Unknown)

let%test "terminate" =
  with_hard_formula (fun t ->
      Solver.configure_terminator t (Some (timeout (Sys.time () +. 5.)));
      Solver.check_sat t = Unknown)

let%test "GC" =
  (with_unsat_formula false) (fun (t, e) ->
      for _ = 0 to 1023 do
        let rec loop k i =
          if k > 0 then loop (k - 1) (mk_term1 Bv_inc i) else ()
        in
        loop 2000 (mk_const bv32_sort);
        Gc.minor ()
      done;
      ignore @@ Solver.check_sat ~assumptions:[| e |] t;
      Gc.full_major ();
      Solver.is_unsat_assumption t e)

let%expect_test "Term.pp_smt2" =
  let fortytwo = mk_bv_value_int bv8_sort 42 in
  Term.pp_smt2 ~bv_format:2 Format.std_formatter fortytwo;
  Format.pp_print_newline Format.std_formatter ();
  Term.pp_smt2 ~bv_format:10 Format.std_formatter fortytwo;
  Format.pp_print_newline Format.std_formatter ();
  Term.pp_smt2 ~bv_format:16 Format.std_formatter fortytwo;
  [%expect {|
    #b00101010
    (_ bv42 8)
    #x2a |}]

let%expect_test "Term.to_string" =
  let fortytwo = mk_bv_value_int bv8_sort 42 in
  Format.pp_print_string Format.std_formatter (Term.to_string fortytwo);
  Format.pp_print_newline Format.std_formatter ();
  Format.pp_print_string Format.std_formatter
    (Term.to_string ~bv_format:2 fortytwo);
  Format.pp_print_newline Format.std_formatter ();
  Format.pp_print_string Format.std_formatter
    (Term.to_string ~bv_format:10 fortytwo);
  Format.pp_print_newline Format.std_formatter ();
  Format.pp_print_string Format.std_formatter
    (Term.to_string ~bv_format:16 fortytwo);
  [%expect {|
    #b00101010
    #b00101010
    (_ bv42 8)
    #x2a |}]
