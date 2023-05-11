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

open Bitwuzla_cxx

let () =
  Format.open_vbox 0;

  (* First, create a Bitwuzla options instance. *)
  let options = Options.default () in
  (* Then, create a Bitwuzla instance. *)
  let bitwuzla = Solver.create options in

  (* Create a bit-vector sort of size 1. *)
  let sortbv1 = mk_bv_sort 1 in
  (* Create a bit-vector sort of size 2. *)
  let sortbv2 = mk_bv_sort 2 in

  (* Create bit-vector variables. *)
  (* (declare-const o0 (_ BitVec 1)) *)
  let o0 = mk_const sortbv1 ~symbol:"o0" in
  (* (declare-const o1 (_ BitVec 1)) *)
  let o1 = mk_const sortbv1 ~symbol:"o1" in
  (* (declare-const s0 (_ BitVec 2)) *)
  let s0 = mk_const sortbv2 ~symbol:"s0" in
  (* (declare-const s1 (_ BitVec 2)) *)
  let s1 = mk_const sortbv2 ~symbol:"s1" in
  (* (declare-const s2 (_ BitVec 2)) *)
  let s2 = mk_const sortbv2 ~symbol:"s1" in
  (* (declare-const goal (_ BitVec 2)) *)
  let goal = mk_const sortbv2 ~symbol:"goal" in

  (* Create bit-vector values zero, one, three. *)
  let zero = mk_bv_zero sortbv2
  and one1 = mk_bv_one sortbv1
  and one2 = mk_bv_one sortbv2
  and three = mk_bv_value_int sortbv2 3 in

  (* Add some assertions. *)
  Solver.assert_formula bitwuzla (mk_term2 Equal s0 zero);
  Solver.assert_formula bitwuzla (mk_term2 Equal goal three);

  (* Push, assert, check sat and pop. *)
  Solver.push bitwuzla 1;
  Solver.assert_formula bitwuzla (mk_term2 Equal s0 goal);
  let result = Solver.check_sat bitwuzla in
  Format.printf "Expect: unsat@,";
  Format.printf "Bitwuzla: %s@," (Result.to_string result);
  Solver.pop bitwuzla 1;

  (* (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0))) *)
  Solver.assert_formula bitwuzla
    (mk_term2 Equal s1
       (mk_term3 Ite (mk_term2 Equal o0 one1) (mk_term2 Bv_add s0 one2) s0));

  (* Push, assert, check sat and pop. *)
  Solver.push bitwuzla 1;
  Solver.assert_formula bitwuzla (mk_term2 Equal s1 goal);
  let result = Solver.check_sat bitwuzla in
  Format.printf "Expect: unsat@,";
  Format.printf "Bitwuzla: %s@," (Result.to_string result);
  Solver.pop bitwuzla 1;

  (* (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1))) *)
  Solver.assert_formula bitwuzla
    (mk_term2 Equal s2
       (mk_term3 Ite (mk_term2 Equal o1 one1) (mk_term2 Bv_add s1 one2) s1));

  (* Push, assert, check sat and pop. *)
  Solver.push bitwuzla 1;
  Solver.assert_formula bitwuzla (mk_term2 Equal s2 goal);
  let result = Solver.check_sat bitwuzla in
  Format.printf "Expect: unsat@,";
  Format.printf "Bitwuzla: %s@," (Result.to_string result);
  Solver.pop bitwuzla 1;

  Format.close_box ()
