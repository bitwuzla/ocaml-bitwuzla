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
  Options.set options Produce_unsat_assumptions true;
  (* Then, create a Bitwuzla instance. *)
  let bitwuzla = Solver.create options in

  (* Create Boolean sort. *)
  let sortbool = mk_bool_sort () in
  (* Create a bit-vector sort of size 2. *)
  let sortbv2 = mk_bv_sort 2 in
  (* Create a bit-vector sort of size 4 *)
  let sortbv4 = mk_bv_sort 4 in
  (* Create Float16 floatinf-point sort. *)
  let sortfp16 = mk_fp_sort 5 11 in

  (* Create bit-vector variables. *)
  (* (declare-const x0 (_ BitVec 4)) *)
  let x0 = mk_const sortbv4 ~symbol:"x0" in
  (* (declare-const x1 (_ BitVec 2)) *)
  let x1 = mk_const sortbv2 ~symbol:"x1" in
  (* (declare-const x2 (_ BitVec 2)) *)
  let x2 = mk_const sortbv2 ~symbol:"x2" in
  (* (declare-const x3 (_ BitVec 2)) *)
  let x3 = mk_const sortbv2 ~symbol:"x3" in
  (* (declare-const x4 Float16) *)
  let x4 = mk_const sortfp16 ~symbol:"x4" in

  (* Create FP positive zero. *)
  let fpzero = mk_fp_pos_zero sortfp16 in
  (* Create BV zero of size 4. *)
  let bvzero = mk_bv_zero sortbv4 in

  (* (define-fun f0 ((a Float16)) Bool (fp.gt a (_ +zero 5 11))) *)
  let a_f0 = mk_var sortfp16 ~symbol:"a_f0" in
  let f0 = mk_term2 Lambda a_f0 (mk_term2 Fp_gt a_f0 fpzero) in

  (* (define-fun f1 ((a Float16)) (_ BitVec 4) (ite (f0 a) x0 #b0000)) *)
  let a_f1 = mk_var sortfp16 ~symbol:"a_f1" in
  let f1 =
    mk_term2 Lambda a_f1 (mk_term3 Ite (mk_term2 Apply f0 a_f1) x0 bvzero)
  in

  (* (define-fun f2 ((a Float16)) (_ BitVec 2) ((_ extract 1 0) (f1 a))) *)
  let a_f2 = mk_var sortfp16 ~symbol:"a_f2" in
  let f2 =
    mk_term2 Lambda a_f2
      (mk_term1_indexed2 Bv_extract (mk_term2 Apply f1 a_f2) 1 0)
  in

  (* (assert (! (bvult x2 (f2 (_ +zero 5 11))) :named a0)) *)
  let a0 = mk_const sortbool ~symbol:"a0" in
  let assumption0 = mk_term2 Bv_ult x2 (mk_term2 Apply f2 fpzero) in
  Solver.assert_formula bitwuzla (mk_term2 Equal a0 assumption0);

  (* (assert (! (= x1 x2 x3) :named a1)) *)
  let a1 = mk_const sortbool ~symbol:"a1" in
  let assumption1 = mk_term Equal [| x1; x2; x3 |] in
  Solver.assert_formula bitwuzla (mk_term2 Equal a1 assumption1);

  (* (assert (!(= x4 ((_ to_fp_unsigned 5 11) RNE x3)) :named a2)) *)
  let a2 = mk_const sortbool ~symbol:"a2" in
  let assumption2 =
    mk_term2 Equal x4
      (mk_term2_indexed2 Fp_to_fp_from_ubv (mk_rm_value Rne) x3 5 11)
  in
  Solver.assert_formula bitwuzla (mk_term2 Equal a2 assumption2);

  (* (check-sat-assuming (assumption0 assumption1 assumption2)) *)
  let result = Solver.check_sat bitwuzla ~assumptions:[| a0; a1; a2 |] in
  Format.printf "Expect: unsat@,";
  Format.printf "Bitwuzla: %s@," (Result.to_string result);

  (* (get-unsat-assumptions) *)
  let unsat_assumptions = Solver.get_unsat_assumptions bitwuzla in
  Format.printf "Unsat Assumptions:@,@[<v 1>{";
  Array.iter (Format.printf "@,%a" Term.pp) unsat_assumptions;
  Format.printf "@]@,}@,";

  Format.close_box ()
