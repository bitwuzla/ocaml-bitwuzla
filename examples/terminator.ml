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

let timeout time_limit =
  let start = Unix.gettimeofday () in
  fun () -> Float.compare (Unix.gettimeofday () -. start) time_limit >= 0

let () =
  Format.open_vbox 0;

  (* First, create a Bitwuzla options instance. *)
  let options = Options.default () in
  (* Then, create a Bitwuzla instance. *)
  let bitwuzla = Solver.create options in

  let bv = mk_bv_sort 32 in

  let x = mk_const bv and s = mk_const bv and t = mk_const bv in

  let a =
    mk_term2 Distinct
      (mk_term2 Bv_mul s (mk_term2 Bv_mul x t))
      (mk_term2 Bv_mul (mk_term2 Bv_mul s x) t)
  in

  (* Now, we check that the following formula is unsat. *)
  (* (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t))) *)
  Format.printf "> Without terminator (with preprocessing):@,";
  Format.printf "Expect: unsat@,";
  Format.printf "Result: %s@,"
    (Result.to_string (Solver.check_sat bitwuzla ~assumptions:[| a |]));

  (* Now, for illustration purposes, we disable preprocessing, which will *)
  (* significantly increase solving time, and connect a terminator instance *)
  (* that terminates after a certain time limit. *)
  Options.set options Preprocess false;
  (* Create new Bitwuzla instance with reconfigured options. *)
  let bitwuzla2 = Solver.create options in

  (* Configure and connect terminator. *)
  let terminator = timeout 1. in
  Solver.configure_terminator bitwuzla2 (Some terminator);

  (* Now, we expect Bitwuzla to be terminated during the check-sat call. *)
  Format.printf "> With terminator (no preprocessing):@,";
  Format.printf "Expect: unknown@,";
  Format.printf "Result: %s@,"
    (Result.to_string (Solver.check_sat bitwuzla2 ~assumptions:[| a |]));

  Format.close_box ()
