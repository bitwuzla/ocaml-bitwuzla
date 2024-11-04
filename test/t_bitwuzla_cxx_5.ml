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

let timeout time_limit =
  let start = Unix.gettimeofday () in
  fun () -> Float.compare (Unix.gettimeofday () -. start) time_limit >= 0

module Options = Bitwuzla_cxx.Options

let quickstart (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  Options.set options Produce_models true;
  let bitwuzla = Solver.create options in
  let sortbv4 = mk_bv_sort 4 and sortbv8 = mk_bv_sort 8 in
  let sortfun = mk_fun_sort [| sortbv8; sortbv4 |] sortbv8 in
  let sortarr = mk_array_sort sortbv8 sortbv8 in
  let x = mk_const sortbv8 ~symbol:"x" and y = mk_const sortbv8 ~symbol:"y" in
  let f = mk_const sortfun ~symbol:"f" in
  let a = mk_const sortarr ~symbol:"a" in
  let one = mk_bv_one sortbv8 in
  let two = mk_bv_value_int sortbv8 2 in
  let sdiv = mk_term2 Bv_sdiv x two in
  let ashr = mk_term2 Bv_ashr y one in
  let sdive = mk_term1_indexed2 Bv_extract sdiv 3 0 in
  let ashre = mk_term1_indexed2 Bv_extract ashr 3 0 in
  Solver.assert_formula bitwuzla (mk_term2 Distinct sdive ashre);
  Solver.assert_formula bitwuzla
    (mk_term2 Equal (mk_term3 Apply f x (mk_term1_indexed2 Bv_extract x 6 3)) y);
  Solver.assert_formula bitwuzla (mk_term2 Equal (mk_term2 Select a x) y);
  let result = Solver.check_sat bitwuzla in
  result = Sat
  && Term.value Z (Solver.get_value bitwuzla x) = Z.of_int 0b10011111
  && Term.value Z (Solver.get_value bitwuzla y) = Z.of_int 0b11111111
  && Term.value Z (Solver.get_value bitwuzla (mk_term2 Bv_mul x x))
     = Z.of_int 0b11000001

let pushpop (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  let bitwuzla = Solver.create options in
  let sortbv1 = mk_bv_sort 1 in
  let sortbv2 = mk_bv_sort 2 in
  let o0 = mk_const sortbv1 ~symbol:"o0" in
  let o1 = mk_const sortbv1 ~symbol:"o1" in
  let s0 = mk_const sortbv2 ~symbol:"s0" in
  let s1 = mk_const sortbv2 ~symbol:"s1" in
  let s2 = mk_const sortbv2 ~symbol:"s1" in
  let goal = mk_const sortbv2 ~symbol:"goal" in
  let zero = mk_bv_zero sortbv2
  and one1 = mk_bv_one sortbv1
  and one2 = mk_bv_one sortbv2
  and three = mk_bv_value_int sortbv2 3 in
  Solver.assert_formula bitwuzla (mk_term2 Equal s0 zero);
  Solver.assert_formula bitwuzla (mk_term2 Equal goal three);
  Solver.push bitwuzla 1;
  Solver.assert_formula bitwuzla (mk_term2 Equal s0 goal);
  let result = Solver.check_sat bitwuzla in
  result = Unsat
  && (Solver.pop bitwuzla 1;
      Solver.assert_formula bitwuzla
        (mk_term2 Equal s1
           (mk_term3 Ite (mk_term2 Equal o0 one1) (mk_term2 Bv_add s0 one2) s0));
      Solver.push bitwuzla 1;
      Solver.assert_formula bitwuzla (mk_term2 Equal s1 goal);
      let result = Solver.check_sat bitwuzla in
      result = Unsat)
  &&
  (Solver.pop bitwuzla 1;
   Solver.assert_formula bitwuzla
     (mk_term2 Equal s2
        (mk_term3 Ite (mk_term2 Equal o1 one1) (mk_term2 Bv_add s1 one2) s1));
   Solver.push bitwuzla 1;
   Solver.assert_formula bitwuzla (mk_term2 Equal s2 goal);
   let result = Solver.check_sat bitwuzla in
   result = Unsat)

let checksatassuming (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  let bitwuzla = Solver.create options in
  let sortbv1 = mk_bv_sort 1 in
  let sortbv2 = mk_bv_sort 2 in
  let o0 = mk_const sortbv1 ~symbol:"o0" in
  let o1 = mk_const sortbv1 ~symbol:"o1" in
  let s0 = mk_const sortbv2 ~symbol:"s0" in
  let s1 = mk_const sortbv2 ~symbol:"s1" in
  let s2 = mk_const sortbv2 ~symbol:"s1" in
  let goal = mk_const sortbv2 ~symbol:"goal" in
  let zero = mk_bv_zero sortbv2
  and one1 = mk_bv_one sortbv1
  and one2 = mk_bv_one sortbv2
  and three = mk_bv_value_int sortbv2 3 in
  Solver.assert_formula bitwuzla (mk_term2 Equal s0 zero);
  Solver.assert_formula bitwuzla (mk_term2 Equal goal three);
  let result =
    Solver.check_sat bitwuzla ~assumptions:[| mk_term2 Equal s0 goal |]
  in
  result = Unsat
  && (Solver.assert_formula bitwuzla
        (mk_term2 Equal s1
           (mk_term3 Ite (mk_term2 Equal o0 one1) (mk_term2 Bv_add s0 one2) s0));
      let result =
        Solver.check_sat bitwuzla ~assumptions:[| mk_term2 Equal s1 goal |]
      in
      result = Unsat)
  &&
  (Solver.assert_formula bitwuzla
     (mk_term2 Equal s2
        (mk_term3 Ite (mk_term2 Equal o1 one1) (mk_term2 Bv_add s1 one2) s1));
   let result =
     Solver.check_sat bitwuzla ~assumptions:[| mk_term2 Equal s2 goal |]
   in
   result = Unsat)

let unsatassumptions (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  Options.set options Produce_unsat_assumptions true;
  let bitwuzla = Solver.create options in
  let sortbool = mk_bool_sort () in
  let sortbv2 = mk_bv_sort 2 in
  let sortbv4 = mk_bv_sort 4 in
  let sortfp16 = mk_fp_sort 5 11 in
  let x0 = mk_const sortbv4 ~symbol:"x0" in
  let x1 = mk_const sortbv2 ~symbol:"x1" in
  let x2 = mk_const sortbv2 ~symbol:"x2" in
  let x3 = mk_const sortbv2 ~symbol:"x3" in
  let x4 = mk_const sortfp16 ~symbol:"x4" in
  let fpzero = mk_fp_pos_zero sortfp16 in
  let bvzero = mk_bv_zero sortbv4 in
  let a_f0 = mk_var sortfp16 ~symbol:"a_f0" in
  let f0 = mk_term2 Lambda a_f0 (mk_term2 Fp_gt a_f0 fpzero) in
  let a_f1 = mk_var sortfp16 ~symbol:"a_f1" in
  let f1 =
    mk_term2 Lambda a_f1 (mk_term3 Ite (mk_term2 Apply f0 a_f1) x0 bvzero)
  in
  let a_f2 = mk_var sortfp16 ~symbol:"a_f2" in
  let f2 =
    mk_term2 Lambda a_f2
      (mk_term1_indexed2 Bv_extract (mk_term2 Apply f1 a_f2) 1 0)
  in
  let a0 = mk_const sortbool ~symbol:"a0" in
  let assumption0 = mk_term2 Bv_ult x2 (mk_term2 Apply f2 fpzero) in
  Solver.assert_formula bitwuzla (mk_term2 Equal a0 assumption0);
  let a1 = mk_const sortbool ~symbol:"a1" in
  let assumption1 = mk_term Equal [| x1; x2; x3 |] in
  Solver.assert_formula bitwuzla (mk_term2 Equal a1 assumption1);
  let a2 = mk_const sortbool ~symbol:"a2" in
  let assumption2 =
    mk_term2 Equal x4
      (mk_term2_indexed2 Fp_to_fp_from_ubv (mk_rm_value Rne) x3 5 11)
  in
  Solver.assert_formula bitwuzla (mk_term2 Equal a2 assumption2);
  let result = Solver.check_sat bitwuzla ~assumptions:[| a0; a1; a2 |] in
  result = Unsat
  &&
  let unsat_assumptions = Solver.get_unsat_core bitwuzla in
  Array.mem a0 unsat_assumptions

let unsatcore (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  Options.set options Produce_unsat_cores true;
  let bitwuzla = Solver.create options in
  let sortbv2 = mk_bv_sort 2 in
  let sortbv4 = mk_bv_sort 4 in
  let sortfp16 = mk_fp_sort 5 11 in
  let x0 = mk_const sortbv4 ~symbol:"x0" in
  let x1 = mk_const sortbv2 ~symbol:"x1" in
  let x2 = mk_const sortbv2 ~symbol:"x2" in
  let x3 = mk_const sortbv2 ~symbol:"x3" in
  let x4 = mk_const sortfp16 ~symbol:"x4" in
  let fpzero = mk_fp_pos_zero sortfp16 in
  let bvzero = mk_bv_zero sortbv4 in
  let a_f0 = mk_var sortfp16 ~symbol:"a_f0" in
  let f0 = mk_term2 Lambda a_f0 (mk_term2 Fp_gt a_f0 fpzero) in
  let a_f1 = mk_var sortfp16 ~symbol:"a_f1" in
  let f1 =
    mk_term2 Lambda a_f1 (mk_term3 Ite (mk_term2 Apply f0 a_f1) x0 bvzero)
  in
  let a_f2 = mk_var sortfp16 ~symbol:"a_f2" in
  let f2 =
    mk_term2 Lambda a_f2
      (mk_term1_indexed2 Bv_extract (mk_term2 Apply f1 a_f2) 1 0)
  in
  let a0 = mk_term2 Bv_ult x2 (mk_term2 Apply f2 fpzero) in
  Solver.assert_formula bitwuzla a0;
  let a1 = mk_term Equal [| x1; x2; x3 |] in
  Solver.assert_formula bitwuzla a1;
  let a2 =
    mk_term2 Equal x4
      (mk_term2_indexed2 Fp_to_fp_from_ubv (mk_rm_value Rne) x3 5 11)
  in
  Solver.assert_formula bitwuzla a2;
  let result = Solver.check_sat bitwuzla in
  result = Unsat
  &&
  let unsat_core = Solver.get_unsat_core bitwuzla in
  Array.mem a0 unsat_core

let terminator (m : (module Bitwuzla_cxx.S)) : bool =
  let open (val m) in
  let options = Options.default () in
  let bitwuzla = Solver.create options in
  let bv = mk_bv_sort 32 in
  let x = mk_const bv and s = mk_const bv and t = mk_const bv in
  let a =
    mk_term2 Distinct
      (mk_term2 Bv_mul s (mk_term2 Bv_mul x t))
      (mk_term2 Bv_mul (mk_term2 Bv_mul s x) t)
  in
  Solver.check_sat bitwuzla ~assumptions:[| a |] = Unsat
  &&
  (Options.set options Preprocess false;
   let bitwuzla2 = Solver.create options in
   let terminator = timeout 1. in
   Solver.configure_terminator bitwuzla2 (Some terminator);
   Solver.check_sat bitwuzla2 ~assumptions:[| a |] = Unknown)

let examples =
  [|
    quickstart;
    pushpop;
    checksatassuming;
    unsatassumptions;
    unsatcore;
    terminator;
  |]

let n = Array.length examples

let run i () =
  let module M = Bitwuzla_cxx.Make () in
  try
    Array.for_all
      (fun f -> f (module M : Bitwuzla_cxx.S))
      (Array.init n (fun j -> Array.get examples ((i + j) mod n)))
  with _ -> false

let%test "domains" =
  Array.for_all Fun.id
    (Array.map Domain.join
       (Array.init (Domain.recommended_domain_count ()) (fun i ->
            Domain.spawn (run i))))

let%test "issues/7" =
  let run () =
    let module M = Bitwuzla_cxx.Make () in
    let _ = M.mk_bool_sort () in
    true
  in
  Array.for_all Fun.id
    (Array.map Domain.join
       (Array.init (Domain.recommended_domain_count ()) (fun _ ->
            Domain.spawn run)))
