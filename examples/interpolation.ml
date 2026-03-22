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

  let sortbv2 = mk_bv_sort 2 in
  let sortbv4 = mk_bv_sort 4 in

  let x1 = mk_const sortbv2 ~symbol:"x1" in
  let x2 = mk_const sortbv2 ~symbol:"x2" in
  let x3 = mk_const sortbv2 ~symbol:"x3" in
  let a1 =
    mk_term2 Bv_slt (mk_bv_zero sortbv4)
      (mk_term2 Bv_sub
         (mk_term1_indexed1 Bv_zero_extend x1 2)
         (mk_bv_one sortbv4))
  in
  let a2 = mk_term2 Equal x1 x2 in
  let a3 =
    mk_term2 Equal x3
      (mk_term1_indexed2 Bv_extract
         (mk_term1 Bv_neg (mk_term1_indexed1 Bv_zero_extend x2 2))
         1 0)
  in
  let a4 = mk_term2 Equal x3 (mk_bv_zero sortbv2) in
  let options = Options.default () in
  Options.set options Produce_interpolants true;
  Options.set options Interpolants_simp true;
  let bitwuzla = Solver.create options in
  Solver.assert_formula bitwuzla a1;
  Solver.assert_formula bitwuzla a2;
  Solver.assert_formula bitwuzla a3;
  Solver.assert_formula bitwuzla a4;
  ignore (Solver.check_sat bitwuzla);

  (* Query an interpolant for A /\ B with A = {a1, a2}. *)
  let interpolant = Solver.get_interpolant bitwuzla [| a1; a2 |] in
  (* (not (= x2 #b00)) *)
  Format.printf "%a@ " Term.pp interpolant;

  (* Query an interpolation sequence for a sequence of A/B-partitions
       {
         ({a1},        {a2, a3, a4}),
         ({a1, a2},    {a3, a4}),
         ({a1, a2, a3, {a4})
       }
     given as a list {{a1}, {a2}, {a3}} of increments of A. *)
  let interpolants =
    Solver.get_interpolants bitwuzla [| [| a1 |]; [| a2 |]; [| a3 |] |]
  in
  (* [0]: (= ((_ extract 3 3) (bvadd (concat #b00 x1) #b1111)) #b0) *)
  (* [1]: (not (= x2 #b00)) *)
  (* [2]: (not (= x3 #b00)) *)
  Format.printf "@[<v>(@ %a)@]"
    (fun ppf interpolants ->
      Array.iter
        (fun term ->
          Term.pp ppf term;
          Format.pp_print_space ppf ())
        interpolants)
    interpolants;

  Format.close_box ()
