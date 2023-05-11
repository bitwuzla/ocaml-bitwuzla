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
  (* First, create a Bitwuzla options instance. *)
  let options = Options.default () in
  (* Then, enable model generation. *)
  Options.set options Produce_models true;
  (* Then, create a Bitwuzla instance. *)
  let bitwuzla = Solver.create options in

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

  (* (check-sat) *)
  let result = Solver.check_sat bitwuzla in

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

  (* Print value for x, y, f and a. *)
  (* Both x and y are bit-vector terms and their value is a bit-vector *)
  (* value that can be printed via Term.value. *)
  Format.printf "value of x: %s@,"
    (Term.value (String { base = 2 }) (Solver.get_value bitwuzla x));
  Format.printf "value of y: %s@,"
    (Term.value (String { base = 2 }) (Solver.get_value bitwuzla y));
  Format.print_space ();

  (* f and a, on the other hand, are a function and array term, respectively. *)
  (* The value of these terms is not a value term: for f, it is a lambda *)
  (* term, and the value of a is represented as a store term. Thus we cannot *)
  (*  use Term.value, but we can print the value of the terms via Term.pp. *)
  Format.printf "str() representation of value of f:@,%a@," Term.pp
    (Solver.get_value bitwuzla f);
  Format.printf "str() representation of value of a:@,%a@," Term.pp
    (Solver.get_value bitwuzla a);
  Format.print_space ();

  (* Note that the assignment string of bit-vector terms is given as the *)
  (* pure assignment string, either in binary, hexadecimal or decimal format, *)
  (* whereas Term.pp print the value in SMT-LIB2 format *)
  (* (in binary number format). *)
  Format.printf "str() representation of value of x:@,%a@," Term.pp
    (Solver.get_value bitwuzla x);
  Format.printf "str() representation of value of y:@,%a@," Term.pp
    (Solver.get_value bitwuzla y);
  Format.print_space ();

  (* Query value of bit-vector term that does not occur in the input formula *)
  let v = Solver.get_value bitwuzla (mk_term2 Bv_mul x x) in
  Format.printf "value of v = x * x: %s@," (Term.value (String { base = 2 }) v);

  Format.close_box ()
