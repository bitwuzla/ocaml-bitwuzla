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

external copyright : unit -> string = "ocaml_bitwuzla_cxx_copyright"

external version : unit -> string = "ocaml_bitwuzla_cxx_version"

external init_format : unit -> unit = "ocaml_bitwuzla_cxx_init_format"

let () =
  Callback.register "Format.pp_open_vbox" Format.pp_open_vbox;
  Callback.register "Format.pp_print_string" Format.pp_print_string;
  Callback.register "Format.pp_print_char" Format.pp_print_char;
  Callback.register "Format.pp_print_space" Format.pp_print_space;
  Callback.register "Format.pp_close_box" Format.pp_close_box;
  init_format ()

module Options = Options
module Sort = Sort

external mk_array_sort : Sort.t -> Sort.t -> Sort.t
  = "ocaml_bitwuzla_cxx_mk_array_sort"

external mk_bool_sort : unit -> Sort.t = "ocaml_bitwuzla_cxx_mk_bool_sort"

external mk_bv_sort : (int[@untagged]) -> Sort.t
  = "ocaml_bitwuzla_cxx_mk_bv_sort" "native_bitwuzla_cxx_mk_bv_sort"

external mk_fp_sort : (int[@untagged]) -> (int[@untagged]) -> Sort.t
  = "ocaml_bitwuzla_cxx_mk_fp_sort" "native_bitwuzla_cxx_mk_fp_sort"

external mk_fun_sort : Sort.t array -> Sort.t -> Sort.t
  = "ocaml_bitwuzla_cxx_mk_fun_sort"

external mk_rm_sort : unit -> Sort.t = "ocaml_bitwuzla_cxx_mk_rm_sort"

external mk_uninterpreted_sort : ?symbol:string -> unit -> Sort.t
  = "ocaml_bitwuzla_cxx_mk_uninterpreted_sort"

module RoundingMode = RoundingMode
module Kind = Kind
module Term = Term

external mk_true : unit -> Term.t = "ocaml_bitwuzla_cxx_mk_true"

external mk_false : unit -> Term.t = "ocaml_bitwuzla_cxx_mk_false"

external mk_bv_zero : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_bv_zero"

external mk_bv_one : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_bv_one"

external mk_bv_ones : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_bv_ones"

external mk_bv_min_signed : Sort.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_bv_min_signed"

external mk_bv_max_signed : Sort.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_bv_max_signed"

external mk_bv_value : Sort.t -> string -> (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_bv_value" "native_bitwuzla_cxx_mk_bv_value"

external mk_bv_value_int : Sort.t -> (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_bv_value_int" "native_bitwuzla_cxx_mk_bv_value_int64"

external mk_bv_value_int64 : Sort.t -> (int64[@unboxed]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_bv_value_int64" "native_bitwuzla_cxx_mk_bv_value_int64"

external mk_fp_pos_zero : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_fp_pos_zero"

external mk_fp_neg_zero : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_fp_neg_zero"

external mk_fp_pos_inf : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_fp_pos_inf"

external mk_fp_neg_inf : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_fp_neg_inf"

external mk_fp_nan : Sort.t -> Term.t = "ocaml_bitwuzla_cxx_mk_fp_nan"

external mk_fp_value : Term.t -> Term.t -> Term.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_fp_value"

external mk_fp_value_from_real : Sort.t -> Term.t -> string -> Term.t
  = "ocaml_bitwuzla_cxx_mk_fp_value_from_real"

external mk_fp_value_from_rational :
  Sort.t -> Term.t -> string -> string -> Term.t
  = "ocaml_bitwuzla_cxx_mk_fp_value_from_rational"

external mk_rm_value : (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_rm_value" "native_bitwuzla_cxx_mk_rm_value"

let mk_rm_value t = mk_rm_value (RoundingMode.to_cxx t)

external mk_term1 : (int[@untagged]) -> Term.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term1" "native_bitwuzla_cxx_mk_term1"

let mk_term1 k t = mk_term1 (Kind.to_cxx k) t

external mk_term2 : (int[@untagged]) -> Term.t -> Term.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term2" "native_bitwuzla_cxx_mk_term2"

let mk_term2 k t1 t2 = mk_term2 (Kind.to_cxx k) t1 t2

external mk_term3 : (int[@untagged]) -> Term.t -> Term.t -> Term.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term3" "native_bitwuzla_cxx_mk_term3"

let mk_term3 k t1 t2 t3 = mk_term3 (Kind.to_cxx k) t1 t2 t3

external mk_term1_indexed1 :
  (int[@untagged]) -> Term.t -> (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term1_indexed1" "native_bitwuzla_cxx_mk_term1_indexed1"

let mk_term1_indexed1 k t i = mk_term1_indexed1 (Kind.to_cxx k) t i

external mk_term1_indexed2 :
  (int[@untagged]) -> Term.t -> (int[@untagged]) -> (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term1_indexed2" "native_bitwuzla_cxx_mk_term1_indexed2"

let mk_term1_indexed2 k t i j = mk_term1_indexed2 (Kind.to_cxx k) t i j

external mk_term2_indexed1 :
  (int[@untagged]) -> Term.t -> Term.t -> (int[@untagged]) -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term2_indexed1" "native_bitwuzla_cxx_mk_term2_indexed1"

let mk_term2_indexed1 k t1 t2 i = mk_term2_indexed1 (Kind.to_cxx k) t1 t2 i

external mk_term2_indexed2 :
  (int[@untagged]) ->
  Term.t ->
  Term.t ->
  (int[@untagged]) ->
  (int[@untagged]) ->
  Term.t
  = "ocaml_bitwuzla_cxx_mk_term2_indexed2" "native_bitwuzla_cxx_mk_term2_indexed2"

let mk_term2_indexed2 k t1 t2 i j = mk_term2_indexed2 (Kind.to_cxx k) t1 t2 i j

external mk_term : (int[@untagged]) -> Term.t array -> int array -> Term.t
  = "ocaml_bitwuzla_cxx_mk_term" "native_bitwuzla_cxx_mk_term"

let mk_term k ?(indices = [||]) args = mk_term (Kind.to_cxx k) args indices

external mk_const : ?symbol:string -> Sort.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_const"

external mk_const_array : Sort.t -> Term.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_const_array"

external mk_var : ?symbol:string -> Sort.t -> Term.t
  = "ocaml_bitwuzla_cxx_mk_var"

external substitute_term : Term.t -> (Term.t * Term.t) array -> Term.t
  = "ocaml_bitwuzla_cxx_substitute_term"

external substitute_terms : Term.t array -> (Term.t * Term.t) array -> unit
  = "ocaml_bitwuzla_cxx_substitute_terms"

module Result = Result
module Solver = Solver
