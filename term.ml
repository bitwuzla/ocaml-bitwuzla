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

type t

external id : t -> (int64[@unboxed])
  = "ocaml_bitwuzla_cxx_term_id" "native_bitwuzla_cxx_term_id"

external compare : t -> t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_compare" "native_bitwuzla_cxx_term_compare"

external equal : t -> t -> bool = "ocaml_bitwuzla_cxx_term_equal"

external hash : t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_hash" "native_bitwuzla_cxx_term_hash"

external kind : t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_kind" "native_bitwuzla_cxx_term_kind"

let kind t = Kind.of_cxx @@ kind t

external sort : t -> Sort.t = "ocaml_bitwuzla_cxx_term_sort"

external num_children : t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_num_children"
    "native_bitwuzla_cxx_term_num_children"

external children : t -> t array = "ocaml_bitwuzla_cxx_term_children"

external get : t -> (int[@untagged]) -> t
  = "ocaml_bitwuzla_cxx_term_get" "native_bitwuzla_cxx_term_get"

external num_indices : t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_num_indices" "native_bitwuzla_cxx_term_num_indices"

external indices : t -> int array = "ocaml_bitwuzla_cxx_term_indices"
external symbol : t -> string = "ocaml_bitwuzla_cxx_term_symbol"
external is_const : t -> bool = "ocaml_bitwuzla_cxx_term_is_const" [@@noalloc]

external is_variable : t -> bool = "ocaml_bitwuzla_cxx_term_is_variable"
[@@noalloc]

external is_value : t -> bool = "ocaml_bitwuzla_cxx_term_is_value" [@@noalloc]

external is_bv_value_zero : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_bv_value_zero"
[@@noalloc]

external is_bv_value_one : t -> bool = "ocaml_bitwuzla_cxx_term_is_bv_value_one"
[@@noalloc]

external is_bv_value_ones : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_bv_value_ones"
[@@noalloc]

external is_bv_value_min_signed : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_bv_value_min_signed"
[@@noalloc]

external is_bv_value_max_signed : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_bv_value_max_signed"
[@@noalloc]

external is_fp_value_pos_zero : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_fp_value_pos_zero"
[@@noalloc]

external is_fp_value_neg_zero : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_fp_value_neg_zero"
[@@noalloc]

external is_fp_value_pos_inf : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_fp_value_pos_inf"
[@@noalloc]

external is_fp_value_neg_inf : t -> bool
  = "ocaml_bitwuzla_cxx_term_is_fp_value_neg_inf"
[@@noalloc]

external is_fp_value_nan : t -> bool = "ocaml_bitwuzla_cxx_term_is_fp_value_nan"
[@@noalloc]

external is_rm_value_rna : t -> bool = "ocaml_bitwuzla_cxx_term_is_rm_value_rna"
[@@noalloc]

external is_rm_value_rne : t -> bool = "ocaml_bitwuzla_cxx_term_is_rm_value_rne"
[@@noalloc]

external is_rm_value_rtn : t -> bool = "ocaml_bitwuzla_cxx_term_is_rm_value_rtn"
[@@noalloc]

external is_rm_value_rtp : t -> bool = "ocaml_bitwuzla_cxx_term_is_rm_value_rtp"
[@@noalloc]

external is_rm_value_rtz : t -> bool = "ocaml_bitwuzla_cxx_term_is_rm_value_rtz"
[@@noalloc]

external to_string : (int[@untagged]) -> t -> string
  = "ocaml_bitwuzla_cxx_term_to_string" "native_bitwuzla_cxx_term_to_string"

let to_string ?(bv_format = 2) t = to_string bv_format t

external pp : Format.formatter -> t -> unit = "ocaml_bitwuzla_cxx_term_pp"

external pp_smt2 : bv_format:(int[@untagged]) -> Format.formatter -> t -> unit
  = "ocaml_bitwuzla_cxx_term_pp_smt2" "native_bitwuzla_cxx_term_pp_smt2"

external to_bool : t -> bool = "ocaml_bitwuzla_cxx_term_boolean_value"

external to_rounding_mode : t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_term_rounding_mode_value"
    "native_bitwuzla_cxx_term_rounding_mode_value"

external to_base : t -> (int[@untagged]) -> string
  = "ocaml_bitwuzla_cxx_term_string_value"
    "native_bitwuzla_cxx_term_string_value"

external to_ieee_754 : t -> string * string * string
  = "ocaml_bitwuzla_cxx_term_ieee_754_value"

external to_zarith : t -> Z.t = "ocaml_bitwuzla_cxx_term_zarith_value"

type _ cast =
  | Bool : bool cast
  | RoundingMode : RoundingMode.t cast
  | String : { base : int } -> string cast
  | IEEE_754 : (string * string * string) cast
  | Z : Z.t cast

let value : type a. a cast -> t -> a =
 fun kind t ->
  match kind with
  | Bool -> to_bool t
  | RoundingMode -> RoundingMode.of_cxx (to_rounding_mode t)
  | String { base } -> to_base t base
  | IEEE_754 -> to_ieee_754 t
  | Z -> to_zarith t
