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
  = "ocaml_bitwuzla_sort_id" "native_bitwuzla_sort_id"

external compare : t -> t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_compare" "native_bitwuzla_sort_compare"

external equal : t -> t -> bool = "ocaml_bitwuzla_sort_equal"

external hash : t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_hash" "native_bitwuzla_sort_hash"

external bv_size : t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_bv_size" "native_bitwuzla_sort_bv_size"

external fp_exp_size : t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_fp_exp_size" "native_bitwuzla_sort_fp_exp_size"

external fp_sig_size : t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_fp_sig_size" "native_bitwuzla_sort_fp_sig_size"

external array_index : t -> t = "ocaml_bitwuzla_sort_array_index"

external array_element : t -> t = "ocaml_bitwuzla_sort_array_element"

external fun_domain : t -> t array = "ocaml_bitwuzla_sort_fun_domain"

external fun_codomain : t -> t = "ocaml_bitwuzla_sort_fun_codomain"

external fun_arity : t -> (int[@untagged])
  = "ocaml_bitwuzla_sort_fun_arity" "native_bitwuzla_sort_fun_arity"

external uninterpreted_symbol : t -> string
  = "ocaml_bitwuzla_sort_uninterpreted_symbol"

external is_array : t -> bool = "ocaml_bitwuzla_sort_is_array" [@@noalloc]

external is_bool : t -> bool = "ocaml_bitwuzla_sort_is_bool" [@@noalloc]

external is_bv : t -> bool = "ocaml_bitwuzla_sort_is_bv" [@@noalloc]

external is_fp : t -> bool = "ocaml_bitwuzla_sort_is_fp" [@@noalloc]

external is_fun : t -> bool = "ocaml_bitwuzla_sort_is_fun" [@@noalloc]

external is_rm : t -> bool = "ocaml_bitwuzla_sort_is_rm" [@@noalloc]

external is_uninterpreted : t -> bool = "ocaml_bitwuzla_sort_is_uninterpreted"
  [@@noalloc]

external to_string : t -> string = "ocaml_bitwuzla_sort_to_string"

external pp : Format.formatter -> t -> unit = "ocaml_bitwuzla_sort_pp"
