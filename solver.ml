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

external create : Options.t -> t = "ocaml_bitwuzla_cxx_new"

external unsafe_delete : t -> unit = "ocaml_bitwuzla_cxx_delete"

external configure_terminator : t -> (unit -> bool) option -> unit
  = "ocaml_bitwuzla_cxx_configure_terminator"

external push : t -> (int[@untagged]) -> unit
  = "ocaml_bitwuzla_cxx_push" "native_bitwuzla_cxx_push"

external pop : t -> (int[@untagged]) -> unit
  = "ocaml_bitwuzla_cxx_pop" "native_bitwuzla_cxx_pop"

external assert_formula : t -> Term.t -> unit
  = "ocaml_bitwuzla_cxx_assert_formula"

external get_assertions : t -> Term.t array
  = "ocaml_bitwuzla_cxx_get_assertions"

external pp_formula : Format.formatter -> t -> unit
  = "ocaml_bitwuzla_cxx_pp_formula"

external pp_statistics : Format.formatter -> t -> unit
  = "ocaml_bitwuzla_cxx_pp_statistics"

external is_unsat_assumption : t -> Term.t -> bool
  = "ocaml_bitwuzla_cxx_is_unsat_assumption"

external get_unsat_assumptions : t -> Term.t array
  = "ocaml_bitwuzla_cxx_get_unsat_assumptions"

external get_unsat_core : t -> Term.t array
  = "ocaml_bitwuzla_cxx_get_unsat_core"

external simplify : t -> unit = "ocaml_bitwuzla_cxx_simplify"

external check_sat : Term.t array -> t -> (int[@untagged])
  = "ocaml_bitwuzla_cxx_check_sat" "native_bitwuzla_cxx_check_sat"

let check_sat ?(assumptions = [||]) t = Result.of_cxx @@ check_sat assumptions t

external get_value : t -> Term.t -> Term.t = "ocaml_bitwuzla_cxx_get_value"
