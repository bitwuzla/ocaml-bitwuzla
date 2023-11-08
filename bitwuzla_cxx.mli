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

(** This is a straight one to one binding of the Bitwuzla C++ API.
    @see <https://bitwuzla.github.io/docs/cpp/api.html> *)

val copyright : unit -> string
(**
   [copyright ()]
   get copyright information.
*)

val version : unit -> string
(**
   [version ()]
   get version information.
*)

module Options : sig
  (** {1:options Options} *)

  (** The options supported by Bitwuzla. *)
  type _ key =
    | Log_level : int key
        (** Log level.

            Values:
            - An unsigned integer value ({b default}: [0]).
        *)
    | Produce_models : bool key
        (** Model generation.

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\]

            This option cannot be enabled in combination with option
            [Pp_unconstrained_optimization].
        *)
    | Produce_unsat_assumptions : bool key
        (** Unsat assumptions generation.

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\]
        *)
    | Produce_unsat_cores : bool key
        (** Unsat core generation.

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\].
        *)
    | Seed : int key
        (** Seed for random number generator.

            Values:
            - An unsigned integer value \[{b default}: [42]\].
        *)
    | Verbosity : int key
        (** Verbosity level.

            Values:
            - An unsigned integer value <= 4 \[{b default}: [0]\].
        *)
    | Time_limit_per : int key
        (** Time limit in milliseconds per satisfiability check.**

            Values:
            - An unsigned integer for the time limit in milliseconds.
            \[{b default}: [0]\].
        *)
    | Bv_solver : bv_solver key
    | Rewrite_level : int key
        (** Rewrite level.

            Values:
            - [0]: no rewriting
            - [1]: term level rewriting
            - [2]: term level rewriting and full preprocessing \[{b default}\]

            This is an expert option to configure rewriting.
        *)
    | Sat_solver : sat_solver key
        (** Configure the SAT solver engine.

            Values:
            - [Cadical] \[{b default}\]:
            \[CaDiCaL\](https://github.com/arminbiere/cadical)
            - [Cms]:
            \[CryptoMiniSat\](https://github.com/msoos/cryptominisat)
            - [Kissat]:
            \[Kissat\](https://github.com/arminbiere/kissat)
        *)
    | Prop_const_bits : bool key
        (** Propagation-based local search solver engine:
            Constant bits.

            Configure constant bit propagation (requries bit-blasting to AIG).

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_ineq_bounds : bool key
        (** Propagation-based local search solver engine:
            Infer bounds for inequalities for value computation.

            When enabled, infer bounds for value computation for inequalities
            based on satisfied top level inequalities.

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\]

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_nprops : int key
        (** Propagation-based local search solver engine:
            Number of propagations.

            Configure the number of propagations used as a limit for the
            propagation-based local search solver engine. No limit if 0.

            Values:
            - An unsigned integer value \[{b default}: [0]\].

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_nupdates : int key
        (** Propagation-based local search solver engine:
            Number of updates.

            Configure the number of model value updates used as a limit for the
            propagation-based local search solver engine. No limit if 0.

            Values:
            - An unsigned integer value \[{b default}: [0]\].

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_opt_lt_concat_sext : bool key
        (** Propagation-based local search solver engine:
        Optimization for inverse value computation of inequalities over
        concat and sign extension operands.

        When enabled, use optimized inverse value value computation for
        inequalities over concats.

        Values:
        - [true]: enable
        - [false]: disable \[{b default}\]

        This is an expert option to configure the prop solver engine.
    *)
    | Prop_path_sel : prop_path_sel key
        (** Propagation-based local search solver engine:
            Path selection.

            Configure mode for path selection.

            Values:
            - [Essential] \[{b default}\]:
            Select path based on essential inputs.
            - [Random]:
            Select path randomly.

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_prob_pick_rand_input : int key
        (** Propagation-based local search solver engine:
            Probability for selecting random input.

            Configure the probability with which to select a random input
            instead of an essential input when selecting the path.

            Values:
            - An unsigned integer value <= 1000 (= 100%) \[{b default}: [0]\].

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_prob_pick_inv_value : int key
        (** Propagation-based local search solver engine:
            Probability for inverse values.

            Configure the probability with which to choose an inverse value
            over a consistent value when aninverse value exists.

            Values:
            - An unsigned integer value <= 1000 (= 100%) \[{b default}: [990]\].

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_sext : bool key
        (** Propagation-based local search solver engine:
            Value computation for sign extension.

            When enabled, detect sign extension operations (are rewritten on
            construction) and use value computation for sign extension.

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\]

            This is an expert option to configure the prop solver engine.
        *)
    | Prop_normalize : bool key
        (** Propagation-based local search solver engine:
            Local search specific normalization.

            When enabled, perform normalizations for local search, on the local
            search layer (does not affect node layer).

            Values:
            - [true]: enable
            - [false]: disable \[{b default}\]

            This is an expert option to configure the prop solver engine.
        *)
    | Preprocess : bool key
        (** Preprocessing

            When enabled, applies all enabled preprocessing passes.

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_contr_ands : bool key
        (** Preprocessing: Find contradicting bit-vector ands

            When enabled, substitutes contradicting nodes of kind #BV_AND
            with zero.

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_elim_extracts : bool key
        (** Preprocessing: Eliminate bit-vector extracts on bit-vector constants

            When enabled, eliminates bit-vector extracts on constants.

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_embedded : bool key
        (** Preprocessing: Embedded constraint substitution

            When enabled, substitutes assertions that occur as sub-expression in
            the formula with their respective Boolean value.

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_flatten_and : bool key
        (** Preprocessing: AND flattening

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_normalize : bool key
        (** Preprocessing: Normalization

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_normalize_share_aware : bool key
        (** Preprocessing: Normalization: Enable share awareness normlization

            When enabled, this disables normalizations that may yield blow-up
            on the bit-level.

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_skeleton_preproc : bool key
        (** Preprocessing: Boolean skeleton preprocessing

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_variable_subst : bool key
        (** Preprocessing: Variable substitution

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_variable_subst_norm_eq : bool key
        (** Preprocessing: Variable substitution: Equality Normalization

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_variable_subst_norm_diseq : bool key
        (** Preprocessing: Variable substitution:
            Bit-Vector Inequality Normalization

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Pp_variable_subst_norm_bv_ineq : bool key
        (** Preprocessing: Variable substitution: Bit-Vector Inequality

            Values:
            - [true]: enable \[{b default}\]
            - [false]: disable
        *)
    | Dbg_rw_node_thresh : int key
        (** Debug:
            Threshold for number of new nodes introduced for recursive call of
            rewrite().

            Prints a warning number of newly introduced nodes is above
            threshold.

            This is an expert debug option.
        *)
    | Dbg_pp_node_thresh : int key
        (** Debug:
            Threshold for formula size increase after preprocessing in percent.

            Prints a warning if formula size increase is above threshold.

            This is an expert debug option.
        *)
    | Check_model : bool key
        (** Debug: Check models for each satisfiable query.

            This is an expert debug option.
        *)
    | Check_unsat_core : bool key
        (** Debug: Check unsat core for each unsatisfiable query.

            This is an expert debug option.
        *)

  and bv_solver = Bitblast | Preprop | Prop

  and sat_solver = Cadical | Cms | Kissat

  and prop_path_sel = Essential | Random

  val to_string : 'a key -> string
  (** [to_string opt] Returns the long name of this option. *)

  val description : 'a key -> string
  (** [description opt] Returns the description of this option. *)

  val default_value : 'a key -> 'a
  (** [default_value opt] Returns the default value of this option. *)

  val min : int key -> int
  (** [min opt] Returns the minimum numeric option value. *)

  val max : int key -> int
  (** [max opt] Returns the maximum numeric option value. *)

  (** {1:config Option set} *)

  type t
  (** A given set of options. *)

  val default : unit -> t
  (** [default ()] creates a set of options initialized with default values. *)

  val set : t -> 'a key -> 'a -> unit
  (** [set t opt value] set option value. *)

  val get : t -> 'a key -> 'a
  (** [get t opt] get the current option value. *)
end

module type S = sig
  (** Signature of a Bitwuzla instance.

    Each instance can create and share {!module:Term}s between several
    {!module:Solver}s.
    However, an instance is not thread safe. Thus multicore users should ensure
    that only one Domain uses a bitwuzla instance at a given time.
  *)

  module Sort : sig
    (** {1:sort Sort} *)

    type t
    (** A Bitwuzla sort. *)

    (** {2:sort_util Util} *)

    val hash : t -> int
    (**
     [hash t]
     compute the hash value for a sort.

     @param t The sort.

     @return The hash value of the sort.
  *)

    val equal : t -> t -> bool
    (**
     [equal a b]
     Syntactical equality operator.

     @param a The first sort.
     @param b The second sort.
     @return True if the given sorts are equal.
  *)

    val compare : t -> t -> int
    (**
     [compare a b]
     Syntactical comparison operator.

     @param a The first sort.
     @param b The second sort.
     @return Zero if the given sorts are equal,
             a positive number if [a] > [b],
             a negative number otherwise.
  *)

    val pp : Format.formatter -> t -> unit
    (**
     [pp formatter t]
     print sort.

     @param t The sort.
     @param formatter The outpout formatter.
  *)

    val to_string : t -> string
    (**
     [to_string t]
     get string representation of this sort.

     @return String representation of this sort.
  *)

    (** {2:sort_query Query} *)

    val id : t -> int64
    (**
     [id t]
     get the id of this sort.

     @param t The sort.
     @return The id value of the sort.
  *)

    val bv_size : t -> int
    (**
     [bv_size t]
     get the size of a bit-vector sort.

     Requires that given sort is a bit-vector sort.

     @param t The sort.

     @return The size of the bit-vector sort.
  *)

    val fp_exp_size : t -> int
    (**
     [fp_exp_size sort]
     get the exponent size of a floating-point sort.

     Requires that given sort is a floating-point sort.

     @param t The sort.

     @return The exponent size of the floating-point sort.
  *)

    val fp_sig_size : t -> int
    (**
     [fp_sig_size t]
     get the significand size of a floating-point sort.

     Requires that given sort is a floating-point sort.

     @param t The sort.

     @return The significand size of the floating-point sort.
  *)

    val array_index : t -> t
    (**
     [array_index t]
     get the index sort of an array sort.

     Requires that given sort is an array sort.

     @param t The sort.

     @return The index sort of the array sort.
  *)

    val array_element : t -> t
    (**
     [array_element t]
     get the element sort of an array sort.

     Requires that given sort is an array sort.

     @param t The sort.

     @return The element sort of the array sort.
  *)

    val fun_domain : t -> t array
    (**
     [fun_domain_sorts t]
     get the domain sorts of a function sort.

     Requires that given sort is a function sort.

     @param t The sort.

     @return The domain sorts of the function sort as an array of sort.
  *)

    val fun_codomain : t -> t
    (**
     [fun_codomain t]
     get the codomain sort of a function sort.

     Requires that given sort is a function sort.

     @param t The sort.

     @return The codomain sort of the function sort.
  *)

    val fun_arity : t -> int
    (**
     [fun_arity t]
     get the arity of a function sort.

     @param t The sort.

     @return The number of arguments of the function sort.
  *)

    val uninterpreted_symbol : t -> string
    (**
     [uninterpreted_symbol t]
     get the symbol of an uninterpreted sort.

     @param t The sort.

     @return The symbol.

     @raise Not_found if no symbol is defined.
  *)

    val is_array : t -> bool
    (**
     [is_array t]
     determine if a sort is an array sort.

     @param t The sort.

     @return [true] if [t] is an array sort.
  *)

    val is_bool : t -> bool
    (**
     [is_bool t]
     determine if a sort is a Boolean sort.

     @param t The sort.

     @return [true] if [t] is a Boolean sort.
  *)

    val is_bv : t -> bool
    (**
     [is_bv t]
     determine if a sort is a bit-vector sort.

     @param t The sort.

     @return [true] if [t] is a bit-vector sort.
  *)

    val is_fp : t -> bool
    (**
     [is_fp t]
     determine if a sort is a floating-point sort.

     @param t The sort.

     @return [true] if [t] is a floating-point sort.
  *)

    val is_fun : t -> bool
    (**
     [is_fun t]
     determine if a sort is a function sort.

     @param t The sort.

     @return [true] if [t] is a function sort.
  *)

    val is_rm : t -> bool
    (**
     [is_rm t]
     determine if a sort is a Roundingmode sort.

     @param t The sort.

     @return [true] if [t] is a Roundingmode sort.
  *)

    val is_uninterpreted : t -> bool
    (**
     [is_uninterpreted t]
     determine if a sort is an uninterpreted sort.

     @param t The sort.

     @return [true] if [t] is an uninterpreted sort.
  *)
  end

  module RoundingMode : sig
    (**
     Rounding mode for floating-point operations.

     For some floating-point operations, infinitely precise results may not be
     representable in a given format. Hence, they are rounded modulo one of five
     rounding modes to a representable floating-point number.

     The following rounding modes follow the SMT-LIB theory for floating-point
     arithmetic, which in turn is based on IEEE Standard 754.
     The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
     Standard 754.
  *)
    type t =
      | Rne
          (** Round to the nearest even number.
        If the two nearest floating-point numbers bracketing an unrepresentable
        infinitely precise result are equally near, the one with an even least
        significant digit will be delivered.

        SMT-LIB: [RNE] roundNearestTiesToEven
    *)
      | Rna
          (** Round to the nearest number away from zero.
        If the two nearest floating-point numbers bracketing an unrepresentable
        infinitely precise result are equally near, the one with larger
        magnitude will be selected.

        SMT-LIB: [RNA] roundNearestTiesToAway
    *)
      | Rtn
          (** Round towards negative infinity (-oo).
        The result shall be the format’s floating-point number (possibly -oo)
        closest to and no less than the infinitely precise result.

        SMT-LIB: [RTN] roundTowardNegative
    *)
      | Rtp
          (** Round towards positive infinity (+oo).
        The result shall be the format’s floating-point number (possibly +oo)
        closest to and no less than the infinitely precise result.

        SMT-LIB: [RTP] roundTowardPositive
    *)
      | Rtz
          (** Round towards zero.
        The result shall be the format’s floating-point number closest to and no
        greater in magnitude than the infinitely precise result.

        SMT-LIB: [RTZ] roundTowardZero
    *)

    val to_string : t -> string
    (**
     [to_string t]
     get string representation of this rounding mode.

     @return String representation of this rounding mode.
  *)
  end

  module Kind : sig
    (** The term kind. *)
    type t =
      | Constant  (** First order constant. *)
      | Const_array  (** Constant array. *)
      | Value  (** Value. *)
      | Variable  (** Bound variable. *)
      | And  (** Boolean and.

               SMT-LIB: [and] *)
      | Distinct  (** Disequality.

                    SMT-LIB: [distinct] *)
      | Equal  (** Equality.

                 SMT-LIB: [=] *)
      | Iff  (** Boolean if and only if.

               SMT-LIB: [=] *)
      | Implies  (** Boolean implies.

                   SMT-LIB: [=>] *)
      | Not  (** Boolean not.

               SMT-LIB: [not] *)
      | Or  (** Boolean or.

              SMT-LIB: [or] *)
      | Xor  (** Boolean xor.

               SMT-LIB: [xor] *)
      | Ite  (** If-then-else.

               SMT-LIB: [ite] *)
      | Exists  (** Existential quantification.

          SMT-LIB: [exists] *)
      | Forall
          (** Universal quantification.

                  SMT-LIB: [forall] *)
      | Apply  (** Function application. *)
      | Lambda  (** Lambda. *)
      | Select  (** Array select.

                        SMT-LIB: [select] *)
      | Store  (** Array store.

                       SMT-LIB: [store] *)
      | Bv_add  (** Bit-vector addition.

                  SMT-LIB: [bvadd] *)
      | Bv_and  (** Bit-vector and.

                  SMT-LIB: [bvand] *)
      | Bv_ashr
          (** Bit-vector arithmetic right shift.

        SMT-LIB: [bvashr] *)
      | Bv_comp
          (** Bit-vector comparison.

                   SMT-LIB: [bvcomp] *)
      | Bv_concat
          (** Bit-vector concat.

                     SMT-LIB: [concat] *)
      | Bv_dec
          (** Bit-vector decrement.

                  Decrement by one. *)
      | Bv_inc
          (** Bit-vector increment.

                  Increment by one. *)
      | Bv_mul
          (** Bit-vector multiplication.

                  SMT-LIB: [bvmul] *)
      | Bv_nand  (** Bit-vector nand.

                   SMT-LIB: [bvnand] *)
      | Bv_neg
          (** Bit-vector negation (two's complement).

        SMT-LIB: [bvneg] *)
      | Bv_nor  (** Bit-vector nor.

                  SMT-LIB: [bvnor] *)
      | Bv_not
          (** Bit-vector not (one's complement).

          SMT-LIB: [bvnot] *)
      | Bv_or  (** Bit-vector or.

                 SMT-LIB: [bvor] *)
      | Bv_redand
          (** Bit-vector and reduction.

        Bit-wise {b and} reduction, all bits are {b and}'ed together into a single
        bit.
        This corresponds to bit-wise {b and} reduction as known from Verilog. *)
      | Bv_redor
          (** Bit-vector reduce or.

        Bit-wise {b or} reduction, all bits are {b or}'ed together into a single
        bit.
        This corresponds to bit-wise {b or} reduction as known from Verilog. *)
      | Bv_redxor
          (** Bit-vector reduce xor.

        Bit-wise {b xor} reduction, all bits are {b xor}'ed together into a
        single bit.
        This corresponds to bit-wise {b xor} reduction as known from Verilog. *)
      | Bv_rol
          (** Bit-vector rotate left (not indexed).

        This is a non-indexed variant of SMT-LIB [rotate_left]. *)
      | Bv_ror
          (** Bit-vector rotate right.

        This is a non-indexed variant of SMT-LIB [rotate_right]. *)
      | Bv_saddo
          (** Bit-vector signed addition overflow test.

        Single bit to indicate if signed addition produces an overflow. *)
      | Bv_sdivo
          (** Bit-vector signed division overflow test.

        Single bit to indicate if signed division produces an overflow. *)
      | Bv_sdiv
          (** Bit-vector signed division.

           SMT-LIB: [bvsdiv] *)
      | Bv_sge
          (** Bit-vector signed greater than or equal.

        SMT-LIB: [bvsge] *)
      | Bv_sgt
          (** Bit-vector signed greater than.

          SMT-LIB: [bvsgt] *)
      | Bv_shl
          (** Bit-vector logical left shift.

          SMT-LIB: [bvshl] *)
      | Bv_shr
          (** Bit-vector logical right shift.

          SMT-LIB: [bvshr] *)
      | Bv_sle
          (** Bit-vector signed less than or equal.

        SMT-LIB: [bvsle] *)
      | Bv_slt  (** Bit-vector signed less than.

          SMT-LIB: [bvslt] *)
      | Bv_smod  (** Bit-vector signed modulo.

           SMT-LIB: [bvsmod] *)
      | Bv_smulo
          (** Bit-vector signed multiplication overflow test.

        SMT-LIB: [bvsmod] *)
      | Bv_srem
          (** Bit-vector signed remainder.

           SMT-LIB: [bvsrem] *)
      | Bv_ssubo
          (** Bit-vector signed subtraction overflow test.

        Single bit to indicate if signed subtraction produces an overflow. *)
      | Bv_sub
          (** Bit-vector subtraction.

                  SMT-LIB: [bvsub] *)
      | Bv_uaddo
          (** Bit-vector unsigned addition overflow test.

        Single bit to indicate if unsigned addition produces an overflow. *)
      | Bv_udiv
          (** Bit-vector unsigned division.

           SMT-LIB: [bvudiv] *)
      | Bv_uge
          (** Bit-vector unsigned greater than or equal.

        SMT-LIB: [bvuge] *)
      | Bv_ugt
          (** Bit-vector unsigned greater than.

          SMT-LIB: [bvugt] *)
      | Bv_ule
          (** Bit-vector unsigned less than or equal.

        SMT-LIB: [bvule] *)
      | Bv_ult
          (** Bit-vector unsigned less than.

          SMT-LIB: [bvult] *)
      | Bv_umulo
          (** Bit-vector unsigned multiplication overflow test.

        Single bit to indicate if unsigned multiplication produces
        an overflow. *)
      | Bv_urem
          (** Bit-vector unsigned remainder.

           SMT-LIB: [bvurem] *)
      | Bv_usubo
          (** Bit-vector unsigned subtraction overflow test.

        Single bit to indicate if unsigned subtraction produces an overflow. *)
      | Bv_xnor  (** Bit-vector xnor.

                   SMT-LIB: [bvxnor] *)
      | Bv_xor  (** Bit-vector xor.

                  SMT-LIB: [bvxor] *)
      | Bv_extract
          (** Bit-vector extract.

              SMT-LIB: [extract] (indexed) *)
      | Bv_repeat
          (** Bit-vector repeat.

             SMT-LIB: [repeat] (indexed) *)
      | Bv_roli
          (** Bit-vector rotate left by integer.

        SMT-LIB: [rotate_left] (indexed) *)
      | Bv_rori
          (** Bit-vector rotate right by integer.

        SMT-LIB: [rotate_right] (indexed) *)
      | Bv_sign_extend
          (** Bit-vector sign extend.

        SMT-LIB: [sign_extend] (indexed) *)
      | Bv_zero_extend
          (** Bit-vector zero extend.

        SMT-LIB: [zero_extend] (indexed) *)
      | Fp_abs
          (** Floating-point absolute value.

          SMT-LIB: [fp.abs] *)
      | Fp_add
          (** Floating-point addition.

                  SMT-LIB: [fp.add] *)
      | Fp_div
          (** Floating-point division.

                  SMT-LIB: [fp.div] *)
      | Fp_equal
          (** Floating-point equality.

                    SMT-LIB: [fp.eq] *)
      | Fp_fma
          (** Floating-point fused multiplcation and addition.

        SMT-LIB: [fp.fma] *)
      | Fp_fp
          (** Floating-point IEEE 754 value.

                 SMT-LIB: [fp] *)
      | Fp_geq
          (** Floating-point greater than or equal.

        SMT-LIB: [fp.geq] *)
      | Fp_gt
          (** Floating-point greater than.

                 SMT-LIB: [fp.gt] *)
      | Fp_is_inf
          (** Floating-point is infinity tester.

        SMT-LIB: [fp.isInfinite] *)
      | Fp_is_nan
          (** Floating-point is Nan tester.

             SMT-LIB: [fp.isNaN] *)
      | Fp_is_neg
          (** Floating-point is negative tester.

        SMT-LIB: [fp.isNegative] *)
      | Fp_is_normal
          (** Floating-point is normal tester.

        SMT-LIB: [fp.isNormal] *)
      | Fp_is_pos
          (** Floating-point is positive tester.

        SMT-LIB: [fp.isPositive] *)
      | Fp_is_subnormal
          (** Floating-point is subnormal tester.

        SMT-LIB: [fp.isSubnormal] *)
      | Fp_is_zero
          (** Floating-point is zero tester.

        SMT-LIB: [fp.isZero] *)
      | Fp_leq
          (** Floating-point less than or equal.

          SMT-LIB: [fp.leq] *)
      | Fp_lt
          (** Floating-point less than.

                 SMT-LIB: [fp.lt] *)
      | Fp_max  (** Floating-point max.

                  SMT-LIB: [fp.max] *)
      | Fp_min  (** Floating-point min.

                  SMT-LIB: [fp.min] *)
      | Fp_mul
          (** Floating-point multiplcation.

          SMT-LIB: [fp.mul] *)
      | Fp_neg
          (** Floating-point negation.

                  SMT-LIB: [fp.neg] *)
      | Fp_rem
          (** Floating-point remainder.

                  SMT-LIB: [fp.rem] *)
      | Fp_rti
          (** Floating-point round to integral.

        SMT-LIB: [fp.roundToIntegral] *)
      | Fp_sqrt
          (** Floating-point round to square root.

        SMT-LIB: [fp.sqrt] *)
      | Fp_sub
          (** Floating-point round to subtraction.

        SMT-LIB: [fp.sqrt] *)
      | Fp_to_fp_from_bv
          (** Floating-point to_fp from IEEE 754 bit-vector.

        SMT-LIB: [to_fp] (indexed) *)
      | Fp_to_fp_from_fp
          (** Floating-point to_fp from floating-point.

        SMT-LIB: [to_fp] (indexed) *)
      | Fp_to_fp_from_sbv
          (** Floating-point to_fp from signed bit-vector value.

        SMT-LIB: [to_fp] (indexed) *)
      | Fp_to_fp_from_ubv
          (** Floating-point to_fp from unsigned bit-vector value.

        SMT-LIB: [to_fp_unsigned] (indexed) *)
      | Fp_to_sbv
          (** Floating-point to_sbv.

        SMT-LIB: [fp.to_sbv] (indexed) *)
      | Fp_to_ubv
          (** Floating-point to_ubv.

        SMT-LIB: [fp.to_ubv] (indexed) *)

    val to_string : t -> string
    (**
     [to_string t]
     get string representation of this kind.

     @return String representation of this kind.
  *)
  end

  module Term : sig
    (** {1:term Term} *)

    type t
    (** A Bitwuzla term. *)

    (** {2:sort_util Util} *)

    val hash : t -> int
    (**
     [hash t]
     compute the hash value for a term.

     @param t The term.

     @return The hash value of the term.
  *)

    val equal : t -> t -> bool
    (**
     [equal a b]
     Syntactical equality operator.

     @param a The first term.
     @param b The second term.
     @return True if the given terms are equal.
  *)

    val compare : t -> t -> int
    (**
     [compare a b]
     Syntactical comparison operator.

     @param a The first term.
     @param b The second term.
     @return Zero if the given term are equal,
             a positive number if [a] > [b],
             a negative number otherwise.
  *)

    val pp : Format.formatter -> t -> unit
    (**
     [pp formatter t]
     print term.

     (alias for {!val:pp_smt2}[ 2])

     @param formatter The outpout formatter.
     @param t The term.
  *)

    val pp_smt2 : bv_format:int -> Format.formatter -> t -> unit
    (**
     [pp_smt2 base formatter t]
     print term in SMTlib format.

     @param bv_format The bit-vector number format:
                      [2] for binary, [10] for decimal and [16] for hexadecimal.
     @param formatter The output formatter.
     @param t The term.
  *)

    val to_string : ?bv_format:int -> t -> string
    (**
     [to_string t ~bv_format]
     get string representation of this term.

     @param t The term.
     @param bv_format The bit-vector number format:
                      [2] for binary \[{b default}\],
                      [10] for decimal and [16] for hexadecimal.

     @return String representation of this term.
  *)

    (** {2:term_query Query} *)

    val id : t -> int64
    (**
     [id t]
     get the id of this term.

     @param t The term.
     @return The id value of the term.
  *)

    val kind : t -> Kind.t
    (**
     [kind t]
     get the kind of a term.

     @param t The term.

     @return The kind of the given term.
  *)

    val sort : t -> Sort.t
    (**
     [sort t]
     get the sort of a term.

     @param t The term.

     @return The sort of the term.
  *)

    val num_children : t -> int
    (**
     [num_children t]
     get the number of child terms of a term.

     @param t The term.

     @return The  number children of [t].
  *)

    val children : t -> t array
    (**
     [children t]
     get the child terms of a term.

     @param t The term.

     @return The children of [t] as an array of terms.
  *)

    val get : t -> int -> t
    (**
     [get t i]
     return child at position [i].

     Only valid to call if [num_children t > 0].

     @param i The position of the child.
     @return The child node at position [i].
  *)

    val num_indices : t -> int
    (**
     [num_indices t]
     get the number of indices of an indexed term.

     Requires that given term is an indexed term.

     @param t The term.

     @return The number of indices of [t].
  *)

    val indices : t -> int array
    (**
     [indices t]
     get the indices of an indexed term.

     Requires that given term is an indexed term.

     @param t The term.

     @return The children of [t] as an array of terms.
  *)

    val symbol : t -> string
    (**
     [symbol t]
     get the symbol of a term.

     @param t The term.

     @return The symbol of [t].

     @raise Not_found if no symbol is defined.
  *)

    val is_const : t -> bool
    (**
     [is_const t]
     determine if a term is a constant.

     @param t The term.

     @return [true] if [t] is a constant.
  *)

    val is_variable : t -> bool
    (**
     [is_variable t]
     determine if a term is a variable.

     @param t The term.

     @return [true] if [t] is a variable.
  *)

    val is_value : t -> bool
    (**
     [is_value t]
     determine if a term is a value.

     @param t The term.

     @return [true] if [t] is a value.
  *)

    val is_bv_value_zero : t -> bool
    (**
     [is_bv_value_zero t]
     determine if a term is a bit-vector value representing zero.

     @param t The term.

     @return [true] if [t] is a bit-vector zero value.
  *)

    val is_bv_value_one : t -> bool
    (**
     [is_bv_value_one t]
     determine if a term is a bit-vector value representing one.

     @param t The term.

     @return [true] if [t] is a bit-vector one value.
  *)

    val is_bv_value_ones : t -> bool
    (**
     [is_bv_value_ones t]
     determine if a term is a bit-vector value with all bits set to one.

     @param t The term.

     @return [true] if [t] is a bit-vector value with all bits set to one.
  *)

    val is_bv_value_min_signed : t -> bool
    (**
     [is_bv_value_min_signed t]
     determine if a term is a bit-vector minimum signed value.

     @param t The term.

     @return [true] if [t] is a bit-vector value with the most significant bit
         set to 1 and all other bits set to 0.
  *)

    val is_bv_value_max_signed : t -> bool
    (**
     [is_bv_value_max_signed t]
     determine if a term is a bit-vector maximum signed value.

     @param t The term.

     @return [true] if [t] is a bit-vector value with the most significant bit
         set to 0 and all other bits set to 1.
  *)

    val is_fp_value_pos_zero : t -> bool
    (**
     [is_fp_value_pos_zero t]
     determine if a term is a floating-point positive zero (+zero) value.

     @param t The term.

     @return [true] if [t] is a floating-point +zero value.
  *)

    val is_fp_value_neg_zero : t -> bool
    (**
     [is_fp_value_neg_zero t]
     determine if a term is a floating-point value negative zero (-zero).

     @param t The term.

     @return [true] if [t] is a floating-point value negative zero.
  *)

    val is_fp_value_pos_inf : t -> bool
    (**
     [is_fp_value_pos_inf t]
     determine if a term is a floating-point positive infinity (+oo) value.

     @param t The term.

     @return [true] if [t] is a floating-point +oo value.
  *)

    val is_fp_value_neg_inf : t -> bool
    (**
     [is_fp_value_neg_inf t]
     determine if a term is a floating-point negative infinity (-oo) value.

     @param t The term.

     @return [true] if [t] is a floating-point -oo value.
  *)

    val is_fp_value_nan : t -> bool
    (**
     [is_fp_value_nan t]
     determine if a term is a floating-point NaN value.

     @param t The term.

     @return [true] if [t] is a floating-point NaN value.
  *)

    val is_rm_value_rna : t -> bool
    (**
     [is_rm_value_rna t]
     determine if a term is a rounding mode RNA value.

     @param t The term.

     @return [true] if [t] is a rounding mode RNA value.
  *)

    val is_rm_value_rne : t -> bool
    (**
     [is_rm_value_rna t]
     determine if a term is a rounding mode RNE value.

     @param t The term.

     @return [true] if [t] is a rounding mode RNE value.
  *)

    val is_rm_value_rtn : t -> bool
    (**
     [is_rm_value_rna t]
     determine if a term is a rounding mode RTN value.

     @param t The term.

     @return [true] if [t] is a rounding mode RTN value.
  *)

    val is_rm_value_rtp : t -> bool
    (**
     [is_rm_value_rna t]
     determine if a term is a rounding mode RTP value.

     @param t The term.

     @return [true] if [t] is a rounding mode RTP value.
  *)

    val is_rm_value_rtz : t -> bool
    (**
     [is_rm_value_rna t]
     determine if a term is a rounding mode RTZ value.

     @param t The term.

     @return [true] if [t] is a rounding mode RTZ value.
  *)

    type _ cast =
      | Bool : bool cast  (** for Boolean values *)
      | RoundingMode : RoundingMode.t cast  (** for rounding mode values *)
      | String : { base : int } -> string cast
          (** for any value
        (Boolean, RoundingMode, bit-vector and floating-point) *)
      | IEEE_754 : (string * string * string) cast
          (** for floating-point values as strings
        for sign bit, exponent and significand *)
      | Z : Z.t cast  (** for bit-vector *)

    val value : 'a cast -> t -> 'a
    (**
     [value kind t]
     get value from value term.

     @param kind The type of the value representation.
     @return The value of [t] in a given representation.
  *)
  end

  module Result : sig
    (** A satisfiability result. *)
    type t = Sat  (** sat *) | Unsat  (** unsat *) | Unknown  (** unknown *)

    val to_string : t -> string
    (**
       [to_string t]
       get string representation of this result.

       @return String representation of this result.
  *)
  end

  module Solver : sig
    (** {1 Solver} *)

    type t
    (** The Bitwuzla solver. *)

    val configure_terminator : t -> (unit -> bool) option -> unit
    (**
     [configure_terminator t f]
     configure a termination callback function.

     If terminator has been connected, Bitwuzla calls this function periodically
     to determine if the connected instance should be terminated.

     @param t The Bitwuzla instance.
     @param f The callback function, returns [true] if [t] should be terminated.
  *)

    val create : Options.t -> t
    (**
     [create options]
     create a new Bitwuzla instance.

     The returned instance can be deleted earlier via {!val:unsafe_delete}.

     @param options The associated options instance.
                  Options must be configured at this point.

     @return The created Bitwuzla instance.
  *)

    (** {2 Formula} *)

    val push : t -> int -> unit
    (**
     [push t nlevels]
     push context levels.

     @param t The Bitwuzla instance.
     @param nlevels The number of context levels to push.
  *)

    val pop : t -> int -> unit
    (**
     [pop t nlevels]
     pop context levels.

     @param t The Bitwuzla instance.
     @param nlevels The number of context levels to pop.
  *)

    val assert_formula : t -> Term.t -> unit
    (**
     [mk_assert t term]
     assert formula.

     @param t The Bitwuzla instance.
     @param term The formula to assert.
  *)

    val get_assertions : t -> Term.t array
    (**
     [get_assertions t]
     get the set of currently asserted formulas.

     @return The assertion formulas.
  *)

    val pp_formula : Format.formatter -> t -> unit
    (**
     [pp_formula formatter t]
     print the current input formula.

     @param formatter The output formatter.
     @param t The Bitwuzla instance.
  *)

    (** {2 Check} *)

    val simplify : t -> unit
    (**
     [simplify t]
     simplify the current input formula.

     @param t The Bitwuzla instance.
  *)

    val check_sat : ?assumptions:Term.t array -> t -> Result.t
    (**
     [check_sat ~assumptions t]
     check satisfiability of current input formula.

     An input formula consists of assertions added via {!val:assert_formula}.
     The search for a solution can by guided by making assumptions via
     [assumptions].

     Assertions and assumptions are combined via Boolean [and].

     @param t The Bitwuzla instance.

     @return {!constructor:Sat} if the input formula is satisfiable and
         {!constructor:Unsat} if it is unsatisfiable, and {!constructor:Unknown}
         when neither satisfiability nor unsatisfiability was determined.
         This can happen when [t] was terminated via a termination callback.
  *)

    (** {2 Sat} *)

    val get_value : t -> Term.t -> Term.t
    (**
     [get_value t term]
     get a term representing the model value of a given term.

     Requires that the last {!val:check_sat} query returned [Sat].

     @param t The Bitwuzla instance.
     @param term The term to query a model value for.

     @return A term representing the model value of term [term].
  *)

    (** {2 Unsat} *)

    val is_unsat_assumption : t -> Term.t -> bool
    (**
     [is_unsat_assumption t term]
     determine if an assumption is an unsat assumption.

     Unsat assumptions are assumptions that force an input formula to become
     unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
     failed assumptions in MiniSAT.

     Requires that unsat assumption generation has been enabled via
     {!val:Options.set}.

     Requires that the last {!val:check_sat} query returned [Unsat].

     @param t The Bitwuzla instance.
     @param term The assumption to check for.

     @return [true] if given assumption is an unsat assumption.
  *)

    val get_unsat_assumptions : t -> Term.t array
    (**
     [get_unsat_assumptions t]
     get the set of unsat assumptions.

     Unsat assumptions are assumptions that force an input formula to become
     unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
     failed assumptions in MiniSAT.

     Requires that unsat assumption generation has been enabled via
     {!val:Options.set}.

     Requires that the last {!val:check_sat} query returned [Unsat].

     @param t The Bitwuzla instance.

     @return An array with unsat assumptions.
  *)

    val get_unsat_core : t -> Term.t array
    (**
     [get_unsat_core t]
     get the set unsat core (unsat assertions).

     The unsat core consists of the set of assertions that force
     an input formula to become unsatisfiable.

     Requires that unsat core generation has been enabled via {!val:Options.set}.

     Requires that the last {!val:check_sat} query returned [Unsat].

     @param t The Bitwuzla instance.

     @return An array with unsat assertions.
  *)

    (** {2 Expert} *)
    val unsafe_delete : t -> unit
    (**
     [delete t]
     delete a Bitwuzla instance.

     UNSAFE: call this ONLY to release the resources earlier
     if the instance is about to be garbage collected.

     @param t The Bitwuzla instance to delete.
  *)

    val pp_statistics : Format.formatter -> t -> unit
  end

  (** {2:sort_constructor Sort constructor} *)

  val mk_array_sort : Sort.t -> Sort.t -> Sort.t
  (**
   [mk_array_sort index element]
   create an array sort.

   @param index The index sort of the array sort.
   @param element The element sort of the array sort.

   @return An array sort which maps sort [index] to sort [element].
*)

  val mk_bool_sort : unit -> Sort.t
  (**
   [mk_bool_sort ()]
   create a Boolean sort.

   A Boolean sort is a bit-vector sort of size 1.

   @return A Boolean sort.
*)

  val mk_bv_sort : int -> Sort.t
  (**
   [mk_bv_sort size]
   create a bit-vector sort of given size.

   @param size The size of the bit-vector sort.

   @return A bit-vector sort of given size.
*)

  val mk_fp_sort : int -> int -> Sort.t
  (**
   [mk_fp_sort exp_size sig_size]
   create a floating-point sort of given exponent and significand size.

   @param exp_size The size of the exponent.
   @param sig_size The size of the significand (including sign bit).

   @return A floating-point sort of given format.
*)

  val mk_fun_sort : Sort.t array -> Sort.t -> Sort.t
  (**
   [mk_fun_sort domain codomain]
   create a function sort.

   @param domain The domain sorts (the sorts of the arguments).
   @param codomain The codomain sort (the sort of the return value).

   @return A function sort of given domain and codomain sorts.
*)

  val mk_rm_sort : unit -> Sort.t
  (**
   [mk_rm_sort ()]
   create a Roundingmode sort.

   @return A Roundingmode sort.
*)

  val mk_uninterpreted_sort : ?symbol:string -> unit -> Sort.t
  (**
   [mk_uninterpreted_sort name]
   create an uninterpreted sort.

   Only 0-arity uninterpreted sorts are supported.

   @param symbol The symbol of the sort.
   @return An uninterpreted sort.
*)

  (** {2:term_constructor Term constructor} *)

  (** {3 Value} *)

  val mk_true : unit -> Term.t
  (**
   [mk_true ()]
   create a true value.

   This creates a bit-vector value 1 of size 1.

   @return A term representing the bit-vector value 1 of size 1.
*)

  val mk_false : unit -> Term.t
  (**
   [mk_false ()]
   create a false value.

   This creates a bit-vector value 0 of size 1.

   @return A term representing the bit-vector value 0 of size 1.
*)

  val mk_bv_zero : Sort.t -> Term.t
  (**
   [mk_bv_zero sort]
   create a bit-vector value zero.

   @param sort The sort of the value.

   @return A term representing the bit-vector value 0 of given sort.
*)

  val mk_bv_one : Sort.t -> Term.t
  (**
   [mk_bv_one sort]
   create a bit-vector value one.

   @param sort The sort of the value.

   @return A term representing the bit-vector value 1 of given sort.
*)

  val mk_bv_ones : Sort.t -> Term.t
  (**
   [mk_bv_ones sort]
   create a bit-vector value where all bits are set to 1.

   @param sort The sort of the value.

   @return A term representing the bit-vector value of given sort
         where all bits are set to 1.
*)

  val mk_bv_min_signed : Sort.t -> Term.t
  (**
   [mk_bv_min_signed sort]
   create a bit-vector minimum signed value.

   @param sort The sort of the value.

   @return A term representing the bit-vector value of given sort where the MSB
         is set to 1 and all remaining bits are set to 0.
*)

  val mk_bv_max_signed : Sort.t -> Term.t
  (**
   [mk_bv_max_signed sort]
   create a bit-vector maximum signed value.

   @param sort The sort of the value.

   @return A term representing the bit-vector value of given sort where the MSB
         is set to 0 and all remaining bits are set to 1.
*)

  val mk_bv_value : Sort.t -> string -> int -> Term.t
  (**
   [mk_bv_value sort value base]
   create a bit-vector value from its string representation.

   Parameter [base] determines the base of the string representation.

   Given value must fit into a bit-vector of given size (sort).

   @param sort The sort of the value.
   @param value A string representing the value.
   @param base The base in which the string is given.

   @return A term representing the bit-vector value of given sort.
*)

  val mk_bv_value_int : Sort.t -> int -> Term.t
  (**
   [mk_bv_value_int sort value]
   create a bit-vector value from its unsigned integer representation.

   If given value does not fit into a bit-vector of given size (sort),
       the value is truncated to fit.

   @param sort The sort of the value.
   @param value The unsigned integer representation of the bit-vector value.

   @return A term representing the bit-vector value of given sort.
*)

  val mk_bv_value_int64 : Sort.t -> int64 -> Term.t
  (**
   [mk_bv_value_int64 sort value]
   create a bit-vector value from its unsigned integer representation.

   If given value does not fit into a bit-vector of given size (sort),
       the value is truncated to fit.

   @param sort The sort of the value.
   @param value The unsigned integer representation of the bit-vector value.

   @return A term representing the bit-vector value of given sort.
*)

  val mk_fp_pos_zero : Sort.t -> Term.t
  (**
   [mk_fp_pos_zero sort]
   create a floating-point positive zero value (SMT-LIB: [+zero]).

   @param sort The sort of the value.

   @return A term representing the floating-point positive zero value of given
         floating-point sort.
*)

  val mk_fp_neg_zero : Sort.t -> Term.t
  (**
   [mk_fp_neg_zero sort]
   create a floating-point negative zero value (SMT-LIB: [-zero]).

   @param sort The sort of the value.

   @return A term representing the floating-point negative zero value of given
         floating-point sort.
*)

  val mk_fp_pos_inf : Sort.t -> Term.t
  (**
   [mk_fp_pos_inf sort]
   create a floating-point positive infinity value (SMT-LIB: [+oo]).

   @param sort The sort of the value.

   @return A term representing the floating-point positive infinity value of
         given floating-point sort.
*)

  val mk_fp_neg_inf : Sort.t -> Term.t
  (**
   [mk_fp_neg_inf sort]
   create a floating-point negative infinity value (SMT-LIB: [-oo]).

   @param sort The sort of the value.

   @return A term representing the floating-point negative infinity value of
         given floating-point sort.
*)

  val mk_fp_nan : Sort.t -> Term.t
  (**
   [mk_fp_nan sort]
   create a floating-point NaN value.

   @param sort The sort of the value.

   @return A term representing the floating-point NaN value of given
         floating-point sort.
*)

  val mk_fp_value : Term.t -> Term.t -> Term.t -> Term.t
  (**
   [mk_fp_value bv_sign bv_exponent bv_significand]
   create a floating-point value from its IEEE 754 standard representation
   given as three bitvectors representing the sign bit, the exponent and the
   significand.

   @param bv_sign The sign bit.
   @param bv_exponent The exponent bit-vector.
   @param bv_significand The significand bit-vector.

   @return A term representing the floating-point value.
*)

  val mk_fp_value_from_real : Sort.t -> Term.t -> string -> Term.t
  (**
   [mk_fp_value_from_real t sort rm real]
   create a floating-point value from its real representation, given as a
   decimal string, with respect to given rounding mode.

   @param sort The sort of the value.
   @param rm The rounding mode.
   @param real The decimal string representing a real value.

   @return A term representing the floating-point value of given sort.
*)

  val mk_fp_value_from_rational : Sort.t -> Term.t -> string -> string -> Term.t
  (**
   [mk_fp_value_from_rational sort rm num den]
   create a floating-point value from its rational representation, given as a
   two decimal strings representing the numerator and denominator, with respect
   to given rounding mode.

   @param sort The sort of the value.
   @param rm The rounding mode.
   @param num The decimal string representing the numerator.
   @param den The decimal string representing the denominator.

   @return A term representing the floating-point value of given sort.
*)

  val mk_rm_value : RoundingMode.t -> Term.t
  (**
   [mk_rm_value rm]
   create a rounding mode value.

   @param rm The rounding mode value.

   @return A term representing the rounding mode value.
*)

  (** {3 Expression} *)

  val mk_term1 : Kind.t -> Term.t -> Term.t
  (**
   [mk_term1 kind arg]
   create a term of given kind with one argument term.

   @param kind The operator kind.
   @param arg The argument to the operator.

   @return A term representing an operation of given kind.
*)

  val mk_term2 : Kind.t -> Term.t -> Term.t -> Term.t
  (**
   [mk_term2 kind arg0 arg1]
   create a term of given kind with two argument terms.

   @param kind The operator kind.
   @param arg0 The first argument to the operator.
   @param arg1 The second argument to the operator.

   @return A term representing an operation of given kind.
*)

  val mk_term3 : Kind.t -> Term.t -> Term.t -> Term.t -> Term.t
  (**
   [mk_term3 kind arg0 arg1 arg2]
   create a term of given kind with three argument terms.

   @param kind The operator kind.
   @param arg0 The first argument to the operator.
   @param arg1 The second argument to the operator.
   @param arg2 The third argument to the operator.

   @return A term representing an operation of given kind.
*)

  val mk_term1_indexed1 : Kind.t -> Term.t -> int -> Term.t
  (**
   [mk_term1_indexed1 kind arg idx]
   create an indexed term of given kind with one argument term and one index.

   @param kind The operator kind.
   @param arg The argument term.
   @param idx The index.

   @return A term representing an indexed operation of given kind.
*)

  val mk_term1_indexed2 : Kind.t -> Term.t -> int -> int -> Term.t
  (**
   [mk_term1_indexed2 kind arg idx0 idx1]
   create an indexed term of given kind with one argument term and two indices.

   @param kind The operator kind.
   @param arg The argument term.
   @param idx0 The first index.
   @param idx1 The second index.

   @return A term representing an indexed operation of given kind.
*)

  val mk_term2_indexed1 : Kind.t -> Term.t -> Term.t -> int -> Term.t
  (**
   [mk_term2_indexed1 t kind arg0 arg1 idx]
   create an indexed term of given kind with two argument terms and one index.

   @param kind The operator kind.
   @param arg0 The first argument term.
   @param arg1 The second argument term.
   @param idx The index.

   @return A term representing an indexed operation of given kind.
*)

  val mk_term2_indexed2 : Kind.t -> Term.t -> Term.t -> int -> int -> Term.t
  (**
   [mk_term2_indexed2 t kind arg0 arg1 idx0 idx1]
   create an indexed term of given kind with two argument terms and two indices.

   @param kind The operator kind.
   @param arg0 The first argument term.
   @param arg1 The second argument term.
   @param idx0 The first index.
   @param idx1 The second index.

   @return A term representing an indexed operation of given kind.
*)

  val mk_term : Kind.t -> ?indices:int array -> Term.t array -> Term.t
  (**
   [mk_term kind args ~indices]
   create an indexed term of given kind with the given argument terms and
   indices.

   @param kind The operator kind.
   @param args The argument terms.
   @param indices The indices.

   @return A term representing an indexed operation of given kind.
*)

  val mk_const : ?symbol:string -> Sort.t -> Term.t
  (**
   [mk_const sort ~symbol]
   create a (first-order) constant of given sort with given symbol.

   This creates a 0-arity function symbol.

   @param sort The sort of the constant.
   @param symbol The symbol of the constant.

   @return A term representing the constant.
*)

  val mk_const_array : Sort.t -> Term.t -> Term.t
  (**
   [mk_const_array sort value]
   create a one-dimensional constant array of given sort, initialized with
   given value.

   @param sort The sort of the array.
   @param value The value to initialize the elements of the array with.

   @return A term representing a constant array of given sort.
*)

  val mk_var : ?symbol:string -> Sort.t -> Term.t
  (**
   [mk_var sort ~symbol]
   create a variable of given sort with given symbol.

   This creates a variable to be bound by quantifiers or lambdas.

   @param sort The sort of the variable.
   @param symbol The symbol of the variable.

   @return A term representing the variable.
*)

  (** {2 Util} *)

  val substitute_term : Term.t -> (Term.t * Term.t) array -> Term.t
  (**
   [substitute t term map]
   substitute a set of keys with their corresponding values in the given term.

   @param term The term in which the keys are to be substituted.
   @param map The key/value associations.

   @return The resulting term from this substitution.
*)

  val substitute_terms : Term.t array -> (Term.t * Term.t) array -> unit
  (**
   [substitute_terms t terms map]
   substitute a set of keys with their corresponding values in the set of given
   terms.

   The terms in [terms] are replaced with the terms resulting from this
   substitutions.

   @param terms The terms in which the keys are to be substituted.
   @param map The key/value associations.
*)
end

module Make () : S
(**
   Create a new independent Bitwuzla instance that can run in parallel
   to all other ones.
 *)

include S
