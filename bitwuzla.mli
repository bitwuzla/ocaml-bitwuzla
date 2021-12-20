(** Bitwuzla is an SMT solver for QF_AUFBVFP problems. *)

(** Create a new Bitwuzla session
    ({!val:check_sat} can only be called once). *)
module Once () : sig
  (** {1 Phantom type} *)

  (** Phantom types are annotations that allow the compiler to statically
      catch some sort mismatch errors. Size mismatch errors will still be
      caught at runtime. *)

  type bv = [ `Bv ]
  (** The bit-vector kind. *)

  type rm = [ `Rm ]
  (** The rounding-mode kind. *)

  type fp = [ `Fp ]
  (** The floating-point kind. *)

  (** The array kind with ['a] index and ['b] element. *)
  type ('a, 'b) ar = [ `Ar of 'a -> 'b ]
    constraint 'a = [< bv | rm | fp ] constraint 'b = [< bv | rm | fp ]
  (** Both index and element should be of bit-vector, rounding-mode
      or floating-point kind *)

  (** The function kind taking ['a] argument and
      returning {!type:'b} element. *)
  type ('a, 'b) fn = [ `Fn of 'a -> 'b ] constraint 'b = [< bv ]
  (** Functions accept only bit-vector, rounding-mode or floating-point as
      argument and return only bit-vector. *)

  (** {1 Core types } *)

  type 'a sort
  (** A sort of ['a] kind. *)

  type 'a term
  (** A term of ['a] kind. *)

  (** A value of ['a] kind. *)
  type 'a value = private 'a term
  (** Values are subtype of terms and can be downcasted using [:>] operator. *)

  module Sort : sig
    type 'a t = 'a sort
    (** A sort of ['a] kind. *)

    val bool : bv t
    (** A Boolean sort is a bit-vector sort of size 1. *)

    val bv : int -> bv t
    (**
       [bv size]
       create a bit-vector sort of given size.

       @param size The size of the bit-vector sort.

       @return A bit-vector sort of given size.
    *)

    val size : bv t -> int
    (**
       [size sort]
       get the size of a bit-vector sort.

       @param sort The sort.

       @return The size of the bit-vector sort.
    *)

    val fp : exponent:int -> int -> fp t
    (**
       [fp exp_size size]
       create a floating-point sort of given size with [exp_size] exponent bits.

       @param exp_size The size of the exponent.
       @param size The total size of the floating-point.

       @return A floating-point sort of given format.
    *)

    val exponent : fp t -> int
    (**
       [exponent sort]
       get the exponent size of a floating-point sort.

       @param sort The sort.

       @return The exponent size of the floating-point sort.
    *)

    val significand : fp t -> int
    (**
       [significand sort]
       get the significand size of a floating-point sort.

       @param sort The sort.

       @return The significand size of the floating-point sort.
    *)

    val rm : rm t
    (** A Roundingmode sort. *)

    val ar : 'a t -> 'b t -> ('a, 'b) ar t
    (**
       [ar index element]
       create an array sort.

       @param index The index sort of the array sort.
       @param element The element sort of the array sort.

       @return An array sort which maps sort [index] to sort [element].
    *)

    val index : ('a, 'b) ar t -> 'a t
    (**
       [index sort]
       get the index sort of an array sort.

       @param sort The sort.

       @return The index sort of the array sort.
    *)

    val element : ('a, 'b) ar t -> 'b t
    (**
       [element sort]
       get the element sort of an array sort.

       @param sort The sort.

       @return The element sort of the array sort.
    *)

    (** Statically typed list of function argument sorts. *)
    type 'a variadic =
      | [] : unit variadic
      | ( :: ) :
          ([< bv | rm | fp ] as 'a) sort * 'b variadic
          -> ('a -> 'b) variadic
          (** Functions accept only bit-vector, rounding-mode or floating-point
          as argument *)

    val fn : 'a variadic -> 'b t -> ('a, 'b) fn t
    (**
       [fn domain codomain]
       create a function sort.

       @param domain The domain sorts (the sorts of the arguments).
       @param codomain The codomain sort (the sort of the return value).

       @return A function sort of given domain and codomain sorts.
    *)

    val arity : ('a, 'b) fn t -> int
    (**
       [arity sort]
       get the arity of a function sort.

       @param sort The sort.

       @return The number of arguments of the function sort.
    *)

    val domain : ('a, 'b) fn t -> 'a variadic
    (**
       [domain sort]
       get the domain sorts of a function sort.

       @param sort The sort.

       @return The domain sorts of the function sort as an array of sort.
    *)

    val codomain : ('a, 'b) fn t -> 'b t
    (**
       [codomain sort]
       get the codomain sort of a function sort.

       @param sort The sort.

       @return The codomain sort of the function sort.
    *)

    val hash : 'a t -> int
    (**
       [hash sort]
       compute the hash value for a sort.

       @param sort The sort.

       @return The hash value of the sort.
    *)

    val equal : 'a t -> 'a t -> bool
    (**
       [equal sort0 sort1]
       determine if two sorts are equal.

       @param sort0 The first sort.
       @param sort1 The second sort.

       @return [true] if the given sorts are equal.
    *)

    val pp : Format.formatter -> 'a t -> unit
    (**
       [pp formatter sort]
       pretty print sort.

       @param formatter The outpout formatter
       @param sort The sort.
    *)
  end

  module Term : sig
    type 'a t = 'a term constraint 'a = [< bv | rm | fp | ('b, 'c) ar ]
    (** A term of ['a] kind. *)

    (** Statically typed list of function argument terms. *)
    type 'a variadic =
      | [] : unit variadic
      | ( :: ) :
          ([< bv | rm | fp ] as 'a) term * 'b variadic
          -> ('a -> 'b) variadic
          (** Functions accept only bit-vector, rounding-mode or floating-point
          as argument *)

    (** {1 Constructor} *)

    (** Boolean *)
    module Bl : sig
      (** Operation over bit-vectors of size 1. *)

      type t = bv term
      (** A boolean term. *)

      val false' : t
      (** A bit-vector value 0 of size 1. *)

      val true' : t
      (** A bit-vector value 1 of size 1. *)

      val of_bool : bool -> t
      (**
         [of_bool b]
         create a bit-vector value of size 1 from a [bool].

         @param b The boolean value.

         @return Either {!val:true'} or {!val:false'}.
      *)

      val of_bv : bv term -> t
      (**
         [of_bv t]
         create a bit-wise {b or} reduction of all bits.

         @param t The bit-vector term.

         @return A term equal to [t <> 0].
      *)

      val logand : t -> t -> t
      (**
         [logand t0 t1]
         create a boolean {b and}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [and]
      *)

      val lognand : t -> t -> t
      (**
         [lognand t0 t1]
         create a boolean {b nand}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [bvnand]
      *)

      val redand : t array -> t
      (**
         [redand ts]
         create a {i n}ary boolean {b and}.

         @param ts The boolean terms.

         @return SMT-LIB: [and]
      *)

      val logor : t -> t -> t
      (**
         [logor t0 t1]
         create a boolean {b or}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [or]
      *)

      val lognor : t -> t -> t
      (**
         [lognor t0 t1]
         create a boolean {b nor}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [bvnor]
      *)

      val redor : t array -> t
      (**
         [redor ts]
         create a {i n}ary boolean {b or}.

         @param ts The boolean terms.

         @return SMT-LIB: [or]
      *)

      val logxor : t -> t -> t
      (**
         [logxor t0 t1]
         create a boolean {b xor}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [xor]
      *)

      val logxnor : t -> t -> t
      (**
         [logxnor t0 t1]
         create a boolean {b xnor}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [bvxnor]
      *)

      val redxor : t array -> t
      (**
         [redxor ts]
         create a {i n}ary boolean {b xor}.

         @param ts The boolean terms.

         @return SMT-LIB: [xor]
      *)

      val lognot : t -> t
      (**
         [lognot t]
         create a boolean {b not}.

         @param t The boolean term.

         @return SMT-LIB: [not]
      *)

      val iff : t -> t -> t
      (**
         [iff t0 t1]
         create a boolean {b if and only if}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [=]
      *)

      val implies : t -> t -> t
      (**
         [implies t0 t1]
         create a boolean {b implies}.

         @param t0 The first boolean term.
         @param t1 The second boolean term.

         @return SMT-LIB: [=>]
      *)

      val assignment : bv value -> bool
      (**
         [assignment t]
         get boolean representation of the current model value of given
         boolean term.

         @param t The term to query a model value for.

         @return boolean representation of current model value of term [t].
      *)
    end

    (** Bit-vector *)
    module Bv : sig
      type t = bv term
      (** A bit-vector term. *)

      val zero : bv sort -> t
      (**
         [zero sort]
         create a bit-vector value zero.

         @param sort The sort of the value.

         @return A term representing the bit-vector value 0 of given sort.
      *)

      val one : bv sort -> t
      (**
         [one sort]
         create a bit-vector value one.

         @param sort The sort of the value.

         @return A term representing the bit-vector value 1 of given sort.
      *)

      val ones : bv sort -> t
      (**
         [ones sort]
         create a bit-vector value where all bits are set to 1.

         @param sort The sort of the value.

         @return A term representing the bit-vector value of given sort
         where all bits are set to 1.
      *)

      val min_signed : bv sort -> t
      (**
         [min_signed sort]
         create a bit-vector minimum signed value.

         @param sort The sort of the value.

         @return A term representing the bit-vector value of given sort
         where the MSB is set to 1 and all remaining bits are set to 0.
      *)

      val max_signed : bv sort -> t
      (**
         [max_signed sort]
         create a bit-vector maximum signed value.

         @param sort The sort of the value.

         @return A term representing the bit-vector value of given sort
         where the MSB is set to 0 and all remaining bits are set to 1.
      *)

      val of_int : bv sort -> int -> t
      (**
         [of_int sort value]
         create a bit-vector value from its unsigned integer representation.

         If given value does not fit into a bit-vector of given size (sort),
         the value is truncated to fit.

         @param sort The sort of the value.
         @param value The unsigned integer representation of
         the bit-vector value.

         @return A term representing the bit-vector value of given sort.
      *)

      val of_z : bv sort -> Z.t -> t
      (**
         [of_z sort value]
         create a bit-vector value from its unsigned integer representation.

         If given value does not fit into a bit-vector of given size (sort),
         the value is truncated to fit.

         @param sort The sort of the value.
         @param value The unsigned integer representation of
         the bit-vector value.

         @return A term representing the bit-vector value of given sort.
      *)

      val of_string : bv sort -> string -> t
      (**
         [of_string sort value]
         create a bit-vector value from its string representation.

         Prefix determine the base of the string representation:
         - [0b]   for binary;
         - [0x]   for hexadecimal;
         - others for decimal.

         Given value must fit into a bit-vector of given size (sort).

         @param sort The sort of the value.
         @param value A string representing the value.

         @return A term representing the bit-vector value of given sort.
      *)

      (** The term operator. *)
      type ('a, 'b) operator =
        | Add : (t -> t -> t, t * t) operator
            (** Bit-vector addition.

            SMT-LIB: [bvadd] *)
        | And : (t -> t -> t, t * t) operator
            (** Bit-vector and.

            SMT-LIB: [bvand] *)
        | Ashr : (t -> t -> t, t * t) operator
            (** Bit-vector arithmetic right shift.

            SMT-LIB: [bvashr] *)
        | Concat : (t -> t -> t, t * t) operator
            (** Bit-vector concat.

            SMT-LIB: [concat] *)
        | Extract : (hi:int -> lo:int -> t -> t, int * int * t) operator
            (** Bit-vector extract.

            SMT-LIB: [extract] (indexed) *)
        | Mul : (t -> t -> t, t * t) operator
            (** Bit-vector multiplication.

            SMT-LIB: [bvmul] *)
        | Neg : (t -> t, t) operator
            (** Bit-vector negation (two's complement).

            SMT-LIB: [bvneg] *)
        | Not : (t -> t, t) operator
            (** Bit-vector not (one's complement).

            SMT-LIB: [bvnot] *)
        | Or : (t -> t -> t, t * t) operator
            (** Bit-vector or.

            SMT-LIB: [bvor] *)
        | Rol : (t -> t -> t, t * t) operator
            (** Bit-vector rotate left (not indexed).

            This is a non-indexed variant of SMT-LIB [rotate_left]. *)
        | Ror : (t -> t -> t, t * t) operator
            (** Bit-vector rotate right.

            This is a non-indexed variant of SMT-LIB [rotate_right]. *)
        | Sdiv : (t -> t -> t, t * t) operator
            (** Bit-vector signed division.

            SMT-LIB: [bvsdiv] *)
        | Sge : (t -> t -> t, t * t) operator
            (** Bit-vector signed greater than or equal.

            SMT-LIB: [bvsge] *)
        | Sgt : (t -> t -> t, t * t) operator
            (** Bit-vector signed greater than.

            SMT-LIB: [bvsgt] *)
        | Shl : (t -> t -> t, t * t) operator
            (** Bit-vector signed less than.

            SMT-LIB: [bvslt] *)
        | Shr : (t -> t -> t, t * t) operator
            (** Bit-vector logical right shift.

            SMT-LIB: [bvshr] *)
        | Sle : (t -> t -> t, t * t) operator
            (** Bit-vector signed less than or equal.

            SMT-LIB: [bvsle] *)
        | Slt : (t -> t -> t, t * t) operator
            (** Bit-vector signed less than.

            SMT-LIB: [bvslt] *)
        | Smod : (t -> t -> t, t * t) operator
            (** Bit-vector signed modulo.

            SMT-LIB: [bvsmod] *)
        | Srem : (t -> t -> t, t * t) operator
            (** Bit-vector signed remainder.

            SMT-LIB: [bvsrem] *)
        | Sub : (t -> t -> t, t * t) operator
            (** Bit-vector subtraction.

            SMT-LIB: [bvsub] *)
        | Udiv : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned division.

            SMT-LIB: [bvudiv] *)
        | Uge : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned greater than or equal.

            SMT-LIB: [bvuge] *)
        | Ugt : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned greater than.

            SMT-LIB: [bvugt] *)
        | Ule : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned less than or equal.

            SMT-LIB: [bvule] *)
        | Ult : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned less than.

            SMT-LIB: [bvult] *)
        | Urem : (t -> t -> t, t * t) operator
            (** Bit-vector unsigned remainder.

            SMT-LIB: [bvurem] *)
        | Xor : (t -> t -> t, t * t) operator
            (** Bit-vector xor.

            SMT-LIB: [bvxor] *)

      val term : ('a, 'b) operator -> 'a
      (**
         [term op ..]
         create a bit-vector term constructor of given kind.

         @param op The operator kind.

         @return A function to build a term representing an operation
                 of given kind.
      *)

      val pred : t -> t
      (**
         [pred t]
         create a bit-vector decrement.

         @param t The bit-vector term.

         @return Decrement by one.
      *)

      val succ : t -> t
      (**
         [succ t]
         create a bit-vector increment.

         @param t The bit-vector term.

         @return Increment by one.
      *)

      val neg : t -> t
      (**
         [neg t]
         create a bit-vector negation.

         @param t The bit-vector term.

         @return SMT-LIB: [bvneg].
      *)

      val add : t -> t -> t
      (**
         [add t0 t1]
         create a bit-vector addition.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvadd]
      *)

      val sadd_overflow : t -> t -> t
      (**
         [sadd_overflow t0 t1]
         create a bit-vector signed addition overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if signed addition
         produces an overflow
      *)

      val uadd_overflow : t -> t -> t
      (**
         [uadd_overflow t0 t1]
         create a bit-vector unsigned addition overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if unsigned addition
         produces an overflow
      *)

      val sub : t -> t -> t
      (**
         [sub t0 t1]
         create a bit-vector substraction.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsub]
      *)

      val ssub_overflow : t -> t -> t
      (**
         [ssub_overflow t0 t1]
         create a bit-vector signed substraction overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if signed substraction
         produces an overflow
      *)

      val usub_overflow : t -> t -> t
      (**
         [usub_overflow t0 t1]
         create a bit-vector ubsigned substraction overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if unsigned substraction
         produces an overflow
      *)

      val mul : t -> t -> t
      (**
         [mul t0 t1]
         create a bit-vector multiplication.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvmul]
      *)

      val smul_overflow : t -> t -> t
      (**
         [smul_overflow t0 t1]
         create a bit-vector signed multiplication overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if signed multiplication
         produces an overflow
      *)

      val umul_overflow : t -> t -> t
      (**
         [umul_overflow t0 t1]
         create a bit-vector unsigned multiplication overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if unsigned multiplication
         produces an overflow
      *)

      val sdiv : t -> t -> t
      (**
         [sdiv t0 t1]
         create a bit-vector signed division.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsdiv]
      *)

      val sdiv_overflow : t -> t -> t
      (**
         [sdiv_overflow t0 t1]
         create a bit-vector signed division overflow test.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return Single bit to indicate if signed division
         produces an overflow
      *)

      val udiv : t -> t -> t
      (**
         [udiv t0 t1]
         create a bit-vector unsigned division.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvudiv]
      *)

      val smod : t -> t -> t
      (**
         [smod t0 t1]
         create a bit-vector signed modulo.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsmod]
      *)

      val srem : t -> t -> t
      (**
         [srem t0 t1]
         create a bit-vector signed reminder.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsrem]
      *)

      val urem : t -> t -> t
      (**
         [urem t0 t1]
         create a bit-vector unsigned reminder.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvurem]
      *)

      val logand : t -> t -> t
      (**
         [logand t0 t1]
         create a bit-vector and.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvand]
      *)

      val lognand : t -> t -> t
      (**
         [lognand t0 t1]
         create a bit-vector nand.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvnand]
      *)

      val redand : t -> t
      (**
         [redand t]
         create a bit-vector and reduction.

         @param t The bit-vector term.

         @return Bit-wise {b and} reduction, all bits are {b and}'ed
         together into a single bit.
      *)

      val logor : t -> t -> t
      (**
         [logor t0 t1]
         create a bit-vector or.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvor]
      *)

      val lognor : t -> t -> t
      (**
         [lognor t0 t1]
         create a bit-vector nor.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvnor]
      *)

      val redor : t -> t
      (**
         [redor t]
         create a bit-vector or reduction.

         @param t The bit-vector term.

         @return Bit-wise {b or} reduction, all bits are {b or}'ed
         together into a single bit.
      *)

      val logxor : t -> t -> t
      (**
         [logxor t0 t1]
         create a bit-vector xor.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvxor]
      *)

      val logxnor : t -> t -> t
      (**
         [logxnor t0 t1]
         create a bit-vector xnor.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvxnor]
      *)

      val redxor : t -> t
      (**
         [redxor t]
         create a bit-vector xor reduction.

         @param t The bit-vector term.

         @return Bit-wise {b xor} reduction, all bits are {b xor}'ed
         together into a single bit.
      *)

      val lognot : t -> t
      (**
         [lognot t]
         create a bit-vector not (one's complement).

         @param t The first bit-vector term.

         @return SMT-LIB: [bvnot]
      *)

      val shift_left : t -> t -> t
      (**
         [shift_left t0 t1]
         create a bit-vector logical left shift.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB [bvshl]
      *)

      val shift_right : t -> t -> t
      (**
         [shift_right t0 t1]
         create a bit-vector arithmetic right shift.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB [bvashr]
      *)

      val shift_right_logical : t -> t -> t
      (**
         [shift_right_logical t0 t1]
         create a bit-vector logical right shift.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB [bvshr]
      *)

      val rotate_left : t -> t -> t
      (**
         [rotate_left t0 t1]
         create a bit-vector left rotation.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return non indexed variant of SMT-LIB [rotate_left]
      *)

      val rotate_lefti : t -> int -> t
      (**
         [rotate_lefti t n]
         create a bit-vector left rotation.

         @param t The bit-vector term.
         @param n The rotation count.

         @return SMT-LIB: [rotate_left] (indexed)
      *)

      val rotate_right : t -> t -> t
      (**
         [rotate_right t0 t1]
         create a bit-vector right rotation.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return non indexed variant of SMT-LIB [rotate_right]
      *)

      val rotate_righti : t -> int -> t
      (**
         [rotate_righti t n]
         create a bit-vector right rotation.

         @param t The bit-vector term.
         @param n The rotation count.

         @return SMT-LIB: [rotate_right] (indexed)
      *)

      val zero_extend : int -> t -> t
      (**
         [zero_extend n t]
         create a bit-vector unsigned extension.

         @param n The number of bits.
         @param t The bit-vector term.

         @return SMT-LIB: [zero_extend] (indexed)
      *)

      val sign_extend : int -> t -> t
      (**
         [sign_extend n t]
         create a bit-vector signed extension.

         @param n The number of bits.
         @param t The bit-vector term.

         @return SMT-LIB: [sign_extend] (indexed)
      *)

      val append : t -> t -> t
      (**
         [append t0 t1]
         create a bit-vector concat.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [concat]
      *)

      val concat : t array -> t
      (**
         [concat ts]
         create a bit-vector {i n}ary concat.

         @param ts The bit-vector terms.

         @return SMT-LIB: [concat]
      *)

      val repeat : int -> t -> t
      (**
         [repeat n t]
         create a bit-vector repetition.

         @param n The number of repetitions.
         @param t The bit-vector term.

         @return SMT-LIB: [repeat] (indexed)
      *)

      val extract : hi:int -> lo:int -> t -> t
      (**
         [extract hi lo t]
         create a bit-vector extract.

         @param hi MSB index.
         @param lo LSB index.
         @param t The bit-vector term.

         @return SMT-LIB: [extract] (indexed)
      *)

      val sge : t -> t -> t
      (**
         [sge t0 t1]
         create a bit-vector signed greater than or equal.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsge]
      *)

      val uge : t -> t -> t
      (**
         [uge t0 t1]
         create a bit-vector unsigned greater than or equal.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvuge]
      *)

      val sgt : t -> t -> t
      (**
         [sgt t0 t1]
         create a bit-vector signed greater than.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsgt]
      *)

      val ugt : t -> t -> t
      (**
         [ugt t0 t1]
         create a bit-vector unsigned greater than.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvugt]
      *)

      val sle : t -> t -> t
      (**
         [sle t0 t1]
         create a bit-vector signed lower than or equal.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvsle]
      *)

      val ule : t -> t -> t
      (**
         [ule t0 t1]
         create a bit-vector unsigned lower than or equal.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvadd]
      *)

      val slt : t -> t -> t
      (**
         [slt t0 t1]
         create a bit-vector signed lower than.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvslt]
      *)

      val ult : t -> t -> t
      (**
         [ult t0 t1]
         create a bit-vector unsigned lower than.

         @param t0 The first bit-vector term.
         @param t1 The second bit-vector term.

         @return SMT-LIB: [bvult]
      *)

      val to_bl : t -> t
      (** Same as {!val:Bl.of_bv}. *)

      val assignment : bv value -> Z.t
      (**
         [assignment t]
         get bit-vector representation of the current model value of given term.

         @param t The term to query a model value for.

         @return bit-vector representation of current model value of term [t].
      *)
    end

    (** Rounding-mode *)
    module Rm : sig
      type t = rm term
      (** A rounding-mode term. *)

      (**
         Rounding mode for floating-point operations.

         For some floating-point operations, infinitely precise results
         may not be representable in a given format. Hence, they are rounded
         modulo one of five rounding modes to a representable floating-point
         number.

         The following rounding modes follow the SMT-LIB theory for
         floating-point arithmetic, which in turn is based on
         IEEE Standard 754.
         The rounding modes are specified in Sections 4.3.1 and 4.3.2
         of the IEEE Standard 754.
      *)
      type 'a operator =
        | Rne : rm term operator
            (** Round to the nearest even number.
            If the two nearest floating-point numbers bracketing an
            unrepresentable infinitely precise result are equally near,
            the one with an even least significant digit will be delivered.

            SMT-LIB: [RNE] roundNearestTiesToEven
        *)
        | Rna : rm term operator
            (** Round to the nearest number away from zero.
            If the two nearest floating-point numbers bracketing an
            unrepresentable infinitely precise result are equally near,
            the one with larger magnitude will be selected.

            SMT-LIB: [RNA] roundNearestTiesToAway
        *)
        | Rtn : rm term operator
            (** Round towards negative infinity (-oo).
            The result shall be the format’s floating-point number
            (possibly -oo) closest to and no less than the infinitely
            precise result.

            SMT-LIB: [RTN] roundTowardNegative
        *)
        | Rtp : rm term operator
            (** Round towards positive infinity (+oo).
            The result shall be the format’s floating-point number
            (possibly +oo) closest to and no less than the infinitely
            precise result.

            SMT-LIB: [RTP] roundTowardPositive
        *)
        | Rtz : rm term operator
            (** Round towards zero.
            The result shall be the format’s floating-point number
            closest to and no greater in magnitude than the infinitely
            precise result.

            SMT-LIB: [RTZ] roundTowardZero
        *)

      val term : 'a operator -> 'a
      (**
         [term op]
         create a rounding-mode term of given kind.

         @param op The operator kind.

         @return A term representing an operation of given kind.
      *)

      val rne : t
      (** Same as {!val:term} {!constructor:Rne} *)

      val rna : t
      (** Same as {!val:term} {!constructor:Rna} *)

      val rtn : t
      (** Same as {!val:term} {!constructor:Rtn} *)

      val rtp : t
      (** Same as {!val:term} {!constructor:Rtp} *)

      val rtz : t
      (** Same as {!val:term} {!constructor:Rtz} *)
    end

    (** Floating-point *)
    module Fp : sig
      type t = fp term
      (** A floating-point term. *)

      val pos_zero : fp sort -> t
      (**
         [pos_zero sort]
         create a floating-point positive zero value (SMT-LIB: [+zero]).

         @param sort The sort of the value.

         @return A term representing the floating-point positive zero value
         of given floating-point sort.
      *)

      val neg_zero : fp sort -> t
      (**
         [neg_zero sort]
         create a floating-point negative zero value (SMT-LIB: [-zero]).

         @param sort The sort of the value.

         @return A term representing the floating-point negative zero value
         of given floating-point sort.
      *)

      val pos_inf : fp sort -> t
      (**
         [pos_inf sort]
         create a floating-point positive infinity value (SMT-LIB: [+oo]).

         @param sort The sort of the value.

         @return A term representing the floating-point positive infinity value
         of given floating-point sort.
      *)

      val neg_inf : fp sort -> t
      (**
         [neg_inf sort]
         create a floating-point negative infinity value (SMT-LIB: [-oo]).

         @param sort The sort of the value.

         @return A term representing the floating-point negative infinity value
         of given floating-point sort.
      *)

      val nan : fp sort -> t
      (**
         [nan sort]
         create a floating-point NaN value.

         @param sort The sort of the value.

         @return A term representing the floating-point NaN value of given
         floating-point sort.
      *)

      val of_float : fp sort -> rm term Rm.operator -> float -> t
      (**
         [of_float sort rm value]
         create a floating-point value from its float representation,
         with respect to given rounding mode.

         @param sort The sort of the value.
         @param rm The rounding mode.
         @param value The floating-point value.

         @return A term representing the floating-point value of given sort.
      *)

      val of_real : fp sort -> rm term Rm.operator -> string -> t
      (**
         [of_real sort rm real]
         create a floating-point value from its real representation, given as a
         decimal string, with respect to given rounding mode.

         @param sort The sort of the value.
         @param rm The rounding mode.
         @param real The decimal string representing a real value.

         @return A term representing the floating-point value of given sort.
      *)

      val of_rational :
        fp sort -> rm term Rm.operator -> num:string -> den:string -> t
      (**
         [from_rational sort rm num den]
         create a floating-point value from its rational representation,
         given as a two decimal strings representing the numerator and
         denominator, with respect to given rounding mode.

         @param sort The sort of the value.
         @param rm The rounding mode.
         @param num The decimal string representing the numerator.
         @param den The decimal string representing the denominator.

         @return A term representing the floating-point value of given sort.
      *)

      type ieee_754 = private {
        sign : bv term;
        exponent : bv term;
        significand : bv term;
      }
      (** Floating-point IEEE 754 representation. *)

      (** The term operator. *)
      type ('a, 'b, 'c) operator =
        | Abs : (t -> t, t, fp) operator
            (** Floating-point absolute value.

            SMT-LIB: [fp.abs] *)
        | Add : (rm term -> t -> t -> t, rm term * t * t, fp) operator
            (** Floating-point addition.

            SMT-LIB: [fp.add] *)
        | Div : (rm term -> t -> t -> t, rm term * t * t, fp) operator
            (** Floating-point division.

            SMT-LIB: [fp.div] *)
        | Eq : (t -> t -> bv term, t * t, bv) operator
            (** Floating-point equality.

            SMT-LIB: [fp.eq] *)
        | Fma : (rm term -> t -> t -> t -> t, rm term * t * t * t, fp) operator
            (** Floating-point fused multiplcation and addition.

            SMT-LIB: [fp.fma] *)
        | Fp
            : ( sign:bv term -> exponent:bv term -> bv term -> t,
                ieee_754,
                fp )
              operator
            (** Floating-point IEEE 754 value.

            SMT-LIB: [fp] *)
        | Geq : (t -> t -> bv term, t * t, bv) operator
            (** Floating-point greater than or equal.

            SMT-LIB: [fp.geq] *)
        | Gt : (t -> t -> bv term, t * t, bv) operator
            (** Floating-point greater than.

            SMT-LIB: [fp.gt] *)
        | Is_inf : (t -> bv term, t, bv) operator
            (** Floating-point is infinity tester.

            SMT-LIB: [fp.isInfinite] *)
        | Is_nan : (t -> bv term, t, bv) operator
            (** Floating-point is Nan tester.

            SMT-LIB: [fp.isNaN] *)
        | Is_neg : (t -> bv term, t, bv) operator
            (** Floating-point is negative tester.

            SMT-LIB: [fp.isNegative] *)
        | Is_normal : (t -> bv term, t, bv) operator
            (** Floating-point is normal tester.

            SMT-LIB: [fp.isNormal] *)
        | Is_pos : (t -> bv term, t, bv) operator
            (** Floating-point is positive tester.

            SMT-LIB: [fp.isPositive] *)
        | Is_subnormal : (t -> bv term, t, bv) operator
            (** Floating-point is subnormal tester.

            SMT-LIB: [fp.isSubnormal] *)
        | Is_zero : (t -> bv term, t, bv) operator
            (** Floating-point is zero tester.

            SMT-LIB: [fp.isZero] *)
        | Leq : (t -> t -> bv term, t * t, bv) operator
            (** Floating-point less than or equal.

            SMT-LIB: [fp.leq] *)
        | Lt : (t -> t -> bv term, t * t, bv) operator
            (** Floating-point less than.

            SMT-LIB: [fp.lt] *)
        | Max : (t -> t -> t, t * t, fp) operator
            (** Floating-point max.

            SMT-LIB: [fp.max] *)
        | Min : (t -> t -> t, t * t, fp) operator
            (** Floating-point min.

            SMT-LIB: [fp.min] *)
        | Mul : (rm term -> t -> t -> t, rm term * t * t, fp) operator
            (** Floating-point multiplcation.

            SMT-LIB: [fp.mul] *)
        | Neg : (t -> t, t, fp) operator
            (** Floating-point negation.

            SMT-LIB: [fp.neg] *)
        | Rem : (t -> t -> t, t * t, fp) operator
            (** Floating-point remainder.

            SMT-LIB: [fp.rem] *)
        | Rti : (rm term -> t -> t, rm term * t, fp) operator
            (** Floating-point round to integral.

            SMT-LIB: [fp.roundToIntegral] *)
        | Sqrt : (rm term -> t -> t, rm term * t, fp) operator
            (** Floating-point round to square root.

            SMT-LIB: [fp.sqrt] *)
        | Sub : (rm term -> t -> t -> t, rm term * t * t, fp) operator
            (** Floating-point round to subtraction.

            SMT-LIB: [fp.sqrt] *)
        | From_bv
            : ( exponent:int -> int -> bv term -> t,
                int * int * bv term,
                fp )
              operator
            (** Floating-point to_fp from IEEE 754 bit-vector.

            SMT-LIB: [to_fp] (indexed) *)
        | From_fp
            : ( exponent:int -> int -> rm term -> t -> t,
                int * int * rm term * t,
                fp )
              operator
            (** Floating-point to_fp from floating-point.

            SMT-LIB: [to_fp] (indexed) *)
        | From_sbv
            : ( exponent:int -> int -> rm term -> bv term -> t,
                int * int * rm term * bv term,
                fp )
              operator
            (** Floating-point to_fp from signed bit-vector value.

            SMT-LIB: [to_fp] (indexed) *)
        | From_ubv
            : ( exponent:int -> int -> rm term -> bv term -> t,
                int * int * rm term * bv term,
                fp )
              operator
            (** Floating-point to_fp from unsigned bit-vector value.

            SMT-LIB: [to_fp_unsigned] (indexed) *)
        | To_sbv
            : (int -> rm term -> t -> bv term, int * rm term * t, bv) operator
            (** Floating-point to_sbv.

            SMT-LIB: [fp.to_sbv] (indexed) *)
        | To_ubv
            : (int -> rm term -> t -> bv term, int * rm term * t, bv) operator
            (** Floating-point to_ubv.

            SMT-LIB: [fp.to_ubv] (indexed) *)

      val term : ('a, 'b, 'c) operator -> 'a
      (**
         [term op ..]
         create a floating-point term constructor of given kind.

         @param op The operator kind.

         @return A function to build a term representing an operation
                 of given kind.
      *)

      val make : sign:bv term -> exponent:bv term -> bv term -> t
      (**
         [make ~sign ~exponent significand]
         create a floating-point value from its IEEE 754 standard
         representation given as three bitvectors representing the sign bit,
         the exponent and the significand.

         @param sign The sign bit.
         @param exponent The exponent bit-vector.
         @param significand The significand bit-vector.

         @return A term representing the floating-point value.
      *)

      val of_sbv : exponent:int -> int -> rm term -> bv term -> t
      (**
         [of_sbv ~exponent size rm t]
         create a floatingt-point to_fp from signed bit-vector value.

         @param exponent The size of the exponent.
         @param size The total size of the floating-point.
         @param rm The rounding-mode.
         @param t The bit-vector term.

         @return SMT-LIB: [to_fp] (indexed)
      *)

      val of_ubv : exponent:int -> int -> rm term -> bv term -> t
      (**
         [of_ubv ~exponent size rm t]
         create a floatingt-point to_fp from unsigned bit-vector value.

         @param exponent The size of the exponent.
         @param size The total size of the floating-point.
         @param rm The rounding-mode.
         @param t The bit-vector term.

         @return SMT-LIB: [to_fp] (indexed)
      *)

      val of_bv : exponent:int -> int -> bv term -> t
      (**
         [of_bv ~exponent size rm t]
         create a floatingt-point to_fp from IEEE 754 bit-vector.

         @param exponent The size of the exponent.
         @param size The total size of the floating-point.
         @param rm The rounding-mode.
         @param t The bit-vector term.

         @return SMT-LIB: [to_fp] (indexed)
      *)

      val of_fp : exponent:int -> int -> rm term -> fp term -> t
      (**
         [of_fp ~exponent size rm t]
         create a floatingt-point to_fp from floating-point.

         @param exponent The size of the exponent.
         @param size The total size of the floating-point.
         @param rm The rounding-mode.
         @param t The floating-point term.

         @return SMT-LIB: [to_fp] (indexed)
      *)

      val abs : t -> t
      (**
         [abs t]
         create a floatingt-point absolute value.

         @param t The floating-point term.

         @return SMT-LIB: [fp.abs]
      *)

      val neg : t -> t
      (**
         [neg t]
         create a floatingt-point negation.

         @param t The floating-point term.

         @return SMT-LIB: [fp.neg]
      *)

      val add : rm term -> t -> t -> t
      (**
         [add rm t0 t1]
         create a floating-point addition.

         @param rm The roundint-mode.
         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.add]
      *)

      val sub : rm term -> t -> t -> t
      (**
         [sub rm t0 t1]
         create a floating-point substraction.

         @param rm The roundint-mode.
         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.sub]
      *)

      val mul : rm term -> t -> t -> t
      (**
         [mul rm t0 t1]
         create a floating-point multiplication.

         @param rm The roundint-mode.
         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.mul]
      *)

      val div : rm term -> t -> t -> t
      (**
         [div rm t0 t1]
         create a floating-point division.

         @param rm The roundint-mode.
         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.div]
      *)

      val fma : rm term -> t -> t -> t -> t
      (**
         [fma rm t0 t1 t2]
         create a floating-point fused multiplication and addition.

         @param rm The roundint-mode.
         @param t0 The first floating-point term.
         @param t1 The second floating-point term.
         @param t2 The third floating-point term.

         @return SMT-LIB: [fp.fma]
      *)

      val sqrt : rm term -> t -> t
      (**
         [sqrt rm t]
         create a floating-point round to square root.

         @param rm The roundint-mode.
         @param t0 The floating-point term.

         @return SMT-LIB: [fp.sqrt]
      *)

      val rem : t -> t -> t
      (**
         [rem t0 t1]
         create a floating-point remainder.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.rem]
      *)

      val rti : rm term -> t -> t
      (**
         [rti rm t]
         create a floating-point round to integral.

         @param rm The roundint-mode.
         @param t0 The floating-point term.

         @return SMT-LIB: [fp.roundToIntegral]
      *)

      val min : t -> t -> t
      (**
         [min t0 t1]
         create a floating-point min.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.min]
      *)

      val max : t -> t -> t
      (**
         [max t0 t1]
         create a floating-point max.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.max]
      *)

      val leq : t -> t -> bv term
      (**
         [leq t0 t1]
         create a floating-point less than or equal.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.leq]
      *)

      val lt : t -> t -> bv term
      (**
         [lt t0 t1]
         create a floating-point less than.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.lt]
      *)

      val geq : t -> t -> bv term
      (**
         [geq t0 t1]
         create a floating-point greater than or equal.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.geq]
      *)

      val gt : t -> t -> bv term
      (**
         [gt t0 t1]
         create a floating-point greater than.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.gt]
      *)

      val eq : t -> t -> bv term
      (**
         [eq t0 t1]
         create a floating-point equality.

         @param t0 The first floating-point term.
         @param t1 The second floating-point term.

         @return SMT-LIB: [fp.eq]
      *)

      val is_normal : t -> bv term
      (**
         [is_normal t]
         create a floatingt-point is normal tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isNormal]
      *)

      val is_subnormal : t -> bv term
      (**
         [is_subnormal t]
         create a floatingt-point is subnormal tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isSubnormal]
      *)

      val is_zero : t -> bv term
      (**
         [is_zero t]
         create a floatingt-point is zero tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isZero]
      *)

      val is_infinite : t -> bv term
      (**
         [is_infinite t]
         create a floatingt-point is infinite tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isInfinite]
      *)

      val is_nan : t -> bv term
      (**
         [is_nan t]
         create a floatingt-point is Nan tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isNan]
      *)

      val is_negative : t -> bv term
      (**
         [is_negative t]
         create a floatingt-point is negative tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isNegative]
      *)

      val is_positive : t -> bv term
      (**
         [is_positive t]
         create a floatingt-point is positive tester.

         @param t The floating-point term.

         @return SMT-LIB: [fp.isPositive]
      *)

      val to_sbv : int -> rm term -> t -> bv term
      (**
         [to_sbv t]
         create a floatingt-point is to_sbv term.

         @param t The floating-point term.

         @return SMT-LIB: [fp.to_sbv] (indexed)
      *)

      val to_ubv : int -> rm term -> t -> bv term
      (**
         [to_ubv t]
         create a floatingt-point is to_ubv term.

         @param t The floating-point term.

         @return SMT-LIB: [fp.to_ubv] (indexed)
      *)

      val assignment : rm term Rm.operator -> fp value -> float
      (**
         [assignement t ]
         get floatint-point representation of the current model value of
         given floating-point term.

         @param term The term to query a model value for.

         @return Floating-point representations of the given term.
      *)
    end

    (** Array *)
    module Ar : sig
      type ('a, 'b) t = ('a, 'b) ar term
      (** An array term which maps ['a] to ['b]. *)

      val make : ('a, 'b) ar sort -> 'b term -> ('a, 'b) t
      (**
         [make sort value]
         create a one-dimensional constant array of given sort,
         initialized with given value.

         @param sort The sort of the array.
         @param value The value to initialize the elements of the array with.

         @return A term representing a constant array of given sort.
      *)

      val select : ('a, 'b) t -> 'a term -> 'b term
      (**
         [select t i]
         create an array access.

         @param t The array term.
         @param i The index term.

         @return SMT-LIB: [select]
      *)

      val store : ('a, 'b) t -> 'a term -> 'b term -> ('a, 'b) t
      (**
         [store t i e]
         create an array write.

         @param t The array term.
         @param i The index term.
         @param e The element term.

         @return SMT-LIB: [store]
      *)

      val assignment :
        ('a, 'b) ar value -> ('a value * 'b value) array * 'b value option
      (**
         [assignment t]
         get the current model value of given array term.

         The value of indices and values can be queried via
         {!val:Bv.assignment} and {!val:Fp.assignment}.

         @param t The term to query a model value for.

         @return An array of associations between indices and values.
           The value of all other indices is [Some default] when
           base array is constant array, otherwise, it is [None].
      *)
    end

    (** Uninterpreted function *)
    module Uf : sig
      type ('a, 'b) t = ('a, 'b) fn term
      (** A function term which maps ['a] to ['b]. *)

      val lambda : 'a Sort.variadic -> ('a variadic -> 'b term) -> ('a, 'b) t
      (**
         [lambda sorts f]
         create a function definition.

         @param sorts The argument sorts.
         @param f A function that take the function formal parameters and
         return a term.

         @return a function definition
      *)

      val apply : ('a, 'b) t -> 'a variadic -> 'b term
      (**
         [apply t args]
         create a function application.

         @param t The function term.
         @param args The argument terms.

         @return a function application
      *)

      (** Statically typed list of function argument values. *)
      type 'a variadic =
        | [] : unit variadic
        | ( :: ) :
            ([< bv | rm | fp ] as 'a) value * 'b variadic
            -> ('a -> 'b) variadic

      val assignment : ('a, 'b) fn value -> ('a variadic * 'b value) array
      (**
         [assignment t]
         get the current model value of given function term.

         The value of arguments and values can be queried via
         {!val:Bv.assignment} and {!val:Fp.assignment}.

         @param t The term to query a model value for.

         @return An array of associations between `arity` arguments and a value.
      *)
    end

    val const : 'a sort -> string -> 'a term
    (**
       [const sort symbol]
       create a (first-order) constant of given sort with given symbol.

       This creates a 0-arity function symbol.

       @param sort The sort of the constant.
       @param symbol The symbol of the constant.

       @return A term representing the constant.
    *)

    val equal : 'a t -> 'a t -> bv t
    (**
       [equal t0 t1]
       create an equality term.

       @param t0 The first term.
       @param t1 The second term.

       @return SMT-LIB: [=]
    *)

    val distinct : 'a t -> 'a t -> bv t
    (**
       [distinct t0 t1]
       create an disequality term.

       @param t0 The first term.
       @param t1 The second term.

       @return SMT-LIB: [not (= t0 t1)]
    *)

    val ite : bv t -> 'a t -> 'a t -> 'a t
    (**
       [ite t0 t1 t2]
       create an if-then-else term.

       @param t0 The condition term.
       @param t1 The {i then} term.
       @param t2 The {i else} term.

       @return SMT-LIB: [ite]
    *)

    val hash : 'a t -> int
    (**
       [hash t]
       compute the hash value for a term.

       @param t The term.

       @return The hash value of the term.
    *)

    val sort : 'a t -> 'a sort
    (**
       [sort t]
       get the sort of a term.

       @param t The term.

       @return The sort of the term.
    *)

    val pp : Format.formatter -> 'a term -> unit
    (**
       [pp formatter t]
       pretty print term.

       @param formatter The outpout formatter
       @param t The term.
    *)

    (** {1 View} *)

    (** Algebraic view of formula terms. *)
    type 'a view =
      | Value : 'a value -> 'a view
      | Const : 'a sort * string -> 'a view
      | Var : ([< bv | rm | fp ] as 'a) sort -> 'a view
      | Lambda : 'a variadic * 'b term -> ('a, 'b) fn view
      | Equal :
          ([< bv | rm | fp | ('b, 'c) ar ] as 'a) term * 'a term
          -> bv view
      | Distinct :
          ([< bv | rm | fp | ('b, 'c) ar ] as 'a) term * 'a term
          -> bv view
      | Ite :
          bv term * ([< bv | rm | fp | ('b, 'c) ar ] as 'a) term * 'a term
          -> 'a view
      | Bv : ('a, 'b) Bv.operator * 'b -> bv view
      | Fp : ('a, 'b, 'c) Fp.operator * 'b -> 'c view
      | Select : ('a, 'b) ar term * 'a term -> 'b view
      | Store : ('a, 'b) ar term * 'a term * 'b term -> ('a, 'b) ar view
      | Apply : ('a, 'b) fn term * 'a variadic -> 'b view

    val view : 'a term -> 'a view
    (**
       [view t]
       destructurate a term.

       @param t The term.

       @return The view of the term and its children.
    *)
  end

  (** {1 Formula} *)

  val assert' : ?name:string -> bv term -> unit
  (**
     [assert' ~name t]
     assert that the condition [t] is [true].

     [t] must be a boolean term ({!type:bv} {!type:term} of size 1).

     @param name The name of the assertion, if any.
     @param t The formula term to assert.
  *)

  (** A satisfiability result. *)
  type result =
    | Sat  (** sat *)
    | Unsat  (** unsat *)
    | Unknown  (** unknown *)

  val pp_result : Format.formatter -> result -> unit
  (**
     [pp formatter result]
     pretty print result.

     @param formatter The output formatter.
     @param result The result to print.
  *)

  val check_sat : ?interrupt:('a -> int) * 'a -> unit -> result
  (**
     [check_sat ~interrupt ()]
     check satisfiability of current input formula.

     @param interrupt Stop the research and return {!constructor:Unknown}
     if the callback function returns a positive value.
     Run into completion otherwise.

     @return {!constructor:Sat} if the input formula is satisfiable and
     {!constructor:Unsat} if it is unsatisfiable, and {!constructor:Unknown}
     when neither satistifiability nor unsatisfiability was determined,
     for instance when it was terminated by {!val:timeout}.
  *)

  val timeout : float -> (?interrupt:(float -> int) * float -> 'b) -> 'b
  (**
     [timeout t f]
     configure the interruptible function [f] with a timeout of [t] seconds.

     [timeout] can be used to limit the time spend on
     {!val:check_sat} or {!val:check_sat_assuming}.
     For instance, for a 1 second time credit, use:
     - [(timeout 1. check_sat) ()]
     - [(timeout 1. check_sat_assuming) assumptions]

     @param t Timeout in second.
     @param f The function to configure.

     @return An interruptible function configured to stop on timeout.
  *)

  val get_value : 'a term -> 'a value
  (**
     [get_value t]
     get a term representing the model value of a given term.

     Requires that the last {!val:check_sat} query returned {!constructor:Sat}.

     @param t The term to query a model value for.

     @return A term representing the model value of term [t].
  *)

  val unsafe_close : unit -> unit
  (**
     [unafe_close ()]
     close the session.

     UNSAFE: call this ONLY to release the resources earlier
     if the session is about to be garbage collected.
  *)
end

(** Create a new Bitwuzla session in incremental mode. *)
module Incremental () : sig
  include module type of Once ()

  (** {1 Formula} *)

  val push : int -> unit
  (**
     [push nlevels]
     push context levels.

     @param nlevels The number of context levels to push.
  *)

  val pop : int -> unit
  (**
     [pop nlevels]
     pop context levels.

     @param nlevels The number of context levels to pop.
  *)

  val check_sat_assuming :
    ?interrupt:('a -> int) * 'a ->
    ?names:string array ->
    bv term array ->
    result
  (**
     [check_sat_assuming ~interrupt ~names assumptions]
     check satisfiability of current input formula, with the search for
     a solution guided by the given assumptions.

     An input formula consists of assertions added via {!val:assert'}
     combined with assumptions via Boolean [and].
     Unsatifiable assumptions can be queried via {!val:get_unsat_assumptions}.

     @param interrupt Stop the research and return {!constructor:Unknown}
     if the callback function returns a positive value.
     Run into completion otherwise.
     @param names The assumption names, if any.
     @param assumption The set of assumptions guiding the research of solutions.

     @return {!constructor:Sat} if the input formula is satisfiable and
     {!constructor:Unsat} if it is unsatisfiable, and {!constructor:Unknown}
     when neither satistifiability nor unsatisfiability was determined,
     for instance when it was terminated by {!val:timeout}.
  *)

  val get_unsat_assumptions : unit -> bv term array
  (**
     [get_unsat_assumptions ()]
     get the set of unsat assumptions.

     Unsat assumptions are assumptions that force an input formula to become
     unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
     failed assumptions in MiniSAT.

     Requires that the last {!val:check_sat} query returned
     {!constructor:Unsat}.

     @return An array with unsat assumptions.
  *)
end

(** Create a new Bitwuzla session in incremental mode while enabling
    unsatifiable core generation. *)
module Unsat_core () : sig
  include module type of Incremental ()

  val get_unsat_core : unit -> bv term array
  (**
     [get_unsat_core ()]
     get the set unsat core (unsat assertions).

     The unsat core consists of the set of assertions that force an
     input formula to become unsatisfiable.

     Requires that the last {!val:check_sat} query returned
     {!constructor:Unsat}.

     @return An array with unsat assertions.
  *)
end
