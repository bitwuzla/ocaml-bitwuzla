/**************************************************************************/
/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.                */
/*                                                                        */
/*  Copyright (C) 2023 by the authors listed in the AUTHORS file at       */
/*  https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS                */
/*                                                                        */
/*  This file is part of Bitwuzla under the MIT license.                  */
/*  See COPYING for more information at                                   */
/*  https://github.com/bitwuzla/bitwuzla/blob/main/COPYING                */
/**************************************************************************/

#include <caml/mlvalues.h>
#include <bitwuzla/cpp/bitwuzla.h>

#include <api/checks.h>
#include <node/node.h>
#include <bv/bitvector.h>

#include <zarith.h>
#ifdef ARCH_SIXTYFOUR
#define Z_MAX_INT       0x3fffffffffffffff
#else
#define Z_MAX_INT       0x3fffffff
#endif

template <>
value
bitwuzla::Term::value(uint8_t base) const
{
  (void) base;
  BITWUZLA_CHECK_NOT_NULL(d_node);
  BITWUZLA_CHECK_TERM_IS_BV_VALUE(*this);
  return d_node->value<bzla::BitVector>().to_zarith();
}

value
bzla::BitVector::to_zarith() const
{
  assert(!is_null());
  value val;
  if (is_gmp()) {
    val = ml_z_from_mpz((mpz_t&)d_val_gmp);
  } else if (d_val_uint64 <= Z_MAX_INT) {
    val = Val_long(d_val_uint64);
  } else {
    mpz_t bits;
    mpz_init(bits);
    mpz_import(bits, 1, -1, sizeof(uint64_t), -1, 0, &d_val_uint64);
    val = ml_z_from_mpz(bits);
    mpz_clear(bits);
  }
  return val;
}
