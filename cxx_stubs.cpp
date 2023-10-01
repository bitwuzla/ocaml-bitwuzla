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

#include <string.h>

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>

typedef value mlvalue;

#include <bitwuzla/cpp/bitwuzla.h>

static struct custom_operations exception_operations =
  {
    "dummy operations after exception",
    custom_finalize_default,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
  };

extern "C" CAMLprim value
ocaml_bitwuzla_copyright ()
{
  return caml_copy_string(bitwuzla::copyright());
}

extern "C" CAMLprim value
ocaml_bitwuzla_version ()
{
  return caml_copy_string(bitwuzla::version());
}

static const value *vpp_open_vbox = NULL;
static const value *vpp_print_string = NULL;
static const value *vpp_print_char = NULL;
static const value *vpp_print_space = NULL;
static const value *vpp_close_box = NULL;

extern "C" CAMLprim void
ocaml_bitwuzla_init_format (void)
{
  vpp_open_vbox = caml_named_value("Format.pp_open_vbox");
  vpp_print_string = caml_named_value("Format.pp_print_string");
  vpp_print_char = caml_named_value("Format.pp_print_char");
  vpp_print_space = caml_named_value("Format.pp_print_space");
  vpp_close_box = caml_named_value("Format.pp_close_box");
}

class Format : public std::streambuf
{
  mlvalue *vf;
public:
  Format(mlvalue *_vf) : vf(_vf) {};
  virtual std::streamsize xsputn(const char* s, std::streamsize n) override;
  virtual int overflow(int c) override;
};

std::streamsize Format::xsputn(const char *s, std::streamsize n)
{
  const char *p = s, *end = s + n;
  while (p != end) {
    const char *b = strchr(p, '\n');
    if (b == NULL) {
      mlvalue vs = caml_alloc_initialized_string(end - p, p);
      caml_callback2(*vpp_print_string, *vf, vs);
      break;
    } else {
      mlvalue vs = caml_alloc_initialized_string(b - p, p);
      caml_callback2(*vpp_print_string, *vf, vs);
      caml_callback2(*vpp_print_space, *vf, Val_unit);
      p = b + 1;
    }
  }
  return n;
}

int Format::overflow (int c)
{
  char ch = traits_type::to_char_type(c);
  if (ch == '\n') {
    caml_callback2(*vpp_print_space, *vf, Val_unit);
  } else {
    caml_callback2(*vpp_print_char, *vf, Val_int(c));
  }
  return c;
}

#define BITWUZLA_TRY_CATCH_BEGIN \
  try                            \
  {
#define BITWUZLA_TRY_CATCH_END \
  }                            \
  catch (bitwuzla::Exception &e) { caml_invalid_argument(e.msg().c_str()); }

#define BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom) \
  }                            \
  catch (bitwuzla::Exception &e) { \
    if(custom != Val_unit) \
      Custom_ops_val(custom) = &exception_operations; \
    caml_invalid_argument(e.msg().c_str()); \
  }

class Options : public bitwuzla::Options
{
public:
  Options() : bitwuzla::Options() {}
  ~Options() {}
  void * operator new (size_t size,
		       struct custom_operations * operations,
		       mlvalue *custom)
  {
    *custom = caml_alloc_custom(operations, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete (void *ptr) {}
};

#define Options_val(v) ((Options*)Data_custom_val(v))

static void options_delete (mlvalue vt)
{
  delete Options_val(vt);
}
static struct custom_operations options_operations =
  {
    "https://bitwuzla.github.io",
    &options_delete,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
  };



extern "C" CAMLprim mlvalue
ocaml_bitwuzla_options_new ()
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&options_operations, &custom) Options();
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim void
native_bitwuzla_options_set_numeric (mlvalue vt, intnat k, intnat v)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  Options_val(vt)->set((bitwuzla::Option)k, v);
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim void
ocaml_bitwuzla_options_set_numeric (mlvalue vt, mlvalue vk, mlvalue vv)
{
  native_bitwuzla_options_set_numeric(vt, Long_val(vk), Long_val(vv));
}

extern "C" CAMLprim void
native_bitwuzla_options_set_mode (mlvalue vt, intnat k, mlvalue vv)
{
  Options_val(vt)->set((bitwuzla::Option)k, String_val(vv));
}

extern "C" CAMLprim void
ocaml_bitwuzla_options_set_mode (mlvalue vt, mlvalue vk, mlvalue vv)
{
  native_bitwuzla_options_set_mode(vt, Long_val(vk), vv);
}

extern "C" CAMLprim intnat
native_bitwuzla_options_get_numeric (mlvalue vt, intnat k)
{
  return Options_val(vt)->get((bitwuzla::Option)k);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_options_get_numeric (mlvalue vt, mlvalue vk)
{
  return Val_long(native_bitwuzla_options_get_numeric(vt, Long_val(vk)));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_options_get_mode (mlvalue vt, intnat k)
{
  Options *t = Options_val(vt);
  return caml_copy_string(t->get_mode((bitwuzla::Option)k).c_str());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_options_get_mode (mlvalue vt, mlvalue vk)
{
  return native_bitwuzla_options_get_mode(vt, Long_val(vk));
}


class Sort : public bitwuzla::Sort
{
public:
  Sort(bitwuzla::Sort t) : bitwuzla::Sort(t) {}
  ~Sort() {}
  void * operator new (size_t size,
		       struct custom_operations * operations,
		       mlvalue *custom)
  {
    *custom = caml_alloc_custom(operations, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete (void *ptr) {}
};

#define Sort_val(v) ((Sort*)Data_custom_val(v))

static void sort_delete (mlvalue vt)
{
  delete Sort_val(vt);
}
extern "C" CAMLprim int native_bitwuzla_sort_compare (mlvalue v1, mlvalue v2)
{
  uint64_t i1 = Sort_val(v1)->id(), i2 = Sort_val(v2)->id();
  return (i1 >= i2) - (i1 <= i2);
}
extern "C" CAMLprim intnat native_bitwuzla_sort_hash (mlvalue vt)
{
  return std::hash<bitwuzla::Sort>{}(*Sort_val(vt));
}
static struct custom_operations sort_operations =
  {
    "https://bitwuzla.github.io",
    &sort_delete,
    &native_bitwuzla_sort_compare,
    &native_bitwuzla_sort_hash,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
  };



extern "C" CAMLprim uint64_t
native_bitwuzla_sort_id (mlvalue vt)
{
  return Sort_val(vt)->id();
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_id (mlvalue vt)
{
  return caml_copy_int64(native_bitwuzla_sort_id(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_compare (mlvalue v1, mlvalue v2)
{
  return Val_long(native_bitwuzla_sort_compare(v1, v2));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_equal (mlvalue v1, mlvalue v2)
{
  return Val_int(*Sort_val(v1) == *Sort_val(v2));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_hash (mlvalue vt)
{
  return Val_long(native_bitwuzla_sort_hash(vt));
}

extern "C" CAMLprim intnat
native_bitwuzla_sort_bv_size (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Sort_val(vt)->bv_size();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_bv_size (mlvalue vt)
{
  return Val_long(native_bitwuzla_sort_bv_size(vt));
}

extern "C" CAMLprim intnat
native_bitwuzla_sort_fp_exp_size (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Sort_val(vt)->fp_exp_size();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_fp_exp_size (mlvalue vt)
{
  return Val_long(native_bitwuzla_sort_fp_exp_size(vt));
}

extern "C" CAMLprim intnat
native_bitwuzla_sort_fp_sig_size (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Sort_val(vt)->fp_sig_size();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_fp_sig_size (mlvalue vt)
{
  return Val_long(native_bitwuzla_sort_fp_sig_size(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_array_index (mlvalue vt)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(Sort_val(vt)->array_index());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_array_element (mlvalue vt)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(Sort_val(vt)->array_element());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_fun_domain (mlvalue vt)
{
  std::vector<bitwuzla::Sort> domain;
  BITWUZLA_TRY_CATCH_BEGIN;
  domain = Sort_val(vt)->fun_domain();
  BITWUZLA_TRY_CATCH_END;
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = domain.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&sort_operations, &custom) Sort(domain[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_fun_codomain (mlvalue vt)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(Sort_val(vt)->fun_codomain());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim intnat
native_bitwuzla_sort_fun_arity (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Sort_val(vt)->fun_arity();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_fun_arity (mlvalue vt)
{
  return Val_long(native_bitwuzla_sort_fun_arity(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_uninterpreted_symbol (mlvalue vt)
{
  std::optional<std::string> symbol;
  BITWUZLA_TRY_CATCH_BEGIN;
  symbol = Sort_val(vt)->uninterpreted_symbol();
  BITWUZLA_TRY_CATCH_END;
  if (symbol.has_value()) {
    return caml_copy_string(symbol->c_str());
  } else {
    caml_raise_not_found();
    __builtin_unreachable();
  }
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_array (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_array());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_bool (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_bool());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_bv (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_bv());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_fp (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_fp());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_fun (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_fun());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_rm (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_rm());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_is_uninterpreted (mlvalue vt)
{
  return Val_bool(Sort_val(vt)->is_uninterpreted());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_sort_to_string (mlvalue vt)
{
  return caml_copy_string(Sort_val(vt)->str().c_str());
}

extern "C" CAMLprim void
ocaml_bitwuzla_sort_pp (mlvalue vf, mlvalue vt)
{
  CAMLparam1(vf);
  Format format(&vf);
  std::ostream formatter(&format);
  caml_callback2(*vpp_open_vbox, vf, Val_int(0));
  formatter << *Sort_val(vt);
  caml_callback2(*vpp_close_box, vf, Val_unit);
  CAMLreturn0;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_array_sort (mlvalue vi, mlvalue ve)
{
  CAMLparam2(vi, ve);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_array_sort(*Sort_val(vi),
							      *Sort_val(ve)));
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
  CAMLreturn(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bool_sort ()
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_bool_sort());
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
  return custom;
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_bv_sort (intnat size)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_bv_sort(size));
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
  return custom;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_sort (mlvalue vsize)
{
  return native_bitwuzla_mk_bv_sort(Long_val(vsize));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_fp_sort (intnat exp_size, intnat sig_size)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_fp_sort(exp_size, sig_size));
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
  return custom;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_sort (mlvalue vexp_size, mlvalue vsig_size)
{
  return native_bitwuzla_mk_fp_sort(Long_val(vexp_size), Long_val(vsig_size));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fun_sort (mlvalue vdomain, mlvalue vcodomain)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  CAMLparam1(vcodomain);
  size_t arity = Wosize_val(vdomain);
  std::vector<bitwuzla::Sort> domain;
  domain.reserve(arity);
  for (size_t i = 0; i < arity; i += 1)
    domain.emplace_back(*Sort_val(Field(vdomain, i)));
  new(&sort_operations, &custom)
    Sort(bitwuzla::mk_fun_sort(domain, *Sort_val(vcodomain)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_rm_sort ()
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_rm_sort());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_uninterpreted_sort (mlvalue vopt)
{
  CAMLparam1(vopt);
  mlvalue custom = Val_unit;
  std::optional<const std::string> symbol;
  if (Is_some(vopt))
    symbol.emplace(std::string(String_val(Field(vopt, 0))));
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(bitwuzla::mk_uninterpreted_sort(symbol));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

#define value mlvalue
class Term : public bitwuzla::Term
{
public:
  Term(bitwuzla::Term t) : bitwuzla::Term(t) {}
  ~Term() {}
  void * operator new (size_t size,
		       struct custom_operations * operations,
		       mlvalue *custom)
  {
    *custom = caml_alloc_custom(operations, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete (void *ptr) {}
};
#undef value

#define Term_val(v) ((Term*)Data_custom_val(v))

static void term_delete (mlvalue vt)
{
  delete Term_val(vt);
}
extern "C" CAMLprim int native_bitwuzla_term_compare (mlvalue v1, mlvalue v2)
{
  uint64_t i1 = Term_val(v1)->id(), i2 = Term_val(v2)->id();
  return (i1 >= i2) - (i1 <= i2);
}
extern "C" CAMLprim intnat native_bitwuzla_term_hash (mlvalue vt)
{
  return std::hash<bitwuzla::Term>{}(*Term_val(vt));
}
static struct custom_operations term_operations =
  {
    "https://bitwuzla.github.io",
    &term_delete,
    &native_bitwuzla_term_compare,
    &native_bitwuzla_term_hash,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
  };



extern "C" CAMLprim uint64_t
native_bitwuzla_term_id (mlvalue vt)
{
  return Term_val(vt)->id();
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_id (mlvalue vt)
{
  return caml_copy_int64(native_bitwuzla_term_id(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_compare (mlvalue v1, mlvalue v2)
{
  return Val_long(native_bitwuzla_term_compare(v1, v2));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_equal (mlvalue v1, mlvalue v2)
{
  return Val_int(*Term_val(v1) == *Term_val(v2));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_hash (mlvalue vt)
{
  return Val_long(native_bitwuzla_term_hash(vt));
}

extern "C" CAMLprim intnat
native_bitwuzla_term_kind (mlvalue vt)
{
  return (intnat)Term_val(vt)->kind();
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_kind (mlvalue vt)
{
  return Val_long(native_bitwuzla_term_kind(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_sort (mlvalue vt)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(Term_val(vt)->sort());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim intnat
native_bitwuzla_term_num_children (mlvalue vt)
{
  return Term_val(vt)->num_children();
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_num_children (mlvalue vt)
{
  return Val_long(native_bitwuzla_term_num_children(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_children (mlvalue vt)
{
  std::vector<bitwuzla::Term> children = Term_val(vt)->children();
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = children.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&term_operations, &custom) Term(children[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_term_get (mlvalue vt, intnat i)
{
  CAMLparam1(vt);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term((*Term_val(vt))[i]);
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_get (mlvalue vt, mlvalue vi)
{
  return native_bitwuzla_term_get(vt, Long_val(vi));
}

extern "C" CAMLprim intnat
native_bitwuzla_term_num_indices (mlvalue vt)
{
  return Term_val(vt)->num_indices();
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_num_indices (mlvalue vt)
{
  return Val_long(native_bitwuzla_term_num_indices(vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_indices (mlvalue vt)
{
  std::vector<uint64_t> indices;
  BITWUZLA_TRY_CATCH_BEGIN;
  indices = Term_val(vt)->indices();
  BITWUZLA_TRY_CATCH_END;
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = indices.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    Field(result, i) = Val_long(indices[i]);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_symbol (mlvalue vt)
{
  std::optional<std::reference_wrapper<const std::string>> symbol =
    Term_val(vt)->symbol();
  if (symbol.has_value()) {
    return caml_copy_string(symbol->get().c_str());
  } else {
    caml_raise_not_found();
    __builtin_unreachable();
  }
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_const (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_const());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_variable (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_variable());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_value (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_value());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_bv_value_zero (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_bv_value_zero());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_bv_value_one (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_bv_value_one());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_bv_value_ones (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_bv_value_ones());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_bv_value_min_signed (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_bv_value_min_signed());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_bv_value_max_signed (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_bv_value_max_signed());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_fp_value_pos_zero (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_fp_value_pos_zero());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_fp_value_neg_zero (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_fp_value_neg_zero());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_fp_value_pos_inf (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_fp_value_pos_inf());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_fp_value_neg_inf (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_fp_value_neg_inf());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_fp_value_nan (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_fp_value_nan());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_rm_value_rna (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_rm_value_rna());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_rm_value_rne (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_rm_value_rne());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_rm_value_rtn (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_rm_value_rtn());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_rm_value_rtp (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_rm_value_rtp());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_is_rm_value_rtz (mlvalue vt)
{
  return Val_bool(Term_val(vt)->is_rm_value_rtz());
}

extern "C" CAMLprim mlvalue
native_bitwuzla_term_to_string (intnat base, mlvalue vt)
{
  return caml_copy_string(Term_val(vt)->str(base).c_str());
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_to_string (mlvalue vbase, mlvalue vt)
{
  return native_bitwuzla_term_to_string(Long_val(vbase), vt);
}

extern "C" CAMLprim void
ocaml_bitwuzla_term_pp (mlvalue vf, mlvalue vt)
{
  CAMLparam1(vf);
  Format format(&vf);
  std::ostream formatter(&format);
  caml_callback2(*vpp_open_vbox, vf, Val_int(0));
  formatter << *Term_val(vt);
  caml_callback2(*vpp_close_box, vf, Val_unit);
  CAMLreturn0;
}

extern "C" CAMLprim void
native_bitwuzla_term_pp_smt2 (intnat base, mlvalue vf, mlvalue vt)
{
  CAMLparam1(vf);
  Format format(&vf);
  std::ostream formatter(&format);
  caml_callback2(*vpp_open_vbox, vf, Val_int(0));
  formatter << bitwuzla::set_bv_format(base) << *Term_val(vt);
  caml_callback2(*vpp_close_box, vf, Val_unit);
  CAMLreturn0;
}

extern "C" CAMLprim void
ocaml_bitwuzla_term_pp_smt2 (mlvalue vbase, mlvalue vf, mlvalue vt)
{
  native_bitwuzla_term_pp_smt2(Long_val(vbase), vf, vt);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_boolean_value (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Val_bool(Term_val(vt)->value<bool>());
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim intnat
native_bitwuzla_term_rounding_mode_value (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return (intnat)Term_val(vt)->value<bitwuzla::RoundingMode>();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_rounding_mode_value (mlvalue vt)
{
  return Val_long(native_bitwuzla_term_rounding_mode_value(vt));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_term_string_value (mlvalue vt, intnat base)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return caml_copy_string(Term_val(vt)->value<std::string>(base).c_str());
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_string_value (mlvalue vt, mlvalue vbase)
{
  return native_bitwuzla_term_string_value(vt, Long_val(vbase));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_ieee_754_value (mlvalue vt)
{
  std::tuple<std::string, std::string, std::string> tuple;
  BITWUZLA_TRY_CATCH_BEGIN;
  tuple =
    Term_val(vt)->value<std::tuple<std::string, std::string, std::string>>();
  BITWUZLA_TRY_CATCH_END;
  CAMLparam0();
  CAMLlocal1(result);
  result = caml_alloc(3, 0);
  caml_modify(&Field(result, 0), caml_copy_string(std::get<0>(tuple).c_str()));
  caml_modify(&Field(result, 1), caml_copy_string(std::get<1>(tuple).c_str()));
  caml_modify(&Field(result, 2), caml_copy_string(std::get<2>(tuple).c_str()));
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_term_zarith_value (mlvalue vt)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Term_val(vt)->value<value>();
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_true ()
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(bitwuzla::mk_true());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_false ()
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(bitwuzla::mk_false());
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_zero (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(bitwuzla::mk_bv_zero(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_one (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(bitwuzla::mk_bv_one(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_ones (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(bitwuzla::mk_bv_ones(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_min_signed (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_bv_min_signed(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_max_signed (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_bv_max_signed(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_bv_value (mlvalue vs, mlvalue vv, intnat base)
{
  CAMLparam1(vs);
  const std::string val = String_val(vv);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_bv_value(*Sort_val(vs), val, base));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_value (mlvalue vs, mlvalue vv, intnat base)
{
  return native_bitwuzla_mk_bv_value(vs, vv, Long_val(base));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_bv_value_int64 (mlvalue vs, intnat val)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_bv_value_int64(*Sort_val(vs), val));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_value_int (mlvalue vs, mlvalue vv)
{
  return native_bitwuzla_mk_bv_value_int64(vs, Long_val(vv));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_bv_value_int64 (mlvalue vs, mlvalue vv)
{
  return native_bitwuzla_mk_bv_value_int64(vs, Int64_val(vv));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_pos_zero (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_pos_zero(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_neg_zero (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_neg_zero(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_pos_inf (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_pos_inf(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_neg_inf (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_neg_inf(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_nan (mlvalue vs)
{
  CAMLparam1(vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_nan(*Sort_val(vs)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_value (mlvalue v1, mlvalue v2, mlvalue v3)
{
  CAMLparam3(v1, v2, v3);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_value(*Term_val(v1), *Term_val(v2), *Term_val(v3)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_value_from_real (mlvalue vs, mlvalue vrm, mlvalue vv)
{
  CAMLparam2(vs, vrm);
  const std::string val(String_val(vv));
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_value(*Sort_val(vs), *Term_val(vrm), val));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_fp_value_from_rational (mlvalue vs, mlvalue vrm,
					  mlvalue vnum, mlvalue vden)
{
  CAMLparam2(vs, vrm);
  const std::string num(String_val(vnum));
  const std::string den(String_val(vden));
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_fp_value(*Sort_val(vs), *Term_val(vrm), num, den));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_const_array (mlvalue vs, mlvalue vv)
{
  CAMLparam2(vs, vv);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_const_array(*Sort_val(vs), *Term_val(vv)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_rm_value (intnat rm)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_rm_value((bitwuzla::RoundingMode)rm));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_rm_value (mlvalue vrm)
{
  return native_bitwuzla_mk_rm_value(Long_val(vrm));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term1 (intnat k, mlvalue v1)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1) };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term1 (intnat vk, mlvalue v1)
{
  return native_bitwuzla_mk_term1(Long_val(vk), v1);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term2 (intnat k, mlvalue v1, mlvalue v2)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1), *Term_val(v2) };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term2 (intnat vk, mlvalue v1, mlvalue v2)
{
  return native_bitwuzla_mk_term2(Long_val(vk), v1, v2);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term3 (intnat k, mlvalue v1, mlvalue v2, mlvalue v3)
{
  const std::vector<bitwuzla::Term>
    args{ *Term_val(v1), *Term_val(v2), *Term_val(v3) };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term3 (intnat vk, mlvalue v1, mlvalue v2, mlvalue v3)
{
  return native_bitwuzla_mk_term3(Long_val(vk), v1, v2, v3);
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term1_indexed1 (intnat k, mlvalue v1, intnat i)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1) };
  const std::vector<uint64_t> indices{ (uint64_t)i };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args, indices));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term1_indexed1 (intnat vk, mlvalue v1, mlvalue vi)
{
  return native_bitwuzla_mk_term1_indexed1(Long_val(vk), v1, Long_val(vi));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term1_indexed2 (intnat k, mlvalue v1, intnat i, intnat j)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1) };
  const std::vector<uint64_t> indices{ (uint64_t)i, (uint64_t)j };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args, indices));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term1_indexed2 (intnat vk, mlvalue v1, mlvalue vi, mlvalue vj)
{
  return native_bitwuzla_mk_term1_indexed2(Long_val(vk), v1,
					   Long_val(vi), Long_val(vj));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term2_indexed1 (intnat k, mlvalue v1, mlvalue v2, intnat i)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1), *Term_val(v2) };
  const std::vector<uint64_t> indices{ (uint64_t)i };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args, indices));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term2_indexed1 (intnat vk, mlvalue v1, mlvalue v2, mlvalue vi)
{
  return native_bitwuzla_mk_term2_indexed1(Long_val(vk), v1, v2, Long_val(vi));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term2_indexed2 (intnat k, mlvalue v1, mlvalue v2,
				   intnat i, intnat j)
{
  const std::vector<bitwuzla::Term> args{ *Term_val(v1), *Term_val(v2) };
  const std::vector<uint64_t> indices{ (uint64_t)i, (uint64_t)j };
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args, indices));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term2_indexed2 (intnat vk, mlvalue v1, mlvalue v2,
				  mlvalue vi, mlvalue vj)
{
  return native_bitwuzla_mk_term2_indexed2(Long_val(vk), v1, v2,
					   Long_val(vi), Long_val(vj));
}

extern "C" CAMLprim mlvalue
native_bitwuzla_mk_term (intnat k, mlvalue vargs, mlvalue vindices)
{
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> indices;
  size_t arity = Wosize_val(vargs);
  args.reserve(arity);
  for (size_t i = 0; i < arity; i += 1)
    args.emplace_back(*Term_val(Field(vargs, i)));
  arity = Wosize_val(vindices);
  indices.reserve(arity);
  for (size_t i = 0; i < arity; i += 1)
    indices.emplace_back((uint64_t)Long_val(Field(vindices, i)));
  new(&term_operations, &custom)
    Term(bitwuzla::mk_term((bitwuzla::Kind)k, args, indices));
  return custom;
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_term (intnat vk, mlvalue vargs, mlvalue vindices)
{
  return native_bitwuzla_mk_term(Long_val(vk), vargs, vindices);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_const (mlvalue vopt, mlvalue vs)
{
  CAMLparam2(vopt, vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  std::optional<const std::string> symbol;
  if (Is_some(vopt))
    symbol.emplace(std::string(String_val(Field(vopt, 0))));
  new(&term_operations, &custom)
    Term(bitwuzla::mk_const(*Sort_val(vs), symbol));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_mk_var (mlvalue vopt, mlvalue vs)
{
  CAMLparam2(vopt, vs);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  std::optional<const std::string> symbol;
  if (Is_some(vopt))
    symbol.emplace(std::string(String_val(Field(vopt, 0))));
  new(&term_operations, &custom)
    Term(bitwuzla::mk_var(*Sort_val(vs), symbol));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_substitute_term (mlvalue vt, mlvalue vmap)
{
  CAMLparam1(vt);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  size_t n = Wosize_val(vmap);
  map.reserve(n);
  for (size_t i = 0; i < n; i += 1) {
    map.emplace(std::make_pair(*Term_val(Field(Field(vmap, i), 0)),
			       *Term_val(Field(Field(vmap, i), 1))));
  }
  new(&term_operations, &custom)
    Term(bitwuzla::substitute_term(*Term_val(vt), map));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim void
ocaml_bitwuzla_substitute_terms (mlvalue va, mlvalue vmap)
{
  CAMLparam1(va);
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  std::vector<bitwuzla::Term> terms;
  size_t n = Wosize_val(vmap);
  map.reserve(n);
  for (size_t i = 0; i < n; i += 1) {
    map.emplace(std::make_pair(*Term_val(Field(Field(vmap, i), 0)),
			       *Term_val(Field(Field(vmap, i), 1))));
  }
  n = Wosize_val(va);
  terms.reserve(n);
  for (size_t i = 0; i < n; i += 1) {
    terms.emplace_back(*Term_val(Field(va, i)));
  }
  bitwuzla::substitute_terms(terms, map);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&term_operations, &custom) Term(terms[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(va, i), custom);
  }
  CAMLreturn0;
}

class Terminator : public bitwuzla::Terminator
{
  volatile mlvalue vtermination_callback;
public:
  Terminator() : vtermination_callback(Val_unit)
  {
    caml_register_global_root((mlvalue*)&vtermination_callback);
  }
  ~Terminator()
  {
    caml_remove_global_root((mlvalue*)&vtermination_callback);
  }
  bool terminate() override
  {
    return vtermination_callback != Val_unit
      && Bool_val(caml_callback((mlvalue)vtermination_callback, Val_unit));
  }
  void set(mlvalue vtc)
  {
    vtermination_callback = vtc;
  }
};

struct t { bitwuzla::Bitwuzla *bitwuzla; Terminator *terminator; };

#define Bitwuzla_val(v) (((struct t*)Data_custom_val(v))->bitwuzla)
#define Terminator_val(v) \
   (((struct t*)Data_custom_val(v))->terminator)

extern "C" CAMLprim void
ocaml_bitwuzla_delete (value vt)
{
  bitwuzla::Bitwuzla *t = Bitwuzla_val(vt);
  Terminator *terminator = Terminator_val(vt);
  Bitwuzla_val(vt) = nullptr;
  Terminator_val(vt) = nullptr;
  if (t != nullptr) {
    delete t;
    delete terminator;
  }
}

static struct custom_operations bitwuzla_operations =
  {
   "https://bitwuzla.github.io",
   ocaml_bitwuzla_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
  };

extern "C" CAMLprim value
ocaml_bitwuzla_new (mlvalue voptions)
{
  bitwuzla::Bitwuzla *t = new bitwuzla::Bitwuzla(*Options_val(voptions));
  Terminator *terminator = new Terminator();
  t->configure_terminator(terminator);
  value vt = caml_alloc_custom(&bitwuzla_operations, sizeof(struct t), 0, 1);
  Bitwuzla_val(vt) = t;
  Terminator_val(vt) = terminator;
  return vt;
}

extern "C" CAMLprim void
ocaml_bitwuzla_configure_terminator (mlvalue vt, mlvalue vtc)
{
  Terminator_val(vt)->set(Is_some(vtc) ? Some_val(vtc) : Val_unit);
}

extern "C" CAMLprim void
native_bitwuzla_push (mlvalue vt, intnat n)
{
  Bitwuzla_val(vt)->push(n);
}

extern "C" CAMLprim void
ocaml_bitwuzla_push (mlvalue vt, mlvalue vn)
{
  native_bitwuzla_push(vt, Long_val(vn));
}

extern "C" CAMLprim void
native_bitwuzla_pop (mlvalue vt, intnat n)
{
  Bitwuzla_val(vt)->pop(n);
}

extern "C" CAMLprim void
ocaml_bitwuzla_pop (mlvalue vt, mlvalue vn)
{
  native_bitwuzla_pop(vt, Long_val(vn));
}


extern "C" CAMLprim void
ocaml_bitwuzla_assert_formula (mlvalue vt, mlvalue va)
{
  Bitwuzla_val(vt)->assert_formula(*Term_val(va));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_get_assertions (mlvalue vt)
{
  std::vector<bitwuzla::Term> assertions = Bitwuzla_val(vt)->get_assertions();
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = assertions.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&term_operations, &custom) Term(assertions[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_is_unsat_assumption (mlvalue vt, mlvalue va)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return Val_bool(Bitwuzla_val(vt)->is_unsat_assumption(*Term_val(va)));
  BITWUZLA_TRY_CATCH_END;
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_get_unsat_assumptions (mlvalue vt)
{
  std::vector<bitwuzla::Term> assumptions;
  BITWUZLA_TRY_CATCH_BEGIN;
  assumptions = Bitwuzla_val(vt)->get_unsat_assumptions();
  BITWUZLA_TRY_CATCH_END;
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = assumptions.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&term_operations, &custom) Term(assumptions[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_get_unsat_core (mlvalue vt)
{
  std::vector<bitwuzla::Term> core;
  BITWUZLA_TRY_CATCH_BEGIN;
  core = Bitwuzla_val(vt)->get_unsat_core();
  BITWUZLA_TRY_CATCH_END;
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = core.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    mlvalue custom = Val_unit;
    BITWUZLA_TRY_CATCH_BEGIN;
    new(&term_operations, &custom) Term(core[i]);
    BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
}

extern "C" CAMLprim void
ocaml_bitwuzla_simplify (mlvalue vt)
{
  Bitwuzla_val(vt)->simplify();
}

extern "C" CAMLprim intnat
native_bitwuzla_check_sat (mlvalue va, mlvalue vt)
{
  std::vector<bitwuzla::Term> assumptions;
  size_t n = Wosize_val(va);
  assumptions.reserve(n);
  for (size_t i = 0; i < n; i += 1)
    assumptions.emplace_back(*Term_val(Field(va, i)));
  return (intnat)Bitwuzla_val(vt)->check_sat(assumptions);
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_check_sat (mlvalue va, mlvalue vt)
{
  return Val_long(native_bitwuzla_check_sat(va, vt));
}

extern "C" CAMLprim mlvalue
ocaml_bitwuzla_get_value (mlvalue vt, mlvalue va)
{
  CAMLparam1(va);
  mlvalue custom = Val_unit;
  BITWUZLA_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Bitwuzla_val(vt)->get_value(*Term_val(va)));
  CAMLreturn(custom);
  BITWUZLA_TRY_CATCH_END_CUSTOM_ALLOC(custom);
}

extern "C" CAMLprim void
ocaml_bitwuzla_pp_formula (mlvalue vf, mlvalue vt)
{
  CAMLparam1(vf);
  Format format(&vf);
  std::ostream formatter(&format);
  caml_callback2(*vpp_open_vbox, vf, Val_int(0));
  Bitwuzla_val(vt)->print_formula(formatter);
  caml_callback2(*vpp_close_box, vf, Val_unit);
  CAMLreturn0;
}

extern "C" CAMLprim void
ocaml_bitwuzla_pp_statistics (mlvalue vf, mlvalue vt)
{
  CAMLparam1(vf);
  Format format(&vf);
  std::ostream formatter(&format);
  caml_callback2(*vpp_open_vbox, vf, Val_int(0));
  auto stats = Bitwuzla_val(vt)->statistics();
  for (auto& [name, val] : stats)
    formatter << name << ": " << val << '\n';
  caml_callback2(*vpp_close_box, vf, Val_unit);
  CAMLreturn0;
}
