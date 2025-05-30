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

#include <iostream>
#include <sstream>
#include <climits>
#include <cstring>
#include <algorithm>
#include <bitwuzla/cpp/bitwuzla.h>

using namespace bitwuzla;

std::string lng_to_vn (std::string lng)
{
  std::string vn(lng);
  vn[0] = std::toupper(vn[0]);
  std::replace(vn.begin(), vn.end(), '-', '_');
  return vn;
}

extern "C" void build_enum_option ()
{
  Options options;
  std::stringstream key_type_stream, mode_types_stream;
  std::stringstream mode_to_string_stream, mode_of_string_stream;
  std::stringstream descr_stream, to_string_stream;
  std::stringstream to_cxx_stream;
  std::stringstream default_stream, min_stream, max_stream;
  std::stringstream set_stream, get_stream;
  key_type_stream << "type _ key =" << std::endl;
  descr_stream <<
    "let description : type a. a key -> string = function" << std::endl;
  to_string_stream <<
    "let to_string : type a. a key -> string = function" << std::endl;
  to_cxx_stream << "let to_cxx : type a. a key -> int = function" << std::endl;
  default_stream <<
    "let default_value : type a. a key -> a = function" << std::endl;
  min_stream << "let min : int key -> int = function" << std::endl;
  max_stream << "let max : int key -> int = function" << std::endl;
  set_stream <<
    "let set : type a. t -> a key -> a -> unit = fun t k v ->"  <<
    std::endl << "  match k with" << std::endl;
  get_stream <<
    "let get : type a. t -> a key -> a = fun t k ->"  <<
    std::endl << "  match k with" << std::endl;
  for (int i = 0; i < (int)Option::NUM_OPTS; i += 1) {
    Option opt = (Option) i;
    OptionInfo info(options, opt);
    std::string name = lng_to_vn(info.lng);
    std::string ln(name);
    ln[0] = std::tolower(ln[0]);
    key_type_stream << "  | " << name << " : ";
    descr_stream <<
      "  | " << name << " -> " << '"' << info.description << '"' << std::endl;
    to_string_stream <<
      "  | " << name << " -> " << '"' << info.lng << '"' << std::endl;
    to_cxx_stream << "  | " << name << " -> " << i << std::endl;
    default_stream << "  | " << name << " -> ";
    set_stream << "  | " << name << " -> ";
    get_stream << "  | " << name << " -> ";
    switch (info.kind) {
    case OptionInfo::Kind::BOOL:
      {
	key_type_stream << "bool";
	OptionInfo::Bool boolean = std::get<OptionInfo::Bool>(info.values);
	default_stream << (boolean.dflt ? "true" : "false") << std::endl;
	set_stream << "set_numeric t (to_cxx k) (Bool.to_int v)" << std::endl;
	get_stream << "get_numeric t (to_cxx k) <> 0" << std::endl;
      }
      break;
    case OptionInfo::Kind::NUMERIC:
      {
	key_type_stream << "int";
	OptionInfo::Numeric numeric =
	  std::get<OptionInfo::Numeric>(info.values);
	default_stream << numeric.dflt << std::endl;
        min_stream << "  | " << name << " -> " << numeric.min << std::endl;
	uint64_t max = numeric.max;
	if (max > (LONG_MAX / 2)) max = (LONG_MAX / 2);
        max_stream << "  | " << name << " -> " << max << std::endl;
	set_stream << "set_numeric t (to_cxx k) v" << std::endl;
	get_stream << "get_numeric t (to_cxx k)" << std::endl;
      }
      break;
    case OptionInfo::Kind::STRING:
      {
	key_type_stream << "string";
	OptionInfo::String str =
	  std::get<OptionInfo::String>(info.values);
	default_stream << '"' << str.dflt << '"' << std::endl;
        set_stream << "set_mode t (to_cxx k) v" << std::endl;
	get_stream << "get_string t (to_cxx k)" << std::endl;
      }
      break;
    case OptionInfo::Kind::MODE:
      {
	key_type_stream << ln;
	mode_types_stream << "and " << ln << " =" << std::endl;
	mode_to_string_stream <<
	  "let " << ln << "_to_string = function" << std::endl;
	mode_of_string_stream <<
	  "let " << ln << "_of_string = function" << std::endl;
        OptionInfo::Mode mode = std::get<OptionInfo::Mode>(info.values);
	std::string dflt = mode.dflt;
	dflt[0] = std::toupper(dflt[0]);
	default_stream << dflt << std::endl;
	std::vector<std::string> modes(mode.modes);
	std::sort(modes.begin(), modes.end());
	for (std::string m : modes) {
	  std::string v = lng_to_vn(m);
	  mode_types_stream << "  | " << v << std::endl;
	  mode_to_string_stream <<
	    "  | " << v << " -> " << '"' << m << '"' << std::endl;
	  mode_of_string_stream <<
	    "  | " << '"' << m << '"' << " -> " << v <<  std::endl;
	}
	mode_of_string_stream << "  | _ -> assert false" << std::endl;
	set_stream <<
	  "set_mode t (to_cxx k) (" << ln << "_to_string v)" << std::endl;
	get_stream <<
	  ln << "_of_string (get_mode t (to_cxx k))" << std::endl;
      }
      break;
    }
    key_type_stream << " key" << std::endl;
  }
  std::cout << key_type_stream.str()
	    << mode_types_stream.str()
	    << descr_stream.str()
	    << to_string_stream.str()
	    << to_cxx_stream.str()
	    << mode_to_string_stream.str()
   	    << mode_of_string_stream.str()
	    << default_stream.str()
	    << min_stream.str()
	    << max_stream.str()
	    << "type t" << std::endl
	    << "external default : unit -> t = "
	    << '"' << "ocaml_bitwuzla_cxx_options_new" << '"' << std::endl
	    << "external set_numeric : t -> (int [@untagged])"
	    << "-> (int [@untagged]) -> unit = "
	    << '"' << "ocaml_bitwuzla_cxx_options_set_numeric" << '"' << ' '
	    << '"' << "native_bitwuzla_cxx_options_set_numeric" << '"'<< std::endl
	    << "external set_mode : t -> (int [@untagged]) -> string -> unit = "
	    << '"' << "ocaml_bitwuzla_cxx_options_set_mode" << '"' << ' '
	    << '"' << "native_bitwuzla_cxx_options_set_mode" << '"' << std::endl
	    << set_stream.str()
	    << "external get_numeric : t -> (int [@untagged])"
	    << "-> (int [@untagged]) = "
	    << '"' << "ocaml_bitwuzla_cxx_options_get_numeric" << '"' << ' '
	    << '"' << "native_bitwuzla_cxx_options_get_numeric" << '"' << std::endl
	    << "external get_mode : t -> (int [@untagged]) -> string = "
	    << '"' << "ocaml_bitwuzla_cxx_options_get_mode" << '"' << ' '
	    << '"' << "native_bitwuzla_cxx_options_get_mode" << '"' << std::endl
	    << "external get_string : t -> (int [@untagged]) -> string = "
	    << '"' << "ocaml_bitwuzla_cxx_options_get_str" << '"' << ' '
	    << '"' << "native_bitwuzla_cxx_options_get_str" << '"' << std::endl
	    << get_stream.str();
}
