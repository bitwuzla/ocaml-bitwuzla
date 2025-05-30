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
#include <cstring>
#include <bitwuzla/cpp/bitwuzla.h>
#define BITWUZLA_API_USE_C_ENUMS
#include <bitwuzla/enums.h>

using namespace bitwuzla;


extern "C" void build_enum_rounding_mode ()
{
  std::stringstream type_stream, to_string_stream;
  std::stringstream to_cxx_stream, of_cxx_stream;
  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cxx_stream << "let to_cxx = function" << std::endl;
  of_cxx_stream << "let of_cxx = function" << std::endl;
  for (int i = 0; i < BITWUZLA_RM_MAX; i += 1) {
    RoundingMode rm = (RoundingMode)i;
    std::string ln(std::to_string(rm));
    std::string name(ln);
    for (std::string::size_type j = 1; j < name.length(); j += 1)
      name[j] = std::tolower(name[j]);
    type_stream << "  | " << name << std::endl;
    to_string_stream <<
      "  | " << name << " -> " << '"' << ln << '"' << std::endl;
    to_cxx_stream <<
      "  | " << name << " -> " << i << std::endl;
    of_cxx_stream << "  | " << i << " -> " << name << std::endl;

  }
  of_cxx_stream << "  | _ -> assert false" << std::endl;
  std::cout << type_stream.str()
	    << to_string_stream.str()
	    << to_cxx_stream.str()
	    << of_cxx_stream.str();
}
