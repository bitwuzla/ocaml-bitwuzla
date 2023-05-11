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

using namespace bitwuzla;


extern "C" void build_enum_result ()
{
  std::vector<Result> results{ Result::SAT, Result::UNSAT, Result::UNKNOWN };
  std::stringstream type_stream, to_string_stream, of_cxx_stream;
  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  of_cxx_stream << "let of_cxx = function" << std::endl;
  for (Result r : results) {
    std::string ln(std::to_string(r));
    std::string name(ln);
    name[0] = std::toupper(name[0]);
    type_stream << "  | " << name << std::endl;
    to_string_stream <<
      "  | " << name << " -> " << '"' << ln << '"' << std::endl;
    of_cxx_stream << "  | " << (int)r << " -> " << name << std::endl;
  }
  of_cxx_stream << "  | _ -> assert false" << std::endl;
  std::cout << type_stream.str()
	    << to_string_stream.str()
	    << of_cxx_stream.str();
}
