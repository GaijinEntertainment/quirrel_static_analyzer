#pragma once

#include "compilation_context.h"


namespace moduleexports
{
  extern std::string csq_exe;

  bool module_export_collector(CompilationContext & ctx, int line, int col, const char * module_name = nullptr); // nullptr for roottable
  bool is_identifier_present_in_root(const char * name);
}
