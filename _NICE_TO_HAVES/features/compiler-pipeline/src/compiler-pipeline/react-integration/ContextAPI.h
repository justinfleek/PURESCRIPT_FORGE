// Context API Header
#ifndef CONTEXT_API_H
#define CONTEXT_API_H

#include "Cpp23Parser.h"
#include <string>

namespace context_api {

// Generate React Context
std::string generate_context(const CppStruct& context_def);

// Generate context with default values
std::string generate_context_with_defaults(const CppStruct& context_def);

// Helper functions
std::string get_default_value(const CppType& type);
std::string cpp_to_typescript(const CppType& type);

} // namespace context_api

#endif // CONTEXT_API_H
