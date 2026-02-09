// Suspense and Error Boundaries Header
#ifndef SUSPENSE_ERROR_BOUNDARIES_H
#define SUSPENSE_ERROR_BOUNDARIES_H

#include "Cpp23Parser.h"
#include <string>

namespace suspense_error_boundaries {

// Generate Error Boundary component
std::string generate_error_boundary(const CppStruct& component_def);

// Generate Suspense wrapper
std::string generate_suspense_wrapper(const CppStruct& component_def);

// Generate async component with Suspense
std::string generate_async_component(const CppFunction& async_func);

// Helper functions
std::string cpp_to_typescript(const CppType& type);

} // namespace suspense_error_boundaries

#endif // SUSPENSE_ERROR_BOUNDARIES_H
