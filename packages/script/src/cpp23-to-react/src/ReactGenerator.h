// React Generator Header (Complete)
#ifndef REACT_GENERATOR_H
#define REACT_GENERATOR_H

#include <string>
#include <vector>
#include <map>

// Forward declarations
struct CppStruct;
struct CppField;
struct CppType;
struct CppFunction;

namespace react_generator {

// Generate React component from C++ struct
std::string generate_react_component(const CppStruct& component_def);

// Generate TypeScript interface from C++ struct
std::string generate_typescript_interface(const CppStruct& struct_def);

// Convert C++ type to TypeScript type
std::string cpp_to_typescript(const CppType& type);
std::string cpp_to_typescript_base(const CppType& type);

// Generate React code for all components
void generate_react_code(const std::vector<CppStruct>& components,
                        const std::string& output_dir);

// Generate React hook from C++ function
std::string generate_react_hook(const CppFunction& func);

// Generate React context provider
std::string generate_context_provider(const std::string& context_name,
                                     const CppType& value_type);

// Generate custom React hook
std::string generate_custom_hook(const std::string& hook_name,
                                const std::vector<CppFunction>& functions);

} // namespace react_generator

#endif // REACT_GENERATOR_H
