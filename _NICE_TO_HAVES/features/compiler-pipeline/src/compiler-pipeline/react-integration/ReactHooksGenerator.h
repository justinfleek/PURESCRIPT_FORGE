// React Hooks Generator Header
#ifndef REACT_HOOKS_GENERATOR_H
#define REACT_HOOKS_GENERATOR_H

#include "Cpp23Parser.h"
#include <string>

namespace react_hooks_generator {

// Generate React hooks from C++23 component
std::string generate_react_hooks(const CppStruct& component_def);

// Check component for hook needs
bool has_state_fields(const CppStruct& component_def);
bool has_effect_fields(const CppStruct& component_def);
bool has_ref_fields(const CppStruct& component_def);
bool has_callback_fields(const CppStruct& component_def);

// Generate specific hook types
std::string generate_use_state_hooks(const CppStruct& component_def);
std::string generate_use_effect_hooks(const CppStruct& component_def);
std::string generate_use_ref_hooks(const CppStruct& component_def);
std::string generate_use_callback_hooks(const CppStruct& component_def);
std::string generate_use_memo_hooks(const CppStruct& component_def);

// Helper functions
std::string extract_dependencies(const CppFunction& func);
std::string extract_callback_dependencies(const CppField& field);
std::string get_default_value(const CppType& type);
std::string capitalize(const std::string& str);

// Type conversion helper (from ReactGenerator)
std::string cpp_to_typescript(const CppType& type);

} // namespace react_hooks_generator

#endif // REACT_HOOKS_GENERATOR_H
