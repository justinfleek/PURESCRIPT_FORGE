// State Management Header
#ifndef STATE_MANAGEMENT_H
#define STATE_MANAGEMENT_H

#include "Cpp23Parser.h"
#include <string>

namespace state_management {

// Generate Redux store
std::string generate_redux_store(const CppStruct& state_def);

// Generate Zustand store
std::string generate_zustand_store(const CppStruct& state_def);

// Generate React hooks for state management
std::string generate_state_hooks(const CppStruct& state_def, 
                                 const std::string& store_type);

// Helper functions
std::string get_default_value(const CppType& type);
std::string capitalize(const std::string& str);
std::string cpp_to_typescript(const CppType& type);

} // namespace state_management

#endif // STATE_MANAGEMENT_H
