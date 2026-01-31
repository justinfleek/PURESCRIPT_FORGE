// Server Components Header
#ifndef SERVER_COMPONENTS_H
#define SERVER_COMPONENTS_H

#include "Cpp23Parser.h"
#include <string>

namespace server_components {

// Generate Server Component
std::string generate_server_component(const CppStruct& component_def);

// Generate Server Component with streaming
std::string generate_streaming_server_component(const CppStruct& component_def);

// Generate Server Action
std::string generate_server_action(const CppFunction& func);

// Generate form action
std::string generate_form_action(const CppFunction& func);

// Helper functions
std::string cpp_to_typescript(const CppType& type);

} // namespace server_components

#endif // SERVER_COMPONENTS_H
