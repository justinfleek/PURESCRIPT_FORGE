// Context API Support - Phase 4
#include "ContextAPI.h"
#include "Cpp23Parser.h"
#include <string>
#include <sstream>
#include <vector>

namespace context_api {

// Generate React Context
std::string generate_context(const CppStruct& context_def) {
    std::ostringstream oss;
    
    oss << "// React Context for " << context_def.name << "\n";
    oss << "import { createContext, useContext, ReactNode } from 'react';\n\n";
    
    // Generate context value type
    oss << "interface " << context_def.name << "ContextValue {\n";
    for (const auto& field : context_def.fields) {
        std::string ts_type = cpp_to_typescript(field.type);
        std::string optional = field.is_optional ? "?" : "";
        oss << "  " << field.name << optional << ": " << ts_type << ";\n";
    }
    oss << "}\n\n";
    
    // Generate context
    oss << "const " << context_def.name << "Context = createContext<" 
        << context_def.name << "ContextValue | null>(null);\n\n";
    
    // Generate provider component
    oss << "interface " << context_def.name << "ProviderProps {\n";
    oss << "  children: ReactNode;\n";
    for (const auto& field : context_def.fields) {
        std::string ts_type = cpp_to_typescript(field.type);
        oss << "  " << field.name << ": " << ts_type << ";\n";
    }
    oss << "}\n\n";
    
    oss << "export const " << context_def.name << "Provider: React.FC<" 
        << context_def.name << "ProviderProps> = ({ children";
    
    for (const auto& field : context_def.fields) {
        oss << ", " << field.name;
    }
    oss << " }) => {\n";
    
    oss << "  const value: " << context_def.name << "ContextValue = {\n";
    for (const auto& field : context_def.fields) {
        oss << "    " << field.name << ",\n";
    }
    oss << "  };\n\n";
    
    oss << "  return (\n";
    oss << "    <" << context_def.name << "Context.Provider value={value}>\n";
    oss << "      {children}\n";
    oss << "    </" << context_def.name << "Context.Provider>\n";
    oss << "  );\n";
    oss << "};\n\n";
    
    // Generate use hook
    oss << "export const use" << context_def.name << " = (): " 
        << context_def.name << "ContextValue => {\n";
    oss << "  const context = useContext(" << context_def.name << "Context);\n";
    oss << "  if (!context) {\n";
    oss << "    throw new Error('use" << context_def.name 
        << " must be used within " << context_def.name << "Provider');\n";
    oss << "  }\n";
    oss << "  return context;\n";
    oss << "};\n";
    
    return oss.str();
}

// Generate context with default values
std::string generate_context_with_defaults(const CppStruct& context_def) {
    std::ostringstream oss;
    
    oss << generate_context(context_def);
    
    // Add default values
    oss << "\n// Default context values\n";
    oss << "const default" << context_def.name << "Value: " 
        << context_def.name << "ContextValue = {\n";
    for (const auto& field : context_def.fields) {
        std::string default_val = get_default_value(field.type);
        oss << "  " << field.name << ": " << default_val << ",\n";
    }
    oss << "};\n\n";
    
    // Update context creation
    oss << "// Updated context with defaults\n";
    oss << "const " << context_def.name << "Context = createContext<" 
        << context_def.name << "ContextValue>(default" 
        << context_def.name << "Value);\n";
    
    return oss.str();
}

// Helper functions
std::string get_default_value(const CppType& type) {
    if (type.name == "int" || type.name == "std::int32_t") {
        return "0";
    } else if (type.name == "double" || type.name == "float") {
        return "0.0";
    } else if (type.name == "bool") {
        return "false";
    } else if (type.name == "std::string" || type.name == "string") {
        return "\"\"";
    } else if (type.name.find("vector") != std::string::npos) {
        return "[]";
    } else if (type.name.find("optional") != std::string::npos) {
        return "null";
    }
    return "null";
}

std::string cpp_to_typescript(const CppType& type) {
    if (type.name == "int" || type.name == "std::int32_t") {
        return "number";
    } else if (type.name == "double" || type.name == "float") {
        return "number";
    } else if (type.name == "bool") {
        return "boolean";
    } else if (type.name == "std::string" || type.name == "string") {
        return "string";
    } else if (type.name.find("vector") != std::string::npos) {
        return "Array<unknown>";
    } else if (type.name.find("optional") != std::string::npos) {
        return "unknown | null";
    }
    return "unknown";
}

} // namespace context_api
